use crate::negbase_utils::negbase_decompose;
use crate::negbase_utils::range_check;
use crate::negbase_utils::id_by_digit;
use crate::regular_functions_utils;
use crate::negbase_utils;
use crate::regular_functions_utils::FftPrecomp;
use crate::regular_functions_utils::RegularFunction;
use crate::regular_functions_utils::compute_divisor_witness;
use crate::regular_functions_utils::gen_random_pt;

use ff::FromUniformBytes;
use ff::{PrimeField, Field};
use group::{Curve, prime::PrimeCurveAffine};
use num_bigint::BigInt;
use num_bigint::Sign;
use num_bigint::ToBigInt;
use num_bigint::{BigUint, RandomBits};
use num_traits::Signed;
use num_traits::{Num, pow, One, Zero};
use halo2::{arithmetic::{self, parallelize, best_fft, FftGroup, eval_polynomial, kate_division, best_multiexp}, poly::{commitment::MSM, ipa::{msm::MSMIPA, commitment::ParamsIPA}}};
use halo2curves::{CurveAffine, bn256, grumpkin, Coordinates, CurveExt};
use halo2curves::bn256::Fr as F;
use halo2curves::grumpkin::Fr as Fq;
use rand_core::OsRng;
use subtle::CtOption;
use std::time::SystemTime;
use std::{ops::{Shl, Add, Mul}, cmp, iter::*, fmt::{Display, Formatter}};
use rand::{Rng, random};

type Grumpkin = grumpkin::G1;

fn logb_ceil(x: &BigUint, base: u8) -> u8{
    let mut x = x.clone();
    let mut i = 0;
    while (x > BigUint::zero()) {
        x /= base;
        i+=1;
    }
    i
}

/// Returns multiplicities of pt, from 1 to base 
fn precompute_multiplicities<C: CurveExt>(pt: &C, base: u8) -> Vec<C>{
    let mut acc : C = *pt;
    let mut ret = vec![];
    for _ in 0..base {
        ret.push(acc);
        acc = acc + *pt;
    }
    ret
}

/// Querying order of a prime field is a bit messy, it gives a string of unspecified format. Therefore:
pub fn order<Fz: PrimeField>() -> BigInt{
    BigInt::from_bytes_le(Sign::Plus, (-Fz::ONE).to_repr().as_ref()) + BigInt::one()
}

/// Idiotic way of converting value to a montgomery arithmetic. from_repr is angry at me and I don't understand why.
fn felt_from_u64<Fz: PrimeField>(d: u64) -> Fz {
    Fz::from(d) * Fz::from(1 as u64).invert().unwrap()
}


/// Generates coefficient < sqrt(p)
fn gen_random_coeff<Fz : PrimeField>() -> Fz {
    let x : u128 = random();
    let y : u128 = random();
    let o = order::<Fz>();
    let sq = o.sqrt();
    let x = BigInt::from(x);
    let y = BigInt::from(y);
    let s = (x+pow(BigInt::from(2), 128)*y) % sq;
    let s = s.to_u32_digits();
    let sh : Fz = felt_from_u64(pow(2,32));
    let mut q = s.1;
    q.reverse();
    q.into_iter().map(|x|felt_from_u64(x as u64)).fold(Fz::ZERO, |acc, x : Fz| acc*sh + x)

}

/// The core function. It takes a vector of scalars and a vector of points, and returns the witness to lhs of Liam Eagen's
/// argument, as described in a paper https://eprint.iacr.org/2022/596 , pages 8-9
/// Few differences: we use arbitrary negbase decomposition, and positive digit set, while Liam's argument uses
/// -3 negbase and symmetric set of digits (-1, 0, 1). Positive digit set gives an advantage with range checks later
/// while gains from symmetric digit set are likely negligible. Base > 3 are also needed for better lookups.
/// The scalars are assumed to be in range between 0 and ceil(sqrt(p)).
pub fn compute_lhs_witness<C: CurveExt>(scalars: &[C::Scalar], pts: &[C], base: u8)->(C, Vec<RegularFunction<C>>) where C::Base : FftPrecomp{
    assert!(scalars.len() == pts.len(), "incompatible amount of coefficients");
    let p = order::<C::Scalar>();
    let sq_p = (&p.sqrt()+BigInt::from_bytes_le(Sign::Plus, &[2])).to_biguint().unwrap();
    let d = logb_ceil(&sq_p, base) + 1; // amount of digits

    let scalars = scalars.iter().map(|x| BigUint::from_bytes_le(x.to_repr().as_ref()));


    // check that scalars are properly range checked from 0 to sqrt(p)
    let _ : Vec<_> = scalars.clone().map(|x| assert!(&x < &sq_p)).collect();

    let mut digits_by_scalar : Vec::<Vec<u8>> = scalars.clone().map(|x| negbase_decompose(&x.to_bigint().unwrap(), base).into_iter().chain(repeat(0 as u8)).take(d.into()).collect()).collect();
    
    (&mut digits_by_scalar).iter_mut().map(|x|x.reverse()).count();

    let precomputed_points : Vec<Vec<C>> = pts.into_iter().map(|pt| precompute_multiplicities(pt, base)).collect();

    let mut carry = C::identity();
    let mut ret = vec![];

    for i in 0..(d as usize){

        let mut tmp = Vec::<C>::new();

        if carry != C::identity(){        
            for _ in 0..base {
                tmp.push(-carry);
            }
        }

        carry = (-carry * felt_from_u64::<C::Scalar>(base as u64)).into();

        for j in 0..pts.len(){
            match id_by_digit(digits_by_scalar[j][i]) {
                None => (),
                Some(x) => {tmp.push(precomputed_points[j][x]); carry = (carry + precomputed_points[j][x]).into()}
            }
        }

        tmp.push(-carry);

        ret.push(compute_divisor_witness(tmp));
    }

    ret.reverse();

    (carry, ret)

}

#[test]

fn lhs_test(){
    let scalars : Vec<Fq> = repeat(gen_random_coeff()).take(10000).collect();
    let pts : Vec<Grumpkin> = repeat(gen_random_pt()).take(10000).collect();
    let pts_aff : Vec< grumpkin::G1Affine > = pts.iter().map(|x|x.into()).collect();
    let a = best_multiexp(&scalars, &pts_aff);
    let (b, _) = compute_lhs_witness(&scalars, &pts, 5);

    assert!(a==b.into());
}