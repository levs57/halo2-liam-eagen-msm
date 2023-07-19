use crate::negbase_utils::negbase_decompose;
use crate::negbase_utils::range_check;
use crate::regular_functions_utils;
use crate::negbase_utils;

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
use std::{ops::{Shl, Add, Mul}, cmp, iter::*, fmt::{Display, Formatter}};
use rand::{Rng, random};

type Grumpkin = grumpkin::G1Affine;

fn logb_ceil(x: &BigUint, base: u8) -> u8{
    let mut x = x.clone();
    let mut i = 0;
    while (x > BigUint::zero()) {
        x /= base;
        i+=1;
    }
    i
}

/// Querying order of a prime field is a bit messy, it gives a string of unspecified format. Therefore:
fn order<Fz: PrimeField>() -> BigInt{
    BigInt::from_bytes_le(Sign::Plus, (-Fz::ONE).to_repr().as_ref()) + BigInt::one()
}


/// The core function. It takes a vector of scalars and a vector of points, and returns the witness to Liam Eagen's argument,
/// as described in a paper https://eprint.iacr.org/2022/596 , pages 8-9
/// Few differences: we use arbitrary negbase decomposition, and positive digit set, while Liam's argument uses
/// -3 negbase and symmetric set of digits (-1, 0, 1). Positive digit set gives an advantage with range checks later
/// while gains from symmetric digit set are likely negligible. Base > 3 are also needed for better lookups.
/// The scalars are assumed to be in range between 0 and ceil(sqrt(p)).
pub fn compute_liams_witness<C: CurveAffine>(scalars: &[C::Scalar], pts: &[C], base: u8)->(){
    assert!(scalars.len() == pts.len(), "incompatible amount of coefficients");
    let p = order::<C::Scalar>();
    let sq_p = (&p.sqrt()+BigInt::from_bytes_le(Sign::Plus, &[2])).to_biguint().unwrap();
    let d = logb_ceil(&sq_p, base) + 1; // amount of digits

    let scalars = scalars.iter().map(|x| BigUint::from_bytes_le(x.to_repr().as_ref()));

    let precomputed_points = &pts.into_iter().map(|x|[1..d].into_iter().map(|x| C::Scalar::))

    // check that scalars are properly range checked from 0 to sqrt(p)
    let _ : Vec<_> = scalars.clone().map(|x| assert!(&x < &sq_p)).collect();

    let digits_by_scalar : Vec::<Vec<u8>> = scalars.map(|x| negbase_decompose(&x.to_bigint().unwrap(), base).into_iter().chain(repeat(0 as u8)).take(d.into()).collect()).collect();

    let mut points_by_digit : Vec::<Vec<C>> = Vec::new();



}