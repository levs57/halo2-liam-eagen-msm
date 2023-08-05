use ff::{PrimeField, Field, BatchInvert, BatchInverter};
use group::{Curve, prime::PrimeCurveAffine, Group};
use num_bigint::{BigUint, RandomBits, BigInt};
use num_traits::{Num, Pow, pow, One};
use halo2::{arithmetic::{self, parallelize, best_fft, FftGroup, eval_polynomial, kate_division, best_multiexp}, poly::{commitment::MSM, ipa::{msm::MSMIPA, commitment::ParamsIPA}}, plonk::{Phase, FirstPhase, SecondPhase, ThirdPhase, Challenge}, transcript::{self, ChallengeScalar}};
use halo2curves::{CurveAffine, bn256, grumpkin::{self, G1Affine}, Coordinates, CurveExt};
use halo2curves::bn256::Fr as F;
use halo2curves::grumpkin::Fr as Fq;
use rand_core::OsRng;
use subtle::CtOption;
use std::{ops::{Shl, Add, Mul, Shr}, cmp, iter::*, fmt::{Display, Formatter}, time::SystemTime, marker::PhantomData};
use rand::{Rng, random};
use crate::{argument_witness_calc::{self, order}, negbase_utils::{self, digit_by_id}, regular_functions_utils::{self, Polynomial, FftPrecomp}};

use halo2::circuit::{AssignedCell, Cell, Region, Value};

use halo2::{
    plonk::{
        Advice, Column, ConstraintSystem, Constraints, Expression, Fixed, Selector, TableColumn,
    },
    poly::Rotation,
};

type Grumpkin = grumpkin::G1;

//taken from Onur's halo2msm repo, very convenient
macro_rules! e {
    // I just want not to see too much cloned expressions around :/ this is a bit less ugly
    ($a:expr) => {
        $a.clone()
    };
}

const NUM_LIMBS : usize = 4;
const BASE : usize = 5;
const SKIP : usize = 2;
const LOGTABLESIZE : usize = 15;
const POLY_ROTATION : usize = 13;
const BATCH_SIZE : usize = 26;

pub struct LiamsGateNarrow<F: PrimeField + Ord, C: CurveExt<Base = F>> {
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    // in my implementation, selectors are just fixed columns, because I sometimes reuse them for various weird stuff,
    // and combining is, thus, undesirable
    pub constants: Column<Fixed>,
    pub s1: Column<Fixed>,
    pub s2: Column<Fixed>,
    pub s3: Column<Fixed>,
    pub s_table: Column<Fixed>,
    pub s_arith: Column<Fixed>,
    pub _marker: PhantomData<(F, C)>,
}

/// this is a simple, non-constant time conversion from a challenge to an affine point of a curve
/// should rewrite it to constant time at some point
pub fn to_curve_x<F: PrimeField + FftPrecomp, C: CurveExt<Base = F>> (c: Vec<F>) -> F{
    assert!(c.len() == 1);
    let mut x = c[0];
    let eq = Polynomial::new(vec![C::b(), C::a(), F::ZERO, F::ONE]);
    loop {
        let (flag, _) = eq.ev(x).sqrt_alt();
        if flag.into() {break;}
    };
    x
}
/// recover y from x
pub fn y_from_x<F: PrimeField + FftPrecomp, C: CurveExt<Base = F>>(c: Vec<F>) -> F{
    assert!(c.len() == 1);
    let eq = Polynomial::new(vec![C::b(), C::a(), F::ZERO, F::ONE]);
    let (_, y) = eq.ev(c[0]).sqrt_alt();
    y
}
/// takes an affine point and returns slope of its tangent
pub fn slope<F: PrimeField + FftPrecomp, C: CurveExt<Base = F>>(c: Vec<F>) -> F{
    assert!(c.len()==2);
    (F::from(3)*c[0]*c[0] + C::a())*((F::from(2) * c[1]).invert().unwrap())
}

impl <F: PrimeField + Ord + FftPrecomp, C: CurveExt<Base = F>> LiamsGateNarrow<F,C>{

    pub fn configure(meta: &mut ConstraintSystem<F>){
        let a = meta.advice_column_in(FirstPhase);
        let b = meta.advice_column_in(SecondPhase);
        let c = meta.advice_column_in(ThirdPhase);

        let s1 = meta.fixed_column(); // this is active if i%batch_size == 0
//        let s2 = meta.fixed_column(); //deprecated, lets see if we can avoid using it completely 
        let s3 = meta.fixed_column(); // todo

        let table = meta.fixed_column(); // lookup table

        let s_table = meta.fixed_column();
        let s_arith = meta.fixed_column();
        
        let constants = meta.fixed_column();

        let v = meta.challenge_usable_after(SecondPhase); // lookup argument challenge
        let ch = meta.challenge_usable_after(FirstPhase); // Liam Eagen's argument challenge used to derive points
        let r = meta.challenge_usable_after(SecondPhase); // random coefficient for linear combination of polynomials


        meta.enable_equality(c);

        // generic gate allowing arithmetic operations in column c
        // it also allows to copy data from column b, and from constants table as a side-effect
        meta.create_gate("arithmetic gate", |meta|{
            let s = meta.query_fixed(s_arith, Rotation(-1));
            let const0 = meta.query_fixed(constants, Rotation(0));
            let const1 = meta.query_fixed(constants, Rotation(1));
            let b0 = meta.query_advice(b, Rotation(0)); 
            let cn0 = meta.query_advice(c, Rotation(0));
            let cn1 = meta.query_advice(c, Rotation(-1));
            let cn2 = meta.query_advice(c, Rotation(-2));
            let cn3 = meta.query_advice(c, Rotation(-3));
            // b * CONST + c[-3] * c[-2] + c[-1] * CONST[1] - c[0]
            //this allows to also reuse it to copy data from from column b
            let gate = e!(b0)*e!(const0) + e!(cn3)*e!(cn2) + e!(cn1)*e!(const1) - e!(cn0);
            [s*gate]
        });

        // this gate will be activate in a scalars region in column b
        // which is (N * BATCH_SIZE) first rows
        // it guarantees that each batch adheres to the structure described in layout.md
        // additionally, every limb + every integrity value must be checked with lookup
        meta.create_gate("b gate", |meta|{
            let b0 = meta.query_advice(b, Rotation(0));
            let b_primary_offsets : Vec<_> = (0..NUM_LIMBS).into_iter().map(
                |i|meta.query_advice(b, Rotation((1+i) as i32))
            ).collect();
            let b_secondary_offsets : Vec<_> = (0..BASE-1).into_iter().map(
                |i| meta.query_advice(b, Rotation(((i+1)*(NUM_LIMBS+1)) as i32))
            ).collect();
            let mut gate_sc_from_buckets = -e!(b0);
            for i in 0..BASE-1 {
                gate_sc_from_buckets = gate_sc_from_buckets + e!(b_secondary_offsets[i])*(F::from(digit_by_id(i) as u64));
            }
            let mut gate_limb_integrity_check = -e!(b0);
            for i in 0..BASE-1 {
                gate_limb_integrity_check = gate_limb_integrity_check + e!(b_secondary_offsets[i]);
            }
            let mut gate_bucket_from_limbs = -e!(b0);
            for i in 0..NUM_LIMBS {
                gate_bucket_from_limbs = gate_bucket_from_limbs + e!(b_primary_offsets[i]) * F::from(BASE as u64).pow([(i*LOGTABLESIZE) as u64]);
            }
            let s = meta.query_fixed(s1, Rotation(0));
            let mut s_prim = Expression::Constant(F::ZERO);
            for i in 0..NUM_LIMBS {
                s_prim = s_prim + meta.query_fixed(s1, Rotation(-(1+i as i32)));
            }
            let mut s_sec = Expression::Constant(F::ZERO);
            for i in 0..BASE-1 {
                s_sec = s_sec + meta.query_fixed(s1, Rotation(-(((1+i)*(NUM_LIMBS+1)) as i32)));
                // this was previously s2; currently expressed through s1; we can replace it to multiple selectors
            }
            [s*gate_sc_from_buckets + s_prim*gate_limb_integrity_check + s_sec*gate_bucket_from_limbs]
        });

        // this gate implements custom lookup argument
        // it spans first two regions in the column b - the N*BATCH_SIZE - sized first region, and additional
        // region of size ~ 2^LOGTABLESIZE * (BATCH_SIZE / (BATCH_SIZE - SKIP)) hosting the table
        // it implements a custom lookup argument, using a challenge v
        meta.create_gate("lookup", |meta|{
            let c0 = meta.query_advice(c, Rotation(0));
            let c1 = meta.query_advice(c, Rotation(1));
            let cn1 = meta.query_advice(c, Rotation(-1));
            let cnskip = meta.query_advice(c, Rotation(-(1 + SKIP as i32)));

            let b0 = meta.query_advice(b, Rotation(0));
            let b1 = meta.query_advice(b, Rotation(1));
            let v = meta.query_challenge(v);
            let t = meta.query_fixed(table, Rotation(0));

            // c[i+1] - c[i] = 1 / (v - b[i+1]) -- must be active on all cells corresponding to limbs / integrities from i = -1 
            let gate_lookup_rhs_1 = (e!(c1) - e!(c0))*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));
            // c[i+1] - c[i-1] = 1/(v-b[i+1]) -- must be active for i corresponding to buckets - to jump over them
            let gate_lookup_rhs_2 = (e!(c1) - e!(cn1))*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));
            // c[i+1] - c[i-SKIP-1] = 1/(v-b[i+1]) -- must be active for i corresponding to scalars - to jump over them and end of batch empty space
            let gate_lookup_rhs_3 = (e!(c1) - e!(cnskip))*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));

            // (c[1] - c[0] CONST - c[-(SKIP+1)](1 - CONST)) * (v-t) - b[1]
            let gate_lookup_lhs_1 = (e!(c0) - e!(cn1))*(e!(v)-e!(t)) + e!(b0);
            let gate_lookup_lhs_2 = (c0 - e!(cnskip))*(v-t) + b0;

            let sr1 = meta.query_fixed(s3, Rotation(0)); // this is activated by its own selector s3
            let mut sr2 = Expression::Constant(F::ZERO);
            for i in 0..BASE-1 {
                sr2 = sr2 + meta.query_fixed(s1, Rotation(-(((1+i)*(NUM_LIMBS+1)) as i32)));
                // this was previously s2; currently expressed through s1; we can replace it to multiple selectors
            }
            let sr3 = meta.query_fixed(s1, Rotation(0)); // active after the SKIP, i.e. on the first row after sc

            let s_table0 = meta.query_fixed(s_table, Rotation(0));
            let s_tablen1 = meta.query_fixed(s_table, Rotation(-1));
            let s_tableskip = meta.query_fixed(s_table, Rotation(SKIP as i32));

            let sl1 = e!(s_tablen1) + s_tableskip;
            let sl2 = s_table0 - s_tablen1;


            [sr1*gate_lookup_rhs_1 + sr2*gate_lookup_rhs_2 + sr3*gate_lookup_rhs_3
            + sl1*gate_lookup_lhs_1 + sl2*gate_lookup_lhs_2]
        });

        meta.create_gate("rhs main", |meta|{
            let c0 = meta.query_advice(c, Rotation(0));
            let b0 = meta.query_advice(b, Rotation(0));
            let cn_noskip = meta.query_advice(c, Rotation(-(1+NUM_LIMBS as i32)));
            let cn_skip = meta.query_advice(c, Rotation(-((2+SKIP+NUM_LIMBS) as i32)));
            
            let ptx = meta.query_fixed(constants, Rotation(0)); // these two slots contain coordinates of precomputed point
            let pty = meta.query_fixed(constants, Rotation(1));

            let ch = meta.query_challenge(ch);
            let ax = Expression::Postprocess(to_curve_x::<F,C>, Box::new(vec![ch]), Box::new("ax".to_string()));
            let ay = Expression::Postprocess(y_from_x::<F,C>, Box::new(vec![e!(ax)]), Box::new("bx".to_string()));
            let t = Expression::Postprocess(slope::<F,C>, Box::new(vec![e!(ax),e!(ay)]), Box::new("slope".to_string()));
            // b should be -2a
//            let bx = e!(t)*e!(t) - e!(ax)*Expression::Constant(F::from(2));
//            let by = e!(ay) - e!(t)*(e!(ax)-e!(bx));
            // y - tx + f - line function
            let f = e!(t)*e!(ax) - e!(ay);

            // c[0] - c[-1-NL] = b[0](Ax - pt.x)/(-z(pt)) = -b[0](Ax-pt.x)/(pt.y - t * pt.x + f)
            let gate_noskip = (e!(c0) - cn_noskip)*(e!(f) + e!(pty) - e!(t)*e!(ptx)) + e!(b0)*(e!(ax)-e!(ptx));
            let gate_skip = (e!(c0) - cn_skip)*(e!(f) + e!(pty) - e!(t)*e!(ptx)) + e!(b0)*(e!(ax)-e!(ptx));

            let mut s_sec = Expression::Constant(F::ZERO);
            for i in 0..BASE-1 {
                s_sec = s_sec + meta.query_fixed(s1, Rotation(-(((1+i)*(NUM_LIMBS+1)) as i32)));
                // this was previously s2; currently expressed through s1; we can replace it to multiple selectors
            }           
            let s_skip = meta.query_fixed(s1, Rotation(-1));
            [(s_sec-e!(s_skip))*gate_noskip + s_skip*gate_skip]

        });
    }

}

#[test]
fn const_assertions() {
    assert!(NUM_LIMBS > 1);
    assert!(pow(BigInt::from(BASE), LOGTABLESIZE*2*NUM_LIMBS) > order::<<Grumpkin as Group>::Scalar>());
    assert!(BATCH_SIZE == ((NUM_LIMBS+2)*(BASE-1)+SKIP));
    assert!(BATCH_SIZE % POLY_ROTATION == 0);
    let poly_rots_in_1_batch = BATCH_SIZE / POLY_ROTATION;
    assert!(poly_rots_in_1_batch >= SKIP);
}

#[test]

fn configure_test(){
    let mut cs : ConstraintSystem<F> = ConstraintSystem::default();
    LiamsGateNarrow::<F, Grumpkin>::configure(&mut cs);
}