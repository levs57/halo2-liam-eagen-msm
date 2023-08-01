use ff::{PrimeField, Field, BatchInvert, BatchInverter};
use group::{Curve, prime::PrimeCurveAffine, Group};
use num_bigint::{BigUint, RandomBits, BigInt};
use num_traits::{Num, Pow, pow, One};
use halo2::{arithmetic::{self, parallelize, best_fft, FftGroup, eval_polynomial, kate_division, best_multiexp}, poly::{commitment::MSM, ipa::{msm::MSMIPA, commitment::ParamsIPA}}, plonk::{Phase, FirstPhase, SecondPhase, ThirdPhase}};
use halo2curves::{CurveAffine, bn256, grumpkin::{self, G1Affine}, Coordinates, CurveExt};
use halo2curves::bn256::Fr as F;
use halo2curves::grumpkin::Fr as Fq;
use rand_core::OsRng;
use subtle::CtOption;
use std::{ops::{Shl, Add, Mul, Shr}, cmp, iter::*, fmt::{Display, Formatter}, time::SystemTime, marker::PhantomData};
use rand::{Rng, random};
use crate::{argument_witness_calc::{self, order}, negbase_utils::{self, digit_by_id}};

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

impl <F: PrimeField + Ord, C: CurveExt<Base = F>> LiamsGateNarrow<F,C>{

    pub fn configure(meta: &mut ConstraintSystem<F>){
        let a = meta.advice_column_in(FirstPhase);
        let b = meta.advice_column_in(SecondPhase);
        let c = meta.advice_column_in(ThirdPhase);

        let s1 = meta.fixed_column(); // this is active if i%batch_size == 0
        let s2 = meta.fixed_column(); // this is active in rows corresponding to sc_buckets
        let s3 = meta.fixed_column(); // todo

        let s_table = meta.fixed_column();
        let s_arith = meta.fixed_column();
        
        let constants = meta.fixed_column();

        meta.enable_equality(c);

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

        meta.create_gate("scalar from buckets", |meta|{
            let sc = meta.query_advice(b, Rotation(0));
            let b_rots : Vec<Expression<F>> = (0..BASE-1).into_iter().map(
                    |i| meta.query_advice(b, Rotation(((i+1)*(NUM_LIMBS+1)) as i32))
                ).collect();
            // b[0] = b[NL+1] + 2*b[2*(NL+2)] + ... (B-1)*b[(NL+1)*(B-1)]
            let mut gate = -sc;
            for i in 0..BASE-1 {
                gate = gate + e!(b_rots[i])*(F::from(digit_by_id(i) as u64));
            }
            // we activate it using selector s1, which itself is activated at condition (i % BATCH_SIZE == 0)
            let s = meta.query_fixed(s1, Rotation(0));
            [s*gate]
        });

        meta.create_gate("limbs integrity check", |meta|{
            let integrity = meta.query_advice(b, Rotation(0));
            let b_rots : Vec<Expression<F>> = (0..BASE-1).into_iter().map(
                |i| meta.query_advice(b, Rotation(((i+1)*(NUM_LIMBS+1)) as i32))
            ).collect();            // b[0] = b[NL+1] + b[2*(NL+2)] + ... b[(NL+1)*(B-1)]
            let mut gate = -integrity;
            for i in 0..BASE-1 {
                gate = gate + e!(b_rots[i]);
            }
            // we activate it using negative rotations of s1
            let mut s = Expression::Constant(F::ZERO);
            
            for i in 0..NUM_LIMBS {
                s = s + meta.query_fixed(s1, Rotation(-(1+i as i32)));
            }

            [s*gate]
        });


        meta.create_gate("bucket from limbs", |meta|{
            let mut sc_bucket = meta.query_advice(b, Rotation(0));
            
            let b_rots : Vec<Expression<F>> = (0..NUM_LIMBS).into_iter().map(
                |i|meta.query_advice(b, Rotation((1+i) as i32))
            ).collect();
            // sc_bucket is decomposed into limbs
            // b[0] == b[1] + BASE^{LOGTABLESIZE} b[2] + ... BASE^{LOGTABLESIZE*(NUM_LIMBS-1)} b[NUM_LIMBS]
            let mut gate = -sc_bucket;
            for i in 0..NUM_LIMBS {
                gate = gate + e!(b_rots[i]) * F::from(BASE as u64).pow([(i*LOGTABLESIZE) as u64]);
            }
            let mut s = meta.query_fixed(s2, Rotation(0));

            [s*gate]
        });
    }

}

#[test]


fn const_assertions() {
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