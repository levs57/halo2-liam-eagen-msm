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
//        let s2 = meta.fixed_column(); //deprecated, lets see if we can avoid using it completely 
        let s3 = meta.fixed_column(); // todo

        let table = meta.fixed_column(); // lookup table

        let s_table = meta.fixed_column();
        let s_arith = meta.fixed_column();
        
        let constants = meta.fixed_column();

        let v = meta.challenge_usable_after(SecondPhase); // lookup argument challenge

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

        meta.create_gate("lookup", |meta|{
            let c0 = meta.query_advice(c, Rotation(0));
            let c1 = meta.query_advice(c, Rotation(1));
            let cn1 = meta.query_advice(c, Rotation(-1));
            let cnskip = meta.query_advice(c, Rotation(-(1 + SKIP as i32)));

            let b1 = meta.query_advice(b, Rotation(1));
            let v = meta.query_challenge(v);
            let t = meta.query_fixed(table, Rotation(0));


            // c[i+1] - c[i] = 1 / (v - b[i+1]) -- must be active on all cells corresponding to limbs / integrities from i = -1 
            let gate_rhs_1 = (e!(c1) - e!(c0))*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));
            // c[i+1] - c[i-1] = 1/(v-b[i+1]) -- must be active for i corresponding to buckets - to jump over them
            let gate_rhs_2 = (e!(c1) - cn1)*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));
            // c[i+1] - c[i-SKIP-1] = 1/(v-b[i+1]) -- must be active for i corresponding to scalars - to jump over them and end of batch empty space
            let gate_rhs_3 = (e!(c1) - e!(cnskip))*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));

            let consts = meta.query_fixed(constants, Rotation(0)); // this is reusing part of the constants table...

            // (c[1] - c[0] CONST - c[-(SKIP+1)](1 - CONST)) * (v-t) - b[1]
            let gate_lhs = (c1 - c0*e!(consts) - cnskip*(Expression::Constant(F::from(1)) - consts))*(v-t) - b1;

            let sel1 = meta.query_fixed(s3, Rotation(0)); // this is activated by its own selector s3
            let mut sel2 = Expression::Constant(F::ZERO);
            for i in 0..BASE-1 {
                sel2 = sel2 + meta.query_fixed(s1, Rotation(-(((1+i)*(NUM_LIMBS+1)) as i32)));
                // this was previously s2; currently expressed through s1; we can replace it to multiple selectors
            }
            let sel3 = meta.query_fixed(s1, Rotation(0)); // active after the SKIP, i.e. on the first row after sc

            let s = meta.query_fixed(s_table, Rotation(0));

            [sel1*gate_rhs_1 + sel2*gate_rhs_2 + sel3*gate_rhs_3 + s*gate_lhs]
        });

        // meta.create_gate("lookup lhs accumulator (jump 1)", |meta|{

        // });
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