use ff::{PrimeField, Field, BatchInvert, BatchInverter};
use group::{Curve, prime::PrimeCurveAffine, Group};
use num_bigint::{BigUint, RandomBits, BigInt};
use num_traits::{Num, Pow, pow, One};
use halo2::{arithmetic::{self, parallelize, best_fft, FftGroup, eval_polynomial, kate_division, best_multiexp}, poly::{commitment::MSM, ipa::{msm::MSMIPA, commitment::ParamsIPA}}, plonk::{Phase, FirstPhase, SecondPhase, ThirdPhase, Challenge, Circuit}, transcript::{self, ChallengeScalar}, circuit::{floor_planner::V1, Layouter}};
use halo2curves::{CurveAffine, bn256, grumpkin::{self, G1Affine}, Coordinates, CurveExt};
use halo2curves::bn256::Fr as F;
use halo2curves::grumpkin::Fr as Fq;
use rand_core::OsRng;
use subtle::CtOption;
use std::{ops::{Shl, Add, Mul, Shr}, cmp, iter::*, fmt::{Display, Formatter}, time::SystemTime, marker::PhantomData};
use rand::{Rng, random};
use crate::{argument_witness_calc::{self, order}, negbase_utils::{self, digit_by_id}, regular_functions_utils::{self, Polynomial, FftPrecomp}, config::LiamsGateNarrow};

use halo2::circuit::{AssignedCell, Cell, Region, Value};

use halo2::{
    plonk::{
        Advice, Column, ConstraintSystem, Constraints, Expression, Fixed, Selector, TableColumn,
    },
    poly::Rotation,
};

type Grumpkin = grumpkin::G1;

// struct LiamEagenCircuit<F: PrimeField + Ord + FftPrecomp, C: CurveExt<Base = F>> {
//     _marker: PhantomData<(F, C)>,
//     num_points : u32,
//     base : u8,
// }

// impl <F: PrimeField + Ord + FftPrecomp, C: CurveExt<Base = F>> Circuit<F> for LiamEagenCircuit<F, C> {
//     type Config = LiamsGateNarrow<F, C>;
//     type FloorPlanner = V1;

// }

// fn f() -> () {
//     Region;
// }