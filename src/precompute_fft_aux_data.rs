use crate::negbase_utils::negbase_decompose;
use crate::negbase_utils::range_check;
use crate::negbase_utils::id_by_digit;
use crate::regular_functions_utils;
use crate::negbase_utils;
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


