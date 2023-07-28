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
use halo2curves::serde::SerdeObject;
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
use std::fs::File;
use std::io::Write;
use std::time::SystemTime;
use std::{ops::{Shl, Add, Mul}, cmp, iter::*, fmt::{Display, Formatter}};
use rand::{Rng, random};


#[test]

// this could have been a procedural macro, I guess, but I'm bad
fn precompute_fft_aux_data() -> () {
    let mut s : String = "".to_string();
    s+="use halo2curves::{bn256::Fr as F, serde::SerdeObject};\n";
    s+="use crate::regular_functions_utils::FftPrecomp;\n";
    s+="impl FftPrecomp for F {\n";
    s+="    fn omega_pow(exp2: u32) -> F {\n";
    s+="        let tmp = match exp2 {\n";
    for i in 0..64 {
        s += &format!("            {i}=>{:?},\n", F::ROOT_OF_UNITY.pow([(2 as u64).pow(i as u32)]).to_raw_bytes());
    }
    s+="            _=>panic!(),\n";
    s+="        };\n";
    s+="    F::from_raw_bytes_unchecked(&tmp)\n";
    s+="    }\n\n";

    s+="    fn omega_pow_inv(exp2: u32) -> F {\n";
    s+="        let tmp = match exp2 {\n";
    for i in 0..64 {
        s += &format!("            {i}=>{:?},\n", F::ROOT_OF_UNITY_INV.pow([(2 as u64).pow(i as u32)]).to_raw_bytes());
    }
    s+="            _=>panic!(),\n";
    s+="        };\n";
    s+="    F::from_raw_bytes_unchecked(&tmp)\n";
    s+="    }\n\n";

    s+="    fn half_pow(exp: u64) -> F {\n";
    s+="        let tmp = match exp {\n";
    for i in 0..64 {
        s += &format!("            {i}=>{:?},\n", F::TWO_INV.pow([i as u64]).to_raw_bytes());
    }
    s+="            _=>panic!(),\n";
    s+="        };\n";
    s+="    F::from_raw_bytes_unchecked(&tmp)\n";
    s+="    }\n";
    s+="}\n";

    let mut f = File::create("./src/precomputed_fft_data.rs").expect("Unable to create file");
    f.write_all(s.as_bytes()).expect("Unable to write data");
}