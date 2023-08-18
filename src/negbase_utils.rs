
use std::vec;

use ff::{Field, PrimeField};
use num_bigint::{BigInt, RandomBits};
use num_bigint::Sign as Sign;
use num_traits::{Num, pow, One, Zero};
use rand::{Rng, random};


pub fn range_check(x: &BigInt) -> () {
    let threshold = pow(BigInt::from_bytes_le(Sign::Plus, &[2]), 127);
    assert!(x < &threshold);
    assert!(x > &-threshold);
}




pub fn negbase_decompose(x: &BigInt, base: u8) -> Vec<u8>{
    let mut x = x.clone();
    let mut acc = vec![];
    while (x != BigInt::zero()){
        let mut digit = x.clone()%base;
        match digit.sign() {                   // NICE % OPERATOR YOU HAVE THERE BIGINT LIBRARY!!!!!!
            Sign::Minus => digit+=base,
            _ => ()
        }
        let mut tmp = digit.clone().to_u64_digits().1;
        tmp.push(0);
        acc.push(tmp[0] as u8);
        x = -((x-digit)/base);
    }
    
    acc
}


pub enum Entry{
    Scalar(BigInt),
    Bucket(i128),
    Limb(i128, u32),
}

/// used for indexing of digits, will return None if digit is 0
pub fn id_by_digit(digit : u8) -> Option<usize> {
    if digit==0 {
        return None;
    }
    Some((digit-1) as usize)
}


pub fn digit_by_id(id : usize) -> u8 {
    (id+1).try_into().unwrap()
}

pub fn table_entry_by_id<F: PrimeField>(base: u8, id: usize) -> F {
    if id == 0 {return F::ZERO}
    
    let b = -F::from(base as u64);
    let mut acc = F::ZERO;
    let mut id = id;
    let mut bits = vec![];
    while id>0 {
        bits.push(id&1);
        id>>=1;
    }

    let l = bits.len();
    for i in 0..l {
        if bits[l-i-1]==1 {acc+=F::ONE}
        acc *= b;
    }
    
    acc
}

pub fn prepare_scalar_witness(sc: &BigInt, base: u8, num_digits: usize, logtable: usize) -> Vec<Vec<(Entry)>>{
    let digits = negbase_decompose(sc, base);
    assert!(digits.len() <= num_digits);
    let num_limbs = (num_digits+logtable-1)/logtable;
    
    let mut ret = vec![];

    for i in 0..(base as usize) {
        ret.push(vec![]);
        for j in 0..num_limbs+1 {
            ret[i].push((0, 0))
            }
        }

    for i in 0..digits.len() {
        match id_by_digit(digits[i]) {
            None => (),
            Some(id) => {
                ret[id+1][0].0 += pow(-(base as i128), i);
                ret[id+1][i%logtable + 1].0 += pow(-(base as i128), i%logtable);
                ret[id+1][i%logtable + 1].1 += pow(2 as u32, i%logtable);
                ret[0][i%logtable+1].0 += pow(-(base as i128), i%logtable);
                ret[0][i%logtable + 1].1 += pow(2 as u32, i%logtable);
            }
        }
    }
    
    let mut ret_ = vec![];

    for i in 0..(base as usize) {
        ret_.push(vec![]);
        for j in 0..num_limbs+1 {
            ret_[i].push(
                if (i==0) && (j==0) {
                    Entry::Scalar(sc.clone())
                } else if (j==0) {
                    Entry::Bucket(ret[i][j].0)
                } else {
                    Entry::Limb(ret[i][j].0, ret[i][j].1)
                }
            )
        }
    }

    ret_
}

#[test]

fn negbase_test() -> (){
    let rnd : u32 = random();
    let rnd = BigInt::from_bytes_le(Sign::Plus, &rnd.to_le_bytes());
    let mut tmp = negbase_decompose(&rnd, 17);
    tmp.reverse();
    assert!(tmp.into_iter().fold(BigInt::zero(), |acc, x| acc*(-17)+x) == rnd);
}
