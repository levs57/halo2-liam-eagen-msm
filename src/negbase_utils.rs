
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

/// Takes bigint as input, and computes the buckets
/// Each bucket only has digits 0 and 1 in negbase representations
pub fn buckets(x: &BigInt, base: u8) -> (){

}

#[test]

fn negbase_test() -> (){
    let rnd : u32 = random();
    let rnd = BigInt::from_bytes_le(Sign::Plus, &rnd.to_le_bytes());
    let mut tmp = negbase_decompose(&rnd, 17);
    tmp.reverse();
    assert!(tmp.into_iter().fold(BigInt::zero(), |acc, x| acc*(-17)+x) == rnd);
}
