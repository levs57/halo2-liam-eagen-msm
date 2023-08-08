use ff::{PrimeField, Field, BatchInvert, BatchInverter};
use group::{Curve, prime::PrimeCurveAffine, Group};
use num_bigint::{BigUint, RandomBits, BigInt, Sign};
use num_traits::{Num, Pow, pow, One};
use halo2::{arithmetic::{self, parallelize, best_fft, FftGroup, eval_polynomial, kate_division, best_multiexp}, poly::{commitment::MSM, ipa::{msm::MSMIPA, commitment::ParamsIPA}}, plonk::{Phase, FirstPhase, SecondPhase, ThirdPhase, Challenge, Circuit, Error}, transcript::{self, ChallengeScalar}, circuit::{floor_planner::V1, Layouter}};
use halo2curves::{CurveAffine, bn256, grumpkin::{self, G1Affine}, Coordinates, CurveExt};
use halo2curves::bn256::Fr as F;
use halo2curves::grumpkin::Fr as Fq;
use rand_core::OsRng;
use subtle::CtOption;
use std::{ops::{Shl, Add, Mul, Shr}, cmp, iter::*, fmt::{Display, Formatter}, time::SystemTime, marker::PhantomData};
use rand::{Rng, random};
use crate::{argument_witness_calc::{self, order, logb_ceil}, negbase_utils::{self, digit_by_id}, regular_functions_utils::{self, Polynomial, FftPrecomp}};

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


fn div_ceil(a: usize, b: usize) -> usize {
    (a+b-1)/b
}

fn params_check<F: PrimeField + Ord + FftPrecomp, C: CurveExt <Base=F>> (params: &Params<F,C>) -> ParamsExt {
    let Params{num_pts, base, logtable, poly_fan_in, batch_offset, pts} = *params;
    assert!(pts.len() == num_pts, "incorrect amount of points");
    let num_digits = logb_ceil(&order::<F>().to_biguint().unwrap(), pow(base as u8,2)) as usize;
    let num_limbs = div_ceil(num_digits, logtable);
    let sc_box_size = (num_limbs+1)*base;
    let batch_size = batch_offset + num_digits;
    let c_skip = div_ceil(batch_size, poly_fan_in);
    let sc_in_batch = (batch_size-c_skip) / sc_box_size;
    let b_skip = batch_size - sc_in_batch * sc_box_size;

    let fit_percentage = (100*sc_in_batch*sc_box_size)/batch_size;

    assert!(sc_in_batch>0, "Must fit at least 1 scalar box.");

    if fit_percentage < 70 {println!("WARNING: only {}% of each batch are populated in column b\nIt is possible to increase batch_offset or poly_fan_in to improve this.", fit_percentage)}

    ParamsExt{ num_digits, num_limbs, batch_size, sc_box_size, sc_in_batch, b_skip, c_skip }
}


/// a fixed column that knows how to populate it
/// for some values of i will return default value None
/// introduced because I want to populate the fixed tables in configure, not synthesize
/// (populating fixed tables in synthesize feels like anti-pattern and I'm not signing up
/// for any design decision that somehow led to this)
pub struct Expansion<F: Field>{
    pub col: Column<Fixed>,
    pub f: Box<dyn Fn (usize) -> Option<F>>, 
}

impl <F: Field> Expansion<F> {
    /// add an additional case to the previously existing ones
    /// cases must be mutually exclusive, or it will panic at runtime
    /// do not call it too many times, flatten instead; this is only convenience thing
    pub fn update(&mut self, g: impl Fn (usize) -> Option<F>) -> () {
        let tmp = |i| {
            match ((self.f)(i), (g(i))) {
                (Some(x), Some(y)) => panic!("non-mutually exclusive cases when attempting to process column expansion"),
                (None, Some(y)) => Some(y),
                (Some(x), None) => Some(x),
                (None, None) => None,
            }
        };
        self.f = Box::new(tmp);
    }

    /// creates a new unpopulated fixed expansion column
    pub fn new (meta: &mut ConstraintSystem<F>) -> Self {
        let col = meta.fixed_column();
        Expansion { col, f: Box::new(|_|None) }
    }
}

pub struct CA1{
    pub first_free_row: usize,
    pub table_init_batch: usize,
}

pub struct DNCA1{
    pub first_free_batch: usize,
    pub table_init_batch: usize,
}
pub enum TableData {
    ConsumesA1(CA1),
    DidNotConsumeA1(DNCA1),
}



#[derive(Clone)]
pub struct LiamMSMConfig<F: PrimeField + Ord + FftPrecomp, C: CurveExt<Base = F>> {
    pub a: Column<Advice>,
    pub b: Column<Advice>,
    pub c: Column<Advice>,
    // in my implementation, selectors are just fixed columns, because I sometimes reuse them for various weird stuff,
    // and combining is, thus, undesirable

    pub s1: Column<Fixed>,
    pub s2: Column<Fixed>,
    pub s3: Column<Fixed>,
    pub s4: Column<Fixed>,

    pub s_table_1: Column<Fixed>,
    pub s_table_2: Column<Fixed>,
    pub s_arith: Column<Fixed>,

    pub table: Column<Fixed>,

    pub v: Challenge,
    pub ch : Challenge,
    pub r : Challenge,

    pub params : Params<F,C>,
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

impl <F: PrimeField + Ord + FftPrecomp, C: CurveExt<Base = F>> LiamMSMConfig<F,C>{

    pub fn configure(meta: &mut ConstraintSystem<F>, params: Params<F,C>) -> Self{
        let params_ext = params_check(&params);
        
        let Params{num_pts, base, logtable, poly_fan_in, batch_offset, pts:_} = params;
        let ParamsExt{num_digits, num_limbs, batch_size, sc_box_size, sc_in_batch, b_skip, c_skip} = params_ext;

        let a = meta.advice_column_in(FirstPhase);
        let b = meta.advice_column_in(SecondPhase);
        let c = meta.advice_column_in(ThirdPhase);

        let s1poly = Expansion::new(meta);
        let s2poly = Expansion::new(meta);
        let s3poly = Expansion::new(meta); // these govern the poly gate

        let s0sc = Expansion::new(meta); // 1st row of each batch in B1
        let s1sc = Expansion::new(meta); // 1st row of each sc_box
        let s2sc = Expansion::new(meta); // primary rotations
        let s3sc = Expansion::new(meta); // secondary rotations
        let s4sc = Expansion::new(meta); // complement of s1,s2,s3 above in A1

        let s1t = Expansion::new(meta); 
        let s2t = Expansion::new(meta);

        let table = Expansion::new(meta); // lookup table

        let s_arith = meta.fixed_column();
        
//        let constants = meta.fixed_column();

        let v = meta.challenge_usable_after(SecondPhase); // lookup argument challenge
        let ch = meta.challenge_usable_after(FirstPhase); // Liam Eagen's argument challenge used to derive points
        let r = meta.challenge_usable_after(SecondPhase); // random coefficient for linear combination of polynomials


        meta.enable_equality(c);

        // generic gate allowing arithmetic operations in column c
        // it also allows to copy data from column b, and from constants table as a side-effect
        meta.create_gate("arithmetic gate", |meta|{
            let s = meta.query_fixed(s_arith, Rotation(-1));
            let b0 = meta.query_advice(b, Rotation(0)); 
            let cn0 = meta.query_advice(c, Rotation(0));
            let cn1 = meta.query_advice(c, Rotation(-1));
            let cn2 = meta.query_advice(c, Rotation(-2));
            let cn3 = meta.query_advice(c, Rotation(-3));
            let const0 = meta.query_fixed(table.col, Rotation(0));
            let const1 = meta.query_fixed(table.col, Rotation(1));
            // b * CONST + c[-3] * c[-2] + c[-1] * CONST[1] - c[0]
            //this allows to also reuse it to copy data from from column b
            let gate = e!(b0)*e!(const0) + e!(cn3)*e!(cn2) + e!(cn1)*e!(const1) - e!(cn0);
            [s*gate]
        });

        meta.create_gate("polynomials random linear combination", |meta|{
            let mut powers_of_r = vec![Expression::Constant(F::ONE), meta.query_challenge(r)];
            for i in 1..params.poly_fan_in {
                powers_of_r.push(e!(powers_of_r[i]) * e!(powers_of_r[0]))
            }
            // this will generate array 1, r, r^2, ..., r^{poly_fan_in}

            let c0 = meta.query_advice(c, Rotation(0));
            let cn1 = meta.query_advice(c, Rotation(-1));

            // if we think that initial rotation is at first line of c_skip, then its absolute coordinate is
            // batch_size-c_skip. therefore, to refer to the 0-th row from it, we would use negated batch_size-c_skip
            let mut a_rots = vec![];
            for i in 0..params.poly_fan_in {
                let k : i32 = (i * c_skip) as i32 - batch_size as i32 + c_skip as i32;
                a_rots.push(meta.query_advice(a, Rotation(k)));
            }
            let mut gate_full_fan_in_init = -e!(c0);
            for i in 0..params.poly_fan_in {
                gate_full_fan_in_init = e!(gate_full_fan_in_init) + e!(powers_of_r[i])*e!(a_rots[i]); 
            }

            let mut gate_full_fan_in = e!(cn1)*powers_of_r[params.poly_fan_in] - e!(c0);
            for i in 0..params.poly_fan_in {
                gate_full_fan_in = e!(gate_full_fan_in) + e!(powers_of_r[i])*e!(a_rots[i]); 
            }

            let mut gate_trunc_fan_in = e!(cn1)*powers_of_r[params.poly_fan_in] - e!(c0);
            for i in 0..params.poly_fan_in-1 {
                gate_trunc_fan_in = e!(gate_trunc_fan_in) + e!(powers_of_r[i])*e!(a_rots[i]); 
            }

            let s1 = meta.query_fixed(s1poly.col, Rotation(0));
            let s2 = meta.query_fixed(s2poly.col, Rotation(0));
            let s3 = meta.query_fixed(s3poly.col, Rotation(0));

            [s1*gate_full_fan_in_init + s2*gate_full_fan_in + s3*gate_trunc_fan_in]
        });

        // populate the poly selectors
        // we activate s1 at the first line of c_skip
        s1poly.update(|i|{
            if i >= batch_size * (num_pts + base + 1) {return None}
            Some(
                if (i%batch_size == batch_size - c_skip) {
                    F::ONE
                } else {
                    F::ZERO
                }
            )
        });

        // s2 is activated provided that the last entry (which is i%batch_size-(batch_size-c_skip) + (poly_rot-1)*c_skip)
        // is < num_digits
        s2poly.update(|i|{
            if i >= batch_size * (num_pts + base + 1) {return None}
            Some(
                if (i%batch_size > batch_size - c_skip) &&
                (i%batch_size + poly_fan_in*c_skip < num_digits) {
                    F::ONE
                } else {
                    F::ZERO
                } 
            )
        });

        s3poly.update(|i|{
            if i >= batch_size * (num_pts + base + 1) {return None}
            Some(
                if (i%batch_size > batch_size - c_skip) &&
                    (i%batch_size + poly_fan_in*c_skip >= num_digits) {
                        F::ONE
                    } else {
                        F::ZERO
                    } 
            )
        });
        // this gate will be activate in a scalars region in column b
        // which is (N * BATCH_SIZE) first rows
        // it guarantees that each batch adheres to the structure described in layout.md
        // additionally, every limb + every integrity value must be checked with lookup
        meta.create_gate("b gate", |meta|{
            let b0 = meta.query_advice(b, Rotation(0));
            let b_primary_offsets : Vec<_> = (1..num_limbs+1).into_iter().map(
                |i|meta.query_advice(b, Rotation(i as i32))
            ).collect();
            let b_secondary_offsets : Vec<_> = (1..base).into_iter().map(
                |i| meta.query_advice(b, Rotation((i*(num_limbs+1)) as i32))
            ).collect();
            let mut gate_sc_from_buckets = -e!(b0);
            for i in 0..base-1 {
                gate_sc_from_buckets = gate_sc_from_buckets + e!(b_secondary_offsets[i])*(F::from(digit_by_id(i) as u64));
            }
            let mut gate_limb_integrity_check = -e!(b0);
            for i in 0..base-1 {
                gate_limb_integrity_check = gate_limb_integrity_check + e!(b_secondary_offsets[i]);
            }
            let mut gate_bucket_from_limbs = -e!(b0);
            for i in 0..num_limbs {
                gate_bucket_from_limbs = gate_bucket_from_limbs + e!(b_primary_offsets[i]) * F::from(base as u64).pow([(i*logtable) as u64]);
            }
            let s1 = meta.query_fixed(s1sc.col, Rotation(0));
            let s2 = meta.query_fixed(s2sc.col, Rotation(0));
            let s3 = meta.query_fixed(s3sc.col, Rotation(0));

            [s1*gate_sc_from_buckets + s2*gate_bucket_from_limbs + s3*gate_limb_integrity_check]
        });

        //populate the scalar selectors

        let bound = (num_pts/sc_in_batch) * batch_size + (num_pts%sc_in_batch) * sc_box_size;

        s1sc.update(|i|{
            if i >= bound {return None};
            Some ({
                let i = i%batch_size;
                if i >= sc_box_size*sc_in_batch {return Some(F::ZERO)};
                let i = i%sc_box_size;
                if i == 0 {F::ONE} else {F::ZERO}
            })
        });

        s2sc.update(|i|{
            if i >= bound {return None};
            Some ({
                let i = i%batch_size;
                if i >= sc_box_size*sc_in_batch {return Some(F::ZERO)};
                let i = i%sc_box_size;
                if i>0 && i%(num_limbs+1)==0 {F::ONE} else {F::ZERO}
            })
        });        

        s3sc.update(|i|{
            if i >= bound {return None};
            let threshold = if i < bound-batch_size {sc_box_size*sc_in_batch} else {sc_box_size*(num_pts-sc_in_batch*(i/batch_size))};
            Some ({
                let i = i%batch_size;
                if i >= sc_box_size*sc_in_batch {return Some(F::ZERO)};
                let i = i%sc_box_size;
                if i>0 && i<(num_limbs+1) {F::ONE} else {F::ZERO}
            })
        });
        // this gate implements custom lookup argument
        // it spans first two regions in the column b - the N*BATCH_SIZE - sized first region, and additional
        // region of size ~ 2^LOGTABLESIZE * (BATCH_SIZE / (BATCH_SIZE - SKIP)) hosting the table
        // it implements a custom lookup argument, using a challenge v
        meta.create_gate("lookup", |meta|{
            let c0 = meta.query_advice(c, Rotation(0));
            let c1 = meta.query_advice(c, Rotation(1));
            let cn1 = meta.query_advice(c, Rotation(-1));
            let cnbskip = meta.query_advice(c, Rotation(-(1 + b_skip as i32)));
            let cncskip = meta.query_advice(c, Rotation(-(1 + c_skip as i32)));

            let b0 = meta.query_advice(b, Rotation(0));
            let b1 = meta.query_advice(b, Rotation(1));
            let v = meta.query_challenge(v);
            let t = meta.query_fixed(table.col, Rotation(0));

            // c[i+1] - c[i] = 1 / (v - b[i+1]) -- must be active on all cells corresponding to limbs / integrities from i = -1 
            let gate_lookup_rhs_1 = (e!(c1) - e!(c0))*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));
            // c[i+1] - c[i-1] = 1/(v-b[i+1]) -- must be active for i corresponding to buckets - to jump over them
            let gate_lookup_rhs_2 = (e!(c1) - e!(cn1))*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));
            // c[i+1] - c[i-b_skip-1] = 1/(v-b[i+1]) -- must be active for i corresponding to scalars - to jump over them and end of batch empty space
            let gate_lookup_rhs_3 = (e!(c1) - e!(cnbskip))*(e!(v)-e!(b1)) - Expression::Constant(F::from(1));

            // (c[1] - c[0] CONST - c[-(SKIP+1)](1 - CONST)) * (v-t) - b[1]
            let gate_lookup_lhs_1 = (e!(c0) - e!(cn1))*(e!(v)-e!(t)) + e!(b0);
            let gate_lookup_lhs_2 = (c0 - e!(cncskip))*(v-t) + b0;

            let s0 = meta.query_fixed(s0sc.col, Rotation(0));
            let s1 = meta.query_fixed(s1sc.col, Rotation(0)); 
            let s2 = meta.query_fixed(s2sc.col, Rotation(0));
            let s4 = meta.query_fixed(s4sc.col, Rotation(0)); 

            let sl1 = meta.query_fixed(s1t.col, Rotation(0));
            let sl2 = meta.query_fixed(s2t.col, Rotation(0));


            [s4*gate_lookup_rhs_1 + s2*gate_lookup_rhs_2 + (s1-s0)*gate_lookup_rhs_3
            + sl1*gate_lookup_lhs_1 + sl2*gate_lookup_lhs_2]
        });

        // populating the table and other selectors

        // s0sc is just active at 1st row of every batch in B1
        s0sc.update(|i|{
            if i >= bound {return None};
            let i = i%batch_size;
            Some(
                if i == 0 {F::ONE} else {F::ZERO}
            )
        });

        s4sc.update(|i|{
            if i >= bound {return None};
            let i = i%batch_size;
            if i >= sc_box_size*sc_in_batch {return Some(F::ZERO)};
            let i = i%sc_box_size;
            Some(
                if i%(num_limbs+1)>0 && i%base>0 {F::ONE} else {F::ZERO}
            )
        });

        //table is allocated in a following way: we leave 1 batch empty, and then allocate until the end of A1
        let table_init_batch = batch_size*div_ceil(num_pts, sc_in_batch) + 1;
        let remaining_batches = (num_pts+base+1) - table_init_batch + 1;
        let remaining_A1_rows = remaining_batches * (batch_size-c_skip);

        let tmp = div_ceil(pow(2, logtable) as usize, (batch_size - c_skip));

        let table_data = if remaining_batches > tmp {
            TableData::DidNotConsumeA1(DNCA1{table_init_batch, first_free_batch : table_init_batch+(remaining_batches-tmp)})
        } else {
            TableData::ConsumesA1(CA1{})
        }


        meta.create_gate("rhs main", |meta|{
            let c0 = meta.query_advice(c, Rotation(0));
            let b0 = meta.query_advice(b, Rotation(0));
            let cn_noskip = meta.query_advice(c, Rotation(-(1+NUM_LIMBS as i32)));
            let cn_skip = meta.query_advice(c, Rotation(-((2+SKIP+NUM_LIMBS) as i32)));
            
            let ptx = meta.query_fixed(table, Rotation(0)); // these two slots contain coordinates of precomputed point
            let pty = meta.query_fixed(table, Rotation(1));

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

            let s_sec = meta.query_fixed(s2, Rotation(0));
            let s_skip = meta.query_fixed(s1, Rotation(-1));
            [(s_sec-e!(s_skip))*gate_noskip + s_skip*gate_skip]

        });

        Self{a, b, c, s1, s2, s3, s4, table, s_arith, s_table_1, s_table_2, v, ch, r, params}
    }

}

#[derive(Clone)]
pub struct LiamMSMCircuit<F: PrimeField+Ord+FftPrecomp, C: CurveExt<Base=F>> {
    params: Params<F,C>,
    scalars: Vec<BigInt>,
    _marker: PhantomData<(F,C)>,
}

#[derive(Clone)]
pub struct Params<F : PrimeField + Ord + FftPrecomp, C : CurveExt<Base=F>> {
    num_pts: usize, // number of points
    base: usize, // base of decomposition
    logtable: usize, // logsize of the table
    poly_fan_in: usize, // amount of elements taken in 1 linear combination
    batch_offset: usize, // amount of elements intentionally left empty in each batch
    pts: Vec<C>, // points for fixed base MSM, must have length num_pts
}

//additional parameters
pub struct ParamsExt{
    num_digits: usize,
    num_limbs: usize,
    batch_size: usize,
    sc_box_size : usize,
    sc_in_batch: usize,
    b_skip: usize,
    c_skip: usize,
}

impl<F : PrimeField + Ord + FftPrecomp, C : CurveExt<Base=F>> Default for Params<F,C> {
    fn default() -> Params<F,C>{
        unreachable!()
    }
}

impl<F: PrimeField+Ord+FftPrecomp, C: CurveExt<Base = F>> Circuit<F> for LiamMSMCircuit<F,C> {
    type Config = LiamMSMConfig<F,C>;
    type FloorPlanner = V1;
    type Params = Params<F,C>;

    fn without_witnesses(&self) -> Self {
        (*self).clone()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        unreachable!()
    }

    fn params(&self) -> Self::Params {
        (*self).params.clone()
    }

    fn configure_with_params(
        meta: &mut ConstraintSystem<F>,
        params: Self::Params,
    ) -> Self::Config {
        Self::Config::configure(meta, params)
    }

    fn synthesize(&self, mut cfg: Self::Config, mut ly: impl Layouter<F>) -> Result<(), Error> {
        let ly = &mut ly;
        
        let Params{num_pts, base, logtable, poly_rot, batch_size, pts} = cfg.params;

        // we start off by computing various constants required in our circuit
        let b_size = (num_pts+base+1)/2; // amount of coefficients in b(x)
        let a_size = (num_pts+base+2)/2; // amount of coefficients in a(x)
        // sanity check - if num_pts+base+1 == 3, b_size will be 1 and a_size will be 2, as it should be for line func
        let p = order::<F>();
        let sq_p = (&p.sqrt()+BigInt::from_bytes_le(Sign::Plus, &[2])).to_biguint().unwrap();
        let digits = logb_ceil(&sq_p, base as u8) as usize;
        let num_limbs = (digits + logtable + 1)/logtable - 1; // ceil(digits/logtable)
        assert!(batch_size % poly_rot == 0);
        let polys_in_batch = batch_size / poly_rot;
        let skip = batch_size - (num_limbs + 1)*base;
        assert! (skip >= polys_in_batch);
        assert! (num_pts % batch_size == 0);
        assert!(pts.len() == num_pts);

        // and now prepare scalars for further consumption
        let scalars = self.scalars.clone();

        

        let v = ly.get_challenge(cfg.v);
        let ch = ly.get_challenge(cfg.ch);
        let r = ly.get_challenge(cfg.r);
        
        let _ = ly.assign_region(||"main", |region|{
            
            macro_rules! v {
                ($e:expr) => {
                    Value::known($e)
                }; // also very convenient and also stolen from Onur Kilic
            


            
            
            }
            


            Ok(())
        });

        Err(Error::Synthesis)
    }


}

#[test]

fn configure_test(){
    let mut cs : ConstraintSystem<F> = ConstraintSystem::default();
    LiamMSMConfig::<F, Grumpkin>::configure(&mut cs);
}