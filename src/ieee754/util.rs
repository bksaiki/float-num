use num_bigint::BigUint;
use std::ops::ShlAssign;

use super::*;

// Converts a `BitVec` to `BitUint`
// TODO: this is really dumb
pub(crate) fn bitvec_to_biguint(bv: &BitVec) -> BigUint {
    let mut i = BigUint::default();
    for b in bv.iter().rev() {
        i.shl_assign(1);
        i.set_bit(0, *b);
    }
    i
}

#[macro_export]
macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
}

// Converts a `BitUint` to `BitVec`
pub(crate) fn biguint_to_bitvec(i: BigUint, width: usize) -> BitVec {
    let mut bv = BitVec::from_vec(i.to_u32_digits());
    bv.resize(width, false);
    bv
}

// Shifts left accumulating a sticky bit that is 1
// when at least one the bits shifted off was 1
// and 0 otherwise
pub(crate) fn shift_left_accum(bv: &mut BitVec, by: usize) -> bool {
    if by == 0 {
        false
    } else if by >= bv.len() {
        let any = bv.any();
        bv.iter_mut().for_each(|mut b| *b = false);
        any
    } else {
        let any = bv[..by].any();
        bv.shift_left(by);
        any
    }
}
