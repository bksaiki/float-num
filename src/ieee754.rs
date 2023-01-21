use num_bigint::BigUint;
use std::ops::ShlAssign;

use crate::number::Number;

mod arithmetic;
mod conversions;
mod number;
mod rounding;

pub(crate) type BitVec = bitvec::prelude::BitVec<u32, Lsb0>;
pub(crate) type Lsb0 = bitvec::prelude::Lsb0;

// Converts a `BitVec` to `BitUint`
// TODO: this is really dumb
pub(crate) fn bitvec_to_biguint(mut bv: BitVec) -> BigUint {
    let mut i = BigUint::default();
    bv.reverse();
    for b in bv {
        i.shl_assign(1);
        i.set_bit(0, b);
    }
    i
}

// Converts a `BitUint` to `BitVec`
// TODO: this is really dumb
pub(crate) fn biguint_to_bitvec(i: BigUint, width: usize) -> BitVec {
    let mut bv = BitVec::from_vec(i.to_u32_digits());
    bv.resize(width, false);
    bv
}

/// Rounding direction
///
/// Sometimes only a rounding direction is requires to specify
/// a rounding behavior rather than a rounding mode.
///
pub enum RoundingDirection {
    ToZero,
    AwayZero,
    ToEven,
    ToOdd,
}

/// Rounding modes
///
/// The IEEE-754 standard specifies five rounding modes:
///
/// - two nearest modes:
///   - _roundTiesToEven_: rounds to the nearest representable floating-point value.
///      In this case there is a tie, round to the floating-point value whose
///      mantissa has a least significant bit of 0.
///   - _roundTiesToAway_: rounds to the nearest representable floating-point value.
///      In this case there is a tie, round to the floating-point value with greater magnitude.
/// - three directed modes:
///   - _roundTowardPositive_: rounds to the closest representable floating-point value
///     in the direction of positive infinity.
///   - _roundTowardNegative_: rounds to the closest representable floating-point value
///     in the direction of negative infinity.
///   - _roundTowardZero_: rounds to the closest representable floating-point value
///     in the direction of zero.
///
/// This module defines two additional rounding modes:
/// - _roundAwayZero_: rounds to the closest representable floating-point value
///     away from zero, towards the nearest infinity.
/// - _roundToOdd_: rounds to the closest representable floating-point value
///     whose mantissa has a least significant bit of 1.
///
/// The rounding behavior of zero, signed zero, positive infinity, negative infinity,
/// and all encodings of NaN  will be unaffected by rounding mode.
///
#[derive(Copy, Clone)]
pub enum RoundingMode {
    NearestEven,
    NearestAway,
    ToPositive,
    ToNegative,
    ToZero,
    AwayZero,
    ToOdd,
}

/// Exception flags as specified by the IEEE-754 standard.
///
/// Besides returning a (possibly) numerical result, any computation with
/// floating-point numbers may also raise exceptions depending on certain conditions.
/// These exceptions include:
///
/// - _invalid operation_: no useful definable result;
/// - _division by zero_: an infinite result for finite arguments;
/// - _overflow_: result exceeded in magnitude what would have been the rounded result
///     had the exponent range been unbounded;
/// - _underflow_: non-zero result that either (a) would lie strictly between
///     `-b^emin` and `+b^emin` had the exponent range been unbounded,
///     or (b) would lie strictly between `-b^emin` and `+b^emin`
///     had the exponent range and precision been unbounded;
/// - _inexact_: result would be different had both the exponent range
///     and precision been unbounded.
///
/// This module defines a sixth:
/// - _carry_: the exponent of the rounded result when in the form `(-1)^s x c x b^e`
///     is different than the real result. In particular, it was incremented
///     by 1 by the rounding operation.
///
#[derive(Copy, Clone, Default)]
pub struct Exceptions {
    /// The _invalid operation_ flag.
    pub invalid: bool,
    /// The _division by zero_ flag.
    pub div_by_zero: bool,
    /// The _overflow_ flag.
    pub overflow: bool,
    /// The _underflow_ flag.
    pub underflow: bool,
    /// The _inexact_ flag.
    pub inexact: bool,
    /// The _carry_ flag.
    pub carry: bool,
}

// Minimal floating-point encoding grouped by classification
enum FloatNum {
    // signed zero or finite number
    // => (sign, exponent, significand)
    Number(bool, i64, BitVec),
    // infinity (+/-)
    // => (sign)
    Infinity(bool),
    // not-a-number
    // => (sign, signaling, payload)
    Nan(bool, bool, BitVec),
}

/// A floating-point number as specified by the IEEE-754 standard.
///
/// The generics `E` and `N` specify the number of bits in the
/// exponent field and in the entire float overall.
///
#[derive(Clone)]
pub struct Float<const E: usize, const N: usize> {
    num: FloatNum,     // number encoding
    flags: Exceptions, // exceptions
}

/// Alias for `Float<15, 128>` (quad-precision number)
pub type Quad = Float<15, 128>;
/// Alias for `Float<11, 64>` (double-precision number)
pub type Double = Float<11, 64>;
/// Alias for `Float<8, 32>` (single-precision number)
pub type Single = Float<8, 32>;
/// Alias for `Float<5, 16>` (half-precision number)
pub type Half = Float<5, 16>;
