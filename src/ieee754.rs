use core::panic;
use std::{
    cmp::Ordering,
    ops::{AddAssign, ShlAssign},
};

use bitvec::{field::BitField, prelude::Lsb0};
use num_bigint::*;
use num_traits::cast::ToPrimitive;

type BitVec = bitvec::prelude::BitVec<u32, Lsb0>;

macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
}

// Converts a `BitVec` to `BitUint`
// TODO: this is really dumb
fn bitvec_to_biguint(mut bv: BitVec) -> BigUint {
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
fn biguint_to_bitvec(i: BigUint, width: usize) -> BitVec {
    let mut bv = BitVec::from_vec(i.to_u32_digits());
    bv.resize(width, false);
    bv
}

// Specifies a rounding type.
// Used for intermediate rounding.
// Does not specify tie-breaking behavior.
// enum RoundingDirection {
//     Nearest,
//     ToZero,
//     AwayZero,
//     Unknown,
// }

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
/// This module defines a sixth:
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
pub struct Float<const E: usize, const N: usize> {
    num: FloatNum,     // number encoding
    flags: Exceptions, // exceptions
}

macro_rules! assert_valid_format {
    ($E:expr, $N:expr) => {
        assert!(
            (2 <= $E) && ($E <= 60),
            "invalid exponent width, must be 2 <= E <= 60: {}",
            $E
        );
        assert!(
            (2 <= ($N - $E)),
            "invalid total width, must be 2 + E <= N: {}",
            $N
        );
    };
}

// Format parameters
impl<const E: usize, const N: usize> Float<E, N> {
    /// Bitwidth of the representation.
    pub const N: usize = N;

    /// Bitwidth of the exponent field.
    pub const E: usize = E;

    /// Radix, in this case, 2.
    pub const B: usize = 2;

    /// Number of (binary) digits when the significand is expressed
    /// as an integer. This is just `Self::M + 1`.
    pub const PREC: usize = N - E;

    /// Bitwidth of the mantissa field.
    pub const M: usize = Self::PREC - 1;

    /// Exponent of the largest finite floating-point value in
    /// this representation when it is in the form `(-1)^s b^e m`
    /// where `m` is a fraction between 1 and 2.
    pub const EMAX: i64 = i64::pow(2, (E - 1) as u32) - 1;

    /// Exponent of the smallest normal floating-point value in
    /// this representation when it is in the form `(-1)^s b^e m`
    /// where `m` is a fraction between 1 and 2.
    /// This is just `1 - Self::EMAX`.
    pub const EMIN: i64 = 1 - Self::EMAX;

    /// Exponent of the largest finite floating-point value in
    /// this representation when it is in the form `(-1)^s b^e c`
    /// where `c` is an integer.
    /// This is just `Self::EMAX - Self::M`.
    pub const EXPMAX: i64 = Self::EMAX - Self::M as i64;

    /// Exponent of the smallest normal floating-point value in
    /// this representation when it is in the form `(-1)^s b^e c`
    /// where `c` is an integer.
    /// This is just `Self::EMAX - Self::M`.
    pub const EXPMIN: i64 = Self::EMIN - Self::M as i64;

    /// Bitwidth of the NaN payload.
    /// This is just `Self::M - 1`.
    pub const NAN_PAYLOAD_SIZE: usize = Self::M - 1;

    /// Returns the exponent bias.
    /// This is just `Self::EMAX`.
    #[inline(always)]
    pub const fn bias() -> i64 {
        Self::EMAX
    }
}

// Constructors and getters
impl<const E: usize, const N: usize> Float<E, N> {
    /// Creates a new `Float` with `E` exponent bits and `N` total bits.
    /// Initializes the `Float` to +0.
    pub fn new() -> Self {
        assert_valid_format!(E, N);
        Self {
            num: FloatNum::Number(false, 0, bitvec![0; Self::PREC]),
            flags: Exceptions::default(),
        }
    }

    /// Returns an infinity with a particular sign
    /// using the same width parameters as this `Float`.
    pub fn infinity(sign: bool) -> Self {
        Self {
            num: FloatNum::Infinity(sign),
            flags: Exceptions::default(),
        }
    }

    /// Returns a zero with a particular sign
    /// using the same width parameters as this `Float`.
    pub fn zero(sign: bool) -> Self {
        Self {
            num: FloatNum::Number(sign, 0, bitvec![0; Self::PREC]),
            flags: Exceptions::default(),
        }
    }

    /// Returns an NaN value based on the specified sign, signaling status
    /// and payload using the same width parameters as this `Float`.
    pub fn nan(sign: bool, signaling: bool, payload: impl Into<BitVec>) -> Self {
        let bv = payload.into();
        assert_eq!(
            bv.len(),
            Self::NAN_PAYLOAD_SIZE,
            "expected a payload size of {}, received {}",
            Self::NAN_PAYLOAD_SIZE,
            bv.len()
        );
        Self {
            num: FloatNum::Nan(sign, signaling, bv),
            flags: Exceptions::default(),
        }
    }

    /// Returns the sign of this `Float`.
    pub fn sign(&self) -> bool {
        match self.num {
            FloatNum::Number(s, _, _) => s,
            FloatNum::Infinity(s) => s,
            FloatNum::Nan(s, _, _) => s,
        }
    }

    /// Returns the exponent of this `Float`.
    /// The result is wrapped in an option since only finite
    /// numbers have a valid exponent.
    pub fn exponent(&self) -> Option<i64> {
        match self.num {
            FloatNum::Number(_, exp, _) => Some(exp),
            _ => None,
        }
    }

    /// Returns the (integer) mantissa of this `Float` as a `Bitvec`.
    /// The result is wrapped in an option since only finite numbers
    /// have a valid exponent.
    pub fn significand(&self) -> Option<BitVec> {
        match &self.num {
            FloatNum::Number(_, _, c) => Some(c.clone()),
            _ => None,
        }
    }

    /// Returns true if this `Float` encodes a zero.
    pub fn is_zero(&self) -> bool {
        match &self.num {
            FloatNum::Number(_, e, c) => *e == 0 && c.not_any(),
            _ => false,
        }
    }

    /// Returns true if this `Float` encodes a subnormal number
    pub fn is_subnormal(&self) -> bool {
        match &self.num {
            FloatNum::Number(_, e, _) => *e < Self::EMIN,
            _ => false,
        }
    }

    /// Returns true if this `Float` encodes a normal number
    pub fn is_normal(&self) -> bool {
        match &self.num {
            FloatNum::Number(_, e, c) => *e >= Self::EMIN && (*e != 0 || c.some()),
            _ => false,
        }
    }

    /// Returns true if this `Float` encodes an infinity.
    pub fn is_infinity(&self) -> bool {
        matches!(self.num, FloatNum::Infinity(_))
    }

    /// Returns true if this `Float` encodes a NaN.
    pub fn is_nan(&self) -> bool {
        matches!(self.num, FloatNum::Nan(_, _, _))
    }

    /// Returns true if this `Float` encodes a signaling NaN.
    /// The result is wrapped in an option since only NaNs can be signaling.
    pub fn is_signaling_nan(&self) -> Option<bool> {
        match self.num {
            FloatNum::Nan(_, signal, _) => Some(signal),
            _ => None,
        }
    }

    /// Returns the NaN payload of this `Float` as a `Bitvec`.
    /// The result is wrapped in an option since only a NaN has a payload.
    pub fn nan_payload(&self) -> Option<BitVec> {
        match &self.num {
            FloatNum::Nan(_, _, payload) => Some(payload.clone()),
            _ => None,
        }
    }

    /// Returns the state of all flags raised during
    /// the operation that created this `Float`.
    pub fn flags(&self) -> Exceptions {
        self.flags
    }

    /// Returns true if the `invalid` flag was raised
    /// during the operation that created this `Float`.
    pub fn invalid_flag(&self) -> bool {
        self.flags.invalid
    }

    /// Returns true if the `div_by_zero` flag was raised
    /// during the operation that created this `Float`.
    pub fn div_by_zero_flag(&self) -> bool {
        self.flags.div_by_zero
    }

    /// Returns true if the `overflow` flag was raised
    /// during the operation that created this `Float`.
    pub fn overflow_flag(&self) -> bool {
        self.flags.overflow
    }

    /// Returns true if the `underflow` flag was raised
    /// during the operation that created this `Float`.
    pub fn underflow_flag(&self) -> bool {
        self.flags.underflow
    }

    /// Returns true if the `inexact` flag was raised
    /// during the operation that created this `Float`.
    pub fn inexact_flag(&self) -> bool {
        self.flags.inexact
    }

    /// Returns true if the `carry` flag was raised
    /// during the operation that created this `Float`.
    pub fn carry_flag(&self) -> bool {
        self.flags.carry
    }
}

// Utility
impl<const E: usize, const N: usize> Float<E, N> {
    // Splices a packed floating-point representation into
    // the sign, exponent, and mantissa field.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn split_packed(bv: &BitVec) -> (bool, BitVec, BitVec) {
        (
            Self::packed_sign(bv),
            Self::packed_exponent(bv),
            Self::packed_mantissa(bv),
        )
    }

    #[inline]
    fn pack_components(s: bool, e: BitVec, m: BitVec) -> BitVec {
        assert_eq!(
            e.len(),
            E,
            "trying to pack a float with exponent width: {}, expected {}",
            e.len(),
            E
        );
        assert_eq!(
            m.len(),
            Self::M,
            "trying to pack a float with mantissa width: {}, expected {}",
            m.len(),
            Self::M
        );

        let mut bv = bitvec![0; N];
        for (i, b) in m.iter().enumerate() {
            bv.set(i, *b);
        }
        for (i, b) in e.iter().enumerate() {
            bv.set(i + Self::M, *b);
        }
        bv.set(N - 1, s);
        bv
    }

    // Returns the sign field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_sign(bv: &BitVec) -> bool {
        bv[N - 1]
    }

    // Returns the exponent field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_exponent(bv: &BitVec) -> BitVec {
        bv[(N - E - 1)..(N - 1)].into()
    }

    // Returns the mantissa field from a packed floating-point representation.
    // Does not check if `bv` has the correct number of bits.
    #[inline]
    fn packed_mantissa(bv: &BitVec) -> BitVec {
        bv[..(N - E - 1)].into()
    }
}

// Rounding (casts)
impl<const E: usize, const N: usize> Float<E, N> {
    /// Rounds this `Float` to the representation specified by `Float<E2, N2>`.
    pub fn round<const E2: usize, const N2: usize>(&self, rm: RoundingMode) -> Float<E2, N2> {
        match &self.num {
            FloatNum::Number(s, exp, c) => Self::round_finite(*s, *exp, c.clone(), rm),
            FloatNum::Infinity(s) => Float::<E2, N2>::infinity(*s),
            FloatNum::Nan(s, signal, payload) => {
                let payload = if Self::NAN_PAYLOAD_SIZE < Float::<E2, N2>::NAN_PAYLOAD_SIZE {
                    // expand the payload with zeros
                    // payload is put in the most signficant bits
                    let diff = Float::<E2, N2>::NAN_PAYLOAD_SIZE - Self::NAN_PAYLOAD_SIZE;
                    let mut p = BitVec::repeat(false, Float::<E2, N2>::NAN_PAYLOAD_SIZE);
                    for (i, b) in payload.iter().enumerate() {
                        p.set(diff + i, *b);
                    }
                    p
                } else {
                    // truncate the payload
                    // only keep the most signficant bits
                    let size = Float::<E2, N2>::NAN_PAYLOAD_SIZE;
                    let diff = Self::NAN_PAYLOAD_SIZE - size;
                    let mut p = BitVec::repeat(false, size);
                    for i in 0..size {
                        p.set(i, *payload.get(i + diff).unwrap());
                    }
                    p
                };
                Float::<E2, N2>::nan(*s, *signal, payload)
            }
        }
    }

    // Rounds a finite, non-zero number in the representation specified
    // by `Float<E2, N2>` using the rounding mode `rm`.
    fn round_finite<const E2: usize, const N2: usize>(
        s: bool,
        mut exp: i64,
        c: BitVec,
        rm: RoundingMode,
    ) -> Float<E2, N2> {
        if exp == 0 && c.not_any() {
            // The exceptional case: exact zero
            // Return zero, no exception flags are raised
            Float::<E2, N2>::zero(s)
        } else {
            // We will construct the new mantissa with three rounding bits
            // Then we'll call the (rounding) finalizer to complete the rounding
            // process and raise the correct exception flags.
            let mut c_new = bitvec![0; Float::<E2, N2>::PREC];
            let mut half_bit = false;
            let mut quarter_bit = false;
            let mut sticky_bit = false;
            let prec = c.len();

            // Branch on mantissa size comparison
            match Float::<E2, N2>::PREC.cmp(&prec) {
                Ordering::Equal => {
                    // The current mantissa is the new mantissa
                    //  - `half_bit`, `quarter_bit`, `sticky_bit` are zero
                    //  - preserve the mantissa and exponent
                    c_new = c;
                }
                Ordering::Greater => {
                    // The current mantissa will fit entirely in the new mantissa:
                    //  - insert most significant bits, then fill with zeros
                    //  - `half_bit`, `quarter_bit`, `sticky_bit` are zero
                    //  - adjust `exp` accordingly
                    let diff = Float::<E2, N2>::PREC - prec;
                    for (i, b) in c.iter().enumerate() {
                        c_new.set(i + diff, *b);
                    }

                    exp -= diff as i64;
                }
                Ordering::Less => {
                    // Truncation will occur:
                    //  - preserve the highest `Float::<E2, N2>::PREC` bits
                    //  - the next two bits are the `half_bit` and `sticky_bit`
                    //  - if any of the remaining bits are high, set `sticky_bit` to 1
                    //  - adjust exp accordingly
                    let diff = prec - Float::<E2, N2>::PREC;
                    if diff == 1 {
                        // optimized case:
                        //  - `m2` is `m[1..PREC]`
                        //  - half bit is m[0]
                        //  - sticky_bit is 0
                        c_new = c[1..prec].into();
                        half_bit = c[0];
                    } else if diff == 2 {
                        // optimized case
                        //  - `m2` is `m[2..PREC]`
                        //  - half bit is m[1]
                        //  - sticky bit is m[0]
                        c_new = c[2..prec].into();
                        half_bit = c[1];
                        quarter_bit = c[0];
                    } else {
                        // hard case:
                        //  - actually split the mantissa
                        //  - `m2` is the high part
                        //  - half bit is the MSB of the low part
                        //  - sticky bit is OR of the rest of the low part
                        let (low, high) = c.split_at(diff);
                        let low_len = low.len();

                        c_new = high.into();
                        half_bit = low[low_len - 1];
                        quarter_bit = low[low_len - 2];
                        sticky_bit = low[.. low_len - 2].any();
                    }

                    exp += diff as i64;
                }
            }

            // adjust if the exponent is too small
            // TODO: this is dumb
            if exp < Float::<E2, N2>::EMIN {
                while exp < Float::<E2, N2>::EMIN  - 1 {
                    sticky_bit |= quarter_bit;
                    quarter_bit = half_bit;
                    half_bit = c_new[0];
                    c_new.shift_left(1);
                    exp += 1;
                }
            }

            // finish the rounding process with all the rounding information
            Float::<E2, N2>::round_finalize(s, exp, c_new, half_bit, quarter_bit, sticky_bit, rm)
        }
    }

    // Returns true if the rounding information implies the mantissa,
    // as viewed as integer, should be incremented by 1. Unlike `round_finalize`
    // we only need the `half_bit` a sticky bit.
    fn round_requires_increment(
        sign: bool,
        lsb: bool,
        half_bit: bool,
        sticky_bit: bool,
        rm: RoundingMode,
    ) -> bool {
        match rm {
            RoundingMode::NearestEven => {
                // no half bit => truncate
                // half bit and sticky bit => increment
                // tie => increment if lsb since we want it to be 0
                half_bit && (sticky_bit || lsb)
            }
            RoundingMode::NearestAway => {
                // no half bit => truncate
                // half bit => increment (tie requires increment)
                half_bit
            }
            RoundingMode::ToPositive => {
                if sign {
                    // negative => always truncate
                    false
                } else {
                    // positive => increment if not exact
                    half_bit || sticky_bit
                }
            }
            RoundingMode::ToNegative => {
                if sign {
                    // negative => increment if not exact
                    half_bit || sticky_bit
                } else {
                    // positive => always truncate
                    false
                }
            }
            RoundingMode::ToZero => {
                // always truncate
                false
            }
            RoundingMode::AwayZero => {
                // increment if not exact
                half_bit || sticky_bit
            }
            RoundingMode::ToOdd => {
                // LSB of the mantissa needs to be 1
                !lsb
            }
        }
    }

    // Assuming overflow has occured, return true if
    // the result should be rounded to +/- infinity
    // (rather than +/- MAX_FLOAT).
    fn overflow_to_infinity(sign: bool, rm: RoundingMode) -> bool {
        match rm {
            // carry all overflows to infinity
            RoundingMode::NearestEven => true,
            RoundingMode::NearestAway => true,
            // sign-dependent
            RoundingMode::ToPositive => !sign,
            RoundingMode::ToNegative => sign,
            // carry all overflows to MAX_FLOAT
            RoundingMode::ToZero => false,
            // carry all overflows to infinity
            RoundingMode::AwayZero => true,
            // only MAX_FLOAT has an odd mantissa bit
            RoundingMode::ToOdd => false,
        }
    }

    // Constructs a new `Float` based on rounding information.
    // Requires a sign, mantissa, exponent, half bit, and sticky bit
    // The inputs must encode a non-zero, finite number.
    fn round_finalize(
        s: bool,
        mut exp: i64,
        mut m: BitVec,
        half_bit: bool,
        quarter_bit: bool,
        sticky_bit: bool,
        rm: RoundingMode,
    ) -> Self {
        // First, we check if we need to round away from zero.
        // We use the sign, rounding mode, LSB of the mantissa, and the two rounding bits.
        let qs_bit = quarter_bit || sticky_bit;
        let increment = Self::round_requires_increment(s, m[0], half_bit, qs_bit, rm);
        if increment {
            // increment the mantissa
            // possibly need to adjust exponent (the exponent is unbounded)
            let mut c = bitvec_to_biguint(m);
            c.add_assign(1_u8);
            let m_ext = biguint_to_bitvec(c, Self::PREC + 1);
            let carry = m_ext[Self::PREC];

            m = m_ext[0..Self::PREC].into();
            if carry {
                m.set(Self::PREC - 1, true);
                exp += 1;
            }
        }

        // Next, we check if overflow occured and alter the result if it has.
        if exp > Self::EMAX {
            // overflow has occured
            // need to check which way we round
            if Self::overflow_to_infinity(s, rm) {
                return Self {
                    num: FloatNum::Infinity(s),
                    flags: Exceptions {
                        invalid: false,
                        div_by_zero: false,
                        overflow: true,
                        underflow: false,
                        inexact: true,
                        carry: increment,
                    },
                };
            } else {
                return Self {
                    num: FloatNum::Number(s, Self::EMAX, bitvec![1; Self::PREC]),
                    flags: Exceptions {
                        invalid: false,
                        div_by_zero: false,
                        overflow: true,
                        underflow: false,
                        inexact: true,
                        carry: increment,
                    },
                };
            }
        }

        // Next, we check if underflow may have occured
        // The underflow exception is only raised if the inexact exception is also raised.
        let underflow = match exp.cmp(&Self::EXPMIN) {
            Ordering::Greater => false,
            Ordering::Less => true,
            Ordering::Equal => {
                if increment && m[..Self::M].not_any() {
                    // result was rounded up to +/-MIN_NORM
                    // with unbounded exponent, would our rounded result have been different, i.e.,
                    // would the rounded result have been halfway between MIN_NORM and MAX_SUBNORM?
                    match rm {
                        // only if we were exactly 3/4 of the way to +/-MIN_NORM
                        RoundingMode::NearestEven => half_bit && quarter_bit && !sticky_bit,
                        RoundingMode::NearestAway => half_bit && quarter_bit && !sticky_bit,
                        // sign-dependent
                        RoundingMode::ToPositive => if s {
                            // same as ToZero
                            panic!("unreachable")
                        } else {
                            // same as AwayZero
                            half_bit && qs_bit
                        },
                        RoundingMode::ToNegative => if !s {
                            // same as ToZero
                            panic!("unreachable")
                        } else {
                            // same as AwayZero
                            half_bit && qs_bit
                        },
                        // the result was exactly +/-MIN_NORM so we shouldn't be here
                        RoundingMode::ToZero => panic!("unreachable"),
                        // only if we were more than 1/2 of the way to +/- MIN_NORM
                        RoundingMode::AwayZero => half_bit && qs_bit,
                        // the result was exactly +/-MIN_NORM so we shouldn't be here
                        RoundingMode::ToOdd => panic!("unreachable"),
                    }
                } else {
                    // larger then MIN_NORM
                    false
                }
            }
        };

        // The inexact flag is just if either of the rounding bits are high
        let inexact = half_bit || quarter_bit || sticky_bit;

        // Some sanity checking
        assert_eq!(
            m.len(),
            Self::PREC,
            "unexpected mantissa width after rounding: {}, expected {}",
            m.len(),
            Self::PREC
        );
        assert!(
            (exp >= Self::EMIN - 1) && (exp <= Self::EMAX),
            "unexpected exponent after rounding: {} [{}, {}]",
            exp,
            Self::EMIN,
            Self::EMAX
        );

        Self {
            num: FloatNum::Number(s, exp, m),
            flags: Exceptions {
                invalid: false,
                div_by_zero: false,
                overflow: false,
                underflow: underflow && inexact,
                inexact,
                carry: increment,
            },
        }
    }
}

// Rounding (casts)
impl<const E: usize, const N: usize> Float<E, N> {
    /// Multiplies this `Float` with another rounding it to the format
    /// specified by `Float<E3, N3>` and rounding mode `rm`.
    pub fn mul<const E2: usize, const N2: usize, const E3: usize, const N3: usize>(
        &self,
        other: &Float<E2, N2>,
        rm: RoundingMode,
    ) -> Float<E3, N3> {
        if self.is_nan() {
            // `self` is NaN
            self.round(rm)
        } else if other.is_nan() {
            // `other` is NaN
            other.round(rm)
        } else if self.is_infinity() {
            // `self` is +/- infinity
            let sign = self.sign() != other.sign();
            if other.is_zero() {
                // `other` is +/- 0 => invalid
                let payload = bitvec![0; Float::<E3, N3>::NAN_PAYLOAD_SIZE];
                let mut r = Float::<E3, N3>::nan(sign, true, payload);
                r.flags.invalid = true;
                r
            } else {
                // `other` is either finite or +/- infinity
                Float::<E3, N3>::infinity(sign)
            }
        } else if other.is_infinity() {
            // `other` is +/- infinity, `self` is either finite or +/- infinity
            let sign = self.sign() != other.sign();
            Float::<E3, N3>::infinity(sign)
        } else {
            // `self` and `other` are both finite
            let (s1, exp1, c1) = match &self.num {
                FloatNum::Number(s, exp, c) => (*s, *exp, c),
                _ => panic!("called on a non-finite float"),
            };

            let (s2, exp2, c2) = match &other.num {
                FloatNum::Number(s, exp, c) => (*s, *exp, c),
                _ => panic!("called on a non-finite float"),
            };

            let u1 = bitvec_to_biguint(c1.clone());
            let u2 = bitvec_to_biguint(c2.clone());

            let s = s1 != s2;
            let exp = exp1 + exp2;
            let c = biguint_to_bitvec(u1 * u2, c1.len() + c2.len());
            Float::<E3, N3>::round_finite(s, exp, c, rm)
        }
    }
}

// Implementing `Default` for `Float`
impl<const E: usize, const N: usize> Default for Float<E, N> {
    fn default() -> Self {
        Self::new()
    }
}

// Implementing `From<Bitvec>` for `Float`
impl<const E: usize, const N: usize> From<BitVec> for Float<E, N> {
    fn from(bv: BitVec) -> Self {
        assert_valid_format!(E, N);
        assert_eq!(
            bv.len(),
            N,
            "expected a BitVec of length {}, received {}",
            N,
            bv.len()
        );

        // split fields
        let (s, e, mut m) = Self::split_packed(&bv);
        let exp = bitvec_to_biguint(e).to_i64().unwrap() - Self::bias() - Self::M as i64;

        // branch on exponent
        if exp > Self::EMAX {
            if m.not_any() {
                // infinity
                Self::infinity(s)
            } else {
                // NaN
                Self::nan(s, m[N - E - 2], &m[..N - E - 2])
            }
        } else if exp < Self::EMIN {
            // subnormal or zero
            if m.not_any() {
                // zero
                Self::zero(s)
            } else {
                // subnormal
                m.push(false);
                assert_eq!(m.len(), Self::PREC);
                Self {
                    num: FloatNum::Number(s, exp, m),
                    flags: Exceptions::default(),
                }
            }
        } else {
            // normal
            m.push(true);
            assert_eq!(m.len(), Self::PREC);
            Self {
                num: FloatNum::Number(s, exp, m),
                flags: Exceptions::default(),
            }
        }
    }
}

// Implementing `From<f64>` for `Float<11, 64>
impl From<f64> for Float<11, 64> {
    fn from(f: f64) -> Self {
        let mut bv = bitvec![0; 64];
        let b = f.to_bits();
        bv.store(b);
        Self::from(bv)
    }
}

// Implementing `From<Float<E, N>>` for `f64`
impl<const E: usize, const N: usize> From<Float<E, N>> for BitVec {
    fn from(f: Float<E, N>) -> Self {
        match f.num {
            FloatNum::Number(s, exp, m) => {
                if exp == 0 && m.not_any() {
                    let m = bitvec![0; Float::<E, N>::M];
                    let e = bitvec![0; E];
                    Float::<E, N>::pack_components(s, e, m)
                } else if exp < Float::<E, N>::EMIN {
                    // subnormal
                    let m: BitVec = m[..N - E - 1].into(); // remove leading 0
                    let e = bitvec![0; E];
                    Float::<E, N>::pack_components(s, e, m)
                } else {
                    // normal
                    let mut exponent = exp + Float::<E, N>::bias();
                    let m: BitVec = m[..N - E - 1].into(); // remove leading 1
                    let mut e = bitvec![0; E];
                    for i in 0..E {
                        e.set(i, (exponent % 2) != 0);
                        exponent >>= 1;
                    }

                    Float::<E, N>::pack_components(s, e, m)
                }
            }
            FloatNum::Infinity(s) => {
                let m = bitvec![0; Float::<E, N>::M];
                let e = bitvec![1; E];
                Float::<E, N>::pack_components(s, e, m)
            }
            FloatNum::Nan(s, signal, payload) => {
                let mut m = payload;
                let e = bitvec![1; E];
                m.push(signal); // mantissa = signal | payload
                Float::<E, N>::pack_components(s, e, m)
            }
        }
    }
}

// Implementing `From<Float<11, 64>>` for `f64`
impl From<Float<11, 64>> for f64 {
    fn from(f: Float<11, 64>) -> Self {
        let bv: BitVec = f.into();
        f64::from_bits(bv[..64].load())
    }
}

/// Alias for `Float<15, 128>` (quad-precision number)
pub type Quad = Float<15, 128>;
/// Alias for `Float<11, 64>` (double-precision number)
pub type Double = Float<11, 64>;
/// Alias for `Float<8, 32>` (single-precision number)
pub type Single = Float<8, 32>;
/// Alias for `Float<5, 16>` (half-precision number)
pub type Half = Float<5, 16>;
