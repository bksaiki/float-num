/*
    Rounding
*/

use std::cmp::Ordering;
use std::ops::AddAssign;

use super::*;

macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
}

impl RoundingMode {
    /// Translates a `RoundingMode` and sign bit to a `RoundingDirection`
    /// and a boolean indicating if the direction only specifies tie-breaking behavior.
    pub fn direction(&self, sign: bool) -> (bool, RoundingDirection) {
        match (self, sign) {
            (RoundingMode::NearestEven, _) => (true, RoundingDirection::ToEven),
            (RoundingMode::NearestAway, _) => (true, RoundingDirection::AwayZero),
            (RoundingMode::ToPositive, false) => (false, RoundingDirection::AwayZero),
            (RoundingMode::ToPositive, true) => (false, RoundingDirection::ToZero),
            (RoundingMode::ToNegative, false) => (false, RoundingDirection::ToZero),
            (RoundingMode::ToNegative, true) => (false, RoundingDirection::AwayZero),
            (RoundingMode::ToZero, _) => (false, RoundingDirection::ToZero),
            (RoundingMode::AwayZero, _) => (false, RoundingDirection::AwayZero),
            (RoundingMode::ToOdd, _) => (false, RoundingDirection::ToOdd),
        }
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
    pub(crate) fn round_finite<const E2: usize, const N2: usize>(
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
                        sticky_bit = low[..low_len - 2].any();
                    }

                    exp += diff as i64;
                }
            }

            // adjust if the exponent is too small
            // TODO: this is dumb
            if exp < Float::<E2, N2>::EXPMIN {
                while exp < Float::<E2, N2>::EXPMIN - 1 {
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
        match rm.direction(sign) {
            (true, RoundingDirection::ToEven) => {
                // no half bit => truncate
                // half bit and sticky bit => increment
                // tie => increment if lsb since we want it to be 0
                half_bit && (sticky_bit || lsb)
            }
            (true, RoundingDirection::AwayZero) => {
                // no half bit => truncate
                // half bit => increment (tie requires increment)
                half_bit
            }
            (true, RoundingDirection::ToZero) => {
                // (unused)
                // tie => truncate
                half_bit && sticky_bit
            }
            (true, RoundingDirection::ToOdd) => {
                // (unused)
                // tie => increment if even
                half_bit && !lsb
            }
            (false, RoundingDirection::AwayZero) => {
                // increment if not exact
                half_bit || sticky_bit
            }
            (false, RoundingDirection::ToZero) => {
                // always truncate
                false
            }
            (false, RoundingDirection::ToOdd) => {
                // LSB of the mantissa needs to be 1
                !lsb
            }
            (false, RoundingDirection::ToEven) => {
                // (unused)
                // LSB of the mantissa needs to be 0
                lsb
            }
        }
    }

    // Assuming overflow has occured, return true if
    // the result should be rounded to +/- infinity
    // (rather than +/- MAX_FLOAT).
    fn overflow_to_infinity(sign: bool, rm: RoundingMode) -> bool {
        match rm.direction(sign) {
            // nearest carries all overflows to infinity
            (true, _) => true,
            // nearest carries all overflows to infinity
            (_, RoundingDirection::AwayZero) => true,
            // carry all overflows to MAX_FLOAT
            (_, RoundingDirection::ToZero) => false,
            // MAX_FLOAT has an odd lsb
            (_, RoundingDirection::ToEven) => true,
            // MAX_FLOAT has an odd lsb
            (_, RoundingDirection::ToOdd) => false,
        }
    }

    // Constructs a new `Float` based on rounding information.
    // Requires a sign, mantissa, exponent, half bit, and sticky bit
    // The inputs must encode a non-zero, finite number.
    fn round_finalize(
        s: bool,
        mut exp: i64,
        mut c: BitVec,
        half_bit: bool,
        quarter_bit: bool,
        sticky_bit: bool,
        rm: RoundingMode,
    ) -> Self {
        // First, we check if we need to round away from zero.
        // We use the sign, rounding mode, LSB of the mantissa, and the two rounding bits.
        let qs_bit = quarter_bit || sticky_bit;
        let increment = Self::round_requires_increment(s, c[0], half_bit, qs_bit, rm);
        if increment {
            // increment the mantissa
            // possibly need to adjust exponent (the exponent is unbounded)
            let mut i = bitvec_to_biguint(c);
            i.add_assign(1_u8);
            let c_ext = biguint_to_bitvec(i, Self::PREC + 1);
            let carry = c_ext[Self::PREC];

            c = c_ext[0..Self::PREC].into();
            if carry {
                c.set(Self::PREC - 1, true);
                exp += 1;
            }
        }

        // Next, we check if overflow occured and alter the result if it has.
        if exp > Self::EXPMAX {
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
                    num: FloatNum::Number(s, Self::EXPMAX, bitvec![1; Self::PREC]),
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
                if increment && c[..Self::M].not_any() {
                    match rm.direction(s) {
                        // only if we were exactly 3/4 of the way to +/-MIN_NORM
                        (true, _) => half_bit && quarter_bit && !sticky_bit,
                        // the result was exactly +/-MIN_NORM so we shouldn't be here
                        (_, RoundingDirection::ToZero) => panic!("unreachable"),
                        // only if we were more than 1/2 of the way to +/- MIN_NORM
                        (_, RoundingDirection::AwayZero) => half_bit && qs_bit,
                        // only if we were more than 1/2 of the way to +/- MIN_NORM
                        (_, RoundingDirection::ToEven) => half_bit && qs_bit,
                        // the result was exactly +/-MIN_NORM so we shouldn't be here
                        (_, RoundingDirection::ToOdd) => panic!("unreachable"),
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
            c.len(),
            Self::PREC,
            "unexpected mantissa width after rounding: {}, expected {}",
            c.len(),
            Self::PREC
        );
        assert!(
            (exp >= Self::EXPMIN - 1) && (exp <= Self::EXPMAX),
            "unexpected exponent after rounding: {} [{}, {}]",
            exp,
            Self::EXPMIN,
            Self::EXPMAX
        );

        Self {
            num: FloatNum::Number(s, exp, c),
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
