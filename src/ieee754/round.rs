/*
    Rounding
*/

use std::convert::Infallible;
use std::ops::AddAssign;

use crate::{ieee754::*, ops::*, Context};

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

// Implementing IEEEContext
impl IEEEContext {
    /// Creates a new rounding context for `Float`s
    /// with `rm` set to `RoundingMode::NearestEven`
    /// and `ftz` set to false.
    pub fn new() -> Self {
        Self {
            rm: RoundingMode::NearestEven,
            ftz: false,
        }
    }

    /// Sets the rounding mode.
    pub fn rounding_mode(mut self, rm: RoundingMode) -> Self {
        self.rm = rm;
        self
    }

    /// Sets the flush-to-zero option.
    pub fn flush_subnormals(mut self, ftz: bool) -> Self {
        self.ftz = ftz;
        self
    }
}

impl Context for IEEEContext {}

impl Default for IEEEContext {
    fn default() -> Self {
        Self::new()
    }
}

// Rounding utilities
impl<const E: usize, const N: usize> Float<E, N> {
    // Rounds a finite, non-zero number in the representation specified
    // by `Float<E2, N2>` using the rounding mode `rm`.
    pub(crate) fn round_finite<const E2: usize, const N2: usize>(
        s: bool,
        mut exp: i64,
        mut c: BitVec,
        ctx: &IEEEContext,
    ) -> Float<E2, N2> {
        if exp == 0 && c.not_any() {
            // The exceptional case: exact zero
            // Return zero, no exception flags are raised
            Float::<E2, N2>::zero(s)
        } else {
            // Drop leading zeros
            let mut prec = c.len();
            let lz = c.last_one().unwrap() + 1;
            if lz < prec {
                c = c[..lz].into();
                prec = lz;
            }

            // Construct a mantissa large enough to hold
            //  (a) input mantissa
            //  (b) output mantissa + 3 bits
            // and record the number of bits added
            let c_len = usize::max(prec, Float::<E2, N2>::PREC) + 3;
             if prec < c_len {
                let padding = c_len - prec;
                c.extend(bitvec![0; padding]);
                c.shift_right(padding);
                exp -= padding as i64;
            }

            // Construct the new mantissa with three rounding bits
            //  `half`: unrounded value is at least half way to the next representable float
            //  `quarter`: unrounded value is either 1/4 or 3/4 of the way
            //   to the next representable float (depending on `half`)
            //  `sticky`: unrounded value is slightly above 0, 1/4, 1/2, 3/4 of the way
            //   to the next representable float but below the next regime
            let diff = c_len - Float::<E2, N2>::PREC;
            let (low, high) = c.split_at(diff);
            let low_len = low.len();
            exp += diff as i64;

            // `c_new` - highest `Float::<E2, N2>::PREC` bits
            // `half_bit` - MSB of the low part
            // `quarter_bit` - next bit of the low part
            // `sticky_bit` - apply OR to the rest of the low part
            let mut c_new = BitVec::from(high);
            let mut half_bit = low[low_len - 1];
            let mut quarter_bit = low[low_len - 2];
            let mut sticky_bit = low[..low_len - 2].any();

            // adjust if the exponent is too small
            // TODO: this is dumb
            while exp < Float::<E2, N2>::EXPMIN {
                sticky_bit |= quarter_bit;
                quarter_bit = half_bit;
                half_bit = c_new[0];
                c_new.shift_left(1);
                exp += 1;
            }

            // finish the rounding process with all the rounding information
            Float::<E2, N2>::round_finalize(s, exp, c_new, half_bit, quarter_bit, sticky_bit, ctx)
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
        ctx: &IEEEContext,
    ) -> Self {
        // First, we check if we need to round away from zero.
        // We use the sign, rounding mode, LSB of the mantissa, and the two rounding bits.
        let qs_bit = quarter_bit || sticky_bit;
        let increment = Self::round_requires_increment(s, c[0], half_bit, qs_bit, ctx.rm);
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
            if Self::overflow_to_infinity(s, ctx.rm) {
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
                    num: FloatNum::Normal(s, Self::EXPMAX, bitvec![1; Self::PREC]),
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
        let underflow = if exp > Self::EXPMIN {
            // definitely larger than MIN_NORM
            false
        } else {
            if c[Self::M] {
                // leading 1 detected
                if increment && c[..Self::M].not_any() {
                    // exactly MIN_NORM: need to check a few things
                    match ctx.rm.direction(s) {
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
                    // definitely larger than MIN_NORM
                    false
                }
            } else {
                // definitely a subnormal result
                true
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
            (exp >= Self::EXPMIN) && (exp <= Self::EXPMAX),
            "unexpected exponent after rounding: {} [{}, {}]",
            exp,
            Self::EXPMIN,
            Self::EXPMAX
        );

        // construct the number
        let num = if underflow {
            if c.not_any() {
                FloatNum::Zero(s)
            } else {
                FloatNum::Subnormal(s, c)
            }
        } else {
            FloatNum::Normal(s, exp, c)
        };

        // set the exception flags
        let flags = Exceptions {
            invalid: false,
            div_by_zero: false,
            overflow: false,
            underflow: underflow && inexact,
            inexact,
            carry: increment,
        };

        Self { num, flags }
    }
}

// Implementing `Round<N>` for `Float`
impl<const E: usize, const N: usize, const E2: usize, const N2: usize> Round<Float<E2, N2>>
    for Float<E, N>
{
    type Error = Infallible;

    fn round(&self, ctx: &Self::Ctx) -> Float<E2, N2> {
        match &self.num {
            FloatNum::Zero(s) => Float::zero(*s),
            FloatNum::Subnormal(s, c) => Self::round_finite(*s, Self::EXPMIN, c.clone(), ctx),
            FloatNum::Normal(s, exp, c) => Self::round_finite(*s, *exp, c.clone(), ctx),
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

    fn round_exact(&self, ctx: &Self::Ctx) -> RoundResult<Float<E2, N2>> {
        let v = Self::round(self, ctx);
        if v.inexact_flag() {
            RoundResult::Inexact(v)
        } else {
            RoundResult::Exact(v)
        }
    }

    fn try_round(&self, ctx: &Self::Ctx) -> Result<RoundResult<Float<E2, N2>>, Self::Error> {
        Result::Ok(Self::round_exact(self, ctx))
    }
}
