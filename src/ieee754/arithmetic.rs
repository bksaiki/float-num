/*
    Arithmetic
*/

use crate::{bitvec, ieee754::*, ops::*};

// Rounding (casts)
impl<const E: usize, const N: usize> Float<E, N> {
    // Decomposes a non-zero finite numbers into the triple (s, e, c)
    // where `s` is the sign bit, `e` is the exponent, and `c` is
    // the mantissa of an integer.
    fn decompose_nonzero_finite(&self) -> (bool, i64, &BitVec) {
        match &self.num {
            FloatNum::Subnormal(s, c) => (*s, Self::EXPMIN, c),
            FloatNum::Normal(s, exp, c) => (*s, *exp, c),
            _ => panic!("called on a non-finite float"),
        }
    }

    /// Negates this `Float` without rounding.
    /// Since this representation is symmetric around 0,
    /// we just negate the sign bit.
    pub fn neg_exact(&self) -> Self {
        let num = match &self.num {
            FloatNum::Zero(s) => FloatNum::Zero(!s),
            FloatNum::Subnormal(s, c) => FloatNum::Subnormal(*s, c.clone()),
            FloatNum::Normal(s, e, c) => FloatNum::Normal(!s, *e, c.clone()),
            FloatNum::Infinity(s) => FloatNum::Infinity(!s),
            FloatNum::Nan(s, signal, payload) => FloatNum::Nan(!s, *signal, payload.clone()),
        };

        Self {
            num,
            flags: self.flags,
        }
    }

    /// Takes the absolute value of this `Float` without rounding.
    /// Since this representation is symmetric around 0,
    /// we just set the sign bit to 0.
    pub fn abs_exact(&self) -> Self {
        let num = match &self.num {
            FloatNum::Zero(_) => FloatNum::Zero(false),
            FloatNum::Subnormal(_, c) => FloatNum::Subnormal(false, c.clone()),
            FloatNum::Normal(_, e, c) => FloatNum::Normal(false, *e, c.clone()),
            FloatNum::Infinity(_) => FloatNum::Infinity(false),
            FloatNum::Nan(_, signal, payload) => FloatNum::Nan(false, *signal, payload.clone()),
        };

        Self {
            num,
            flags: self.flags,
        }
    }

    /// Negates this `Float` rounding the result according to the rounding context.
    pub fn neg<const E2: usize, const N2: usize>(&self, ctx: &IEEEContext) -> Float<E2, N2> {
        self.neg_exact().round(ctx)
    }

    /// Returns the absolute value of this `Float`,
    /// rounding the result according to the rounding context.
    pub fn abs<const E2: usize, const N2: usize>(&self, ctx: &IEEEContext) -> Float<E2, N2> {
        self.abs_exact().round(ctx)
    }

    /// Adds this `Float` with another, rounding the result to the format
    /// specified by `Float<E3, N3>` and rounding mode `rm`.
    pub fn add<const E2: usize, const N2: usize, const E3: usize, const N3: usize>(
        &self,
        other: &Float<E2, N2>,
        ctx: &IEEEContext,
    ) -> Float<E3, N3> {
        if self.is_nan() {
            // `self` is NaN
            let mut r = self.round(ctx);
            r.flags.invalid = true;
            r
        } else if other.is_nan() {
            // `other` is NaN
            let mut r = other.round(ctx);
            r.flags.invalid = true;
            r
        } else if self.is_infinity() {
            // `self` is +/- infinity
            if other.is_infinity() && self.sign() != other.sign() {
                // `other` is -/+ infinity => invalid (negative)
                let payload = bitvec![0; Float::<E3, N3>::NAN_PAYLOAD_SIZE];
                let mut r = Float::<E3, N3>::nan(true, true, payload);
                r.flags.invalid = true;
                r
            } else {
                // `other` is either finite or +/- infinity
                Float::<E3, N3>::infinity(self.sign())
            }
        } else if other.is_infinity() {
            // `other` is +/- infinity, `self` is either finite or +/- infinity
            let sign = self.sign() != other.sign();
            if self.is_infinity() && self.sign() != other.sign() {
                // `self` is -/+ infinity => invalid
                let payload = bitvec![0; Float::<E3, N3>::NAN_PAYLOAD_SIZE];
                let mut r = Float::<E3, N3>::nan(true, true, payload);
                r.flags.invalid = true;
                r
            } else {
                Float::<E3, N3>::infinity(sign)
            }
        } else if self.is_zero() {
            // `self` is +/- 0
            if other.is_zero() {
                // `other` is +/- 0
                // the result is negative only if both arguments are negative
                Float::<E3, N3>::zero(self.sign() && other.sign())
            } else {
                // the unrounded result is `other`
                other.round(ctx)
            }
        } else if other.is_zero() {
            // `other` is +/- 0 and `self` is non-zero finite
            self.round(ctx)
        } else {
            // `self` and `other` are both finite
            // let (s1, exp1, c1) = self.decompose_nonzero_finite();
            // let (s2, exp2, c2) = other.decompose_nonzero_finite();

            todo!()
        }
    }

    /// Subtracts this `Float` with another, rounding the result to the format
    /// specified by `Float<E3, N3>` and rounding mode `rm`.
    pub fn sub<const E2: usize, const N2: usize, const E3: usize, const N3: usize>(
        &self,
        other: &Float<E2, N2>,
        ctx: &IEEEContext,
    ) -> Float<E3, N3> {
        self.add(&other.neg_exact(), ctx)
    }

    /// Multiplies this `Float` with another, rounding the result to the format
    /// specified by `Float<E3, N3>` and rounding mode `rm`.
    pub fn mul<const E2: usize, const N2: usize, const E3: usize, const N3: usize>(
        &self,
        other: &Float<E2, N2>,
        ctx: &IEEEContext,
    ) -> Float<E3, N3> {
        if self.is_nan() {
            // `self` is NaN
            let mut r = self.round(ctx);
            r.flags.invalid = true;
            r
        } else if other.is_nan() {
            // `other` is NaN
            let mut r = other.round(ctx);
            r.flags.invalid = true;
            r
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
            if self.is_zero() {
                // `self` is +/- 0 => invalid
                let payload = bitvec![0; Float::<E3, N3>::NAN_PAYLOAD_SIZE];
                let mut r = Float::<E3, N3>::nan(sign, true, payload);
                r.flags.invalid = true;
                r
            } else {
                Float::<E3, N3>::infinity(sign)
            }
        } else if self.is_zero() || other.is_zero() {
            // either `self` or `other` is +/- 0
            let sign = self.sign() != other.sign();
            Float::<E3, N3>::zero(sign)
        } else {
            // `self` and `other` are both finite
            let (s1, exp1, c1) = self.decompose_nonzero_finite();
            let (s2, exp2, c2) = other.decompose_nonzero_finite();
            let c_len = c1.len() + c2.len();

            let u1 = bitvec_to_biguint(c1);
            let u2 = bitvec_to_biguint(c2);

            let s = s1 != s2;
            let exp = exp1 + exp2;
            let c = biguint_to_bitvec(u1 * u2, c_len);
            Float::<E3, N3>::round_finite(s, exp, c, ctx)
        }
    }
}
