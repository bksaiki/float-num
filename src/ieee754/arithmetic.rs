/*
    Arithmetic
*/

use super::*;

macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
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
