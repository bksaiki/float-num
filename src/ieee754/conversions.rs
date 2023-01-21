/*
    Conversions to and from `Float<E, N>`
*/

use bitvec::field::BitField;
use num_traits::cast::ToPrimitive;

use super::*;

macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
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
        let mut exp = bitvec_to_biguint(e).to_i64().unwrap() - Self::BIAS;

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
                exp -= Self::M as i64;
                assert_eq!(m.len(), Self::PREC);
                Self {
                    num: FloatNum::Number(s, exp, m),
                    flags: Exceptions::default(),
                }
            }
        } else {
            // normal
            m.push(true);
            exp -= Self::M as i64;
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
                } else if exp < Float::<E, N>::EXPMIN {
                    // subnormal
                    let m: BitVec = m[..N - E - 1].into(); // remove leading 0
                    let e = bitvec![0; E];
                    Float::<E, N>::pack_components(s, e, m)
                } else {
                    // normal
                    let mut exponent = exp + Float::<E, N>::BIAS + Float::<E, N>::M as i64;
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
