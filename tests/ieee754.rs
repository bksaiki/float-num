use bitvec::prelude::Lsb0;
use float_sim::ieee754::*;
use float_sim::ops::*;
use float_sim::Number;

use gmp_mpfr_sys::mpfr;

type BitVec = bitvec::prelude::BitVec<u32, Lsb0>;

macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
}

fn rm_to_mpfr(rm: RoundingMode) -> mpfr::rnd_t {
    match rm {
        RoundingMode::NearestEven => mpfr::rnd_t::RNDN,
        RoundingMode::NearestAway => panic!("MPFR does not support RoundingMode::NearestAway"),
        RoundingMode::ToPositive => mpfr::rnd_t::RNDU,
        RoundingMode::ToNegative => mpfr::rnd_t::RNDD,
        RoundingMode::ToZero => mpfr::rnd_t::RNDZ,
        RoundingMode::AwayZero => mpfr::rnd_t::RNDA,
        RoundingMode::ToOdd => panic!("MPFR does not support RoundingMode::ToOdd"),
    }
}

fn mpfr_mul(
    a: &rug::Float,
    b: &rug::Float,
    ewidth: usize,
    prec: usize,
    rm: RoundingMode,
) -> (rug::Float, bool, bool, bool, bool, bool) {
    let mut r = rug::Float::new(prec as u32);

    let mpfr_emax = usize::pow(2, ewidth as u32 - 1) as i64;
    let mpfr_emin = 4 - (mpfr_emax + prec as i64);

    let (invalid, div_by_zero, overflow, underflow, inexact) = unsafe {
        let a_mpfr = a.as_raw();
        let b_mpfr = b.as_raw();
        let r_mpfr = r.as_raw_mut();
        let rnd = rm_to_mpfr(rm);

        let emin = mpfr::get_emin();
        let emax = mpfr::get_emax();
        mpfr::set_emin(mpfr_emin);
        mpfr::set_emax(mpfr_emax);
        mpfr::clear_flags();

        let t = mpfr::mul(r_mpfr, a_mpfr, b_mpfr, rnd);
        mpfr::subnormalize(r_mpfr, t, rnd);

        let invalid = mpfr::nanflag_p() != 0;
        let div_by_zero = mpfr::divby0_p() != 0;
        let overflow = mpfr::overflow_p() != 0;
        let inexact = mpfr::inexflag_p() != 0;
        let underflow = inexact && mpfr::underflow_p() != 0;

        mpfr::set_emin(emin);
        mpfr::set_emax(emax);

        (invalid, div_by_zero, overflow, underflow, inexact)
    };

    (r, invalid, div_by_zero, overflow, underflow, inexact)
}

#[test]
fn parameters() {
    assert_eq!(Quad::E, 15);
    assert_eq!(Quad::N, 128);
    assert_eq!(Quad::B, 2);
    assert_eq!(Quad::PREC, 113);
    assert_eq!(Quad::EMAX, 16383);
    assert_eq!(Quad::EMIN, -16382);

    assert_eq!(Double::E, 11);
    assert_eq!(Double::N, 64);
    assert_eq!(Double::B, 2);
    assert_eq!(Double::PREC, 53);
    assert_eq!(Double::EMAX, 1023);
    assert_eq!(Double::EMIN, -1022);
    assert_eq!(Double::EXPMAX, 971);
    assert_eq!(Double::EXPMIN, -1074);

    assert_eq!(Single::E, 8);
    assert_eq!(Single::N, 32);
    assert_eq!(Single::B, 2);
    assert_eq!(Single::PREC, 24);
    assert_eq!(Single::EMAX, 127);
    assert_eq!(Single::EMIN, -126);

    assert_eq!(Half::E, 5);
    assert_eq!(Half::N, 16);
    assert_eq!(Half::B, 2);
    assert_eq!(Half::PREC, 11);
    assert_eq!(Half::EMAX, 15);
    assert_eq!(Half::EMIN, -14);
}

#[test]
fn from_f64() {
    let fp = 1.0;
    let bv = Double::from(fp);
    assert!(
        !bv.is_infinity() && !bv.is_nan(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert_eq!(
        bv.exponent().unwrap(),
        -52,
        "conversion from f64 failed (exponent): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap()[52],
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap()[..52].not_any(),
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );

    let fp = -1.0;
    let bv = Double::from(fp);
    assert!(
        !bv.is_infinity() && !bv.is_nan(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert_eq!(
        bv.exponent().unwrap(),
        -52,
        "conversion from f64 failed (exponent): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap()[52],
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap()[..52].not_any(),
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );

    let fp = 0.0;
    let bv = Double::from(fp);
    assert!(
        !bv.is_infinity() && !bv.is_nan(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert_eq!(
        bv.exponent().unwrap(),
        0,
        "conversion from f64 failed (exponent): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap().not_any(),
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );

    let fp = -0.0;
    let bv = Double::from(fp);
    assert!(
        !bv.is_infinity() && !bv.is_nan(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert_eq!(
        bv.exponent().unwrap(),
        0,
        "conversion from f64 failed (exponent): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap().not_any(),
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );

    let fp = f64::MIN_POSITIVE;
    let bv = Double::from(fp);
    assert!(
        !bv.is_infinity() && !bv.is_nan(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert_eq!(
        bv.exponent().unwrap(),
        -1074,
        "conversion from f64 failed (exponent): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap()[..52].not_any(),
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );

    let fp = f64::from_bits(0xF_FFFF_FFFF_FFFF);
    let bv = Double::from(fp);
    assert!(
        !bv.is_infinity() && !bv.is_nan(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert_eq!(
        bv.exponent().unwrap(),
        -1074,
        "conversion from f64 failed (exponent): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap()[1..52].all(),
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );

    let fp = f64::from_bits(0x1);
    let bv = Double::from(fp);
    assert!(
        !bv.is_infinity() && !bv.is_nan(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert_eq!(
        bv.exponent().unwrap(),
        -1074,
        "conversion from f64 failed (exponent): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap()[1..52].not_any(),
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );

    let fp = f64::MAX;
    let bv = Double::from(fp);
    assert!(
        !bv.is_infinity() && !bv.is_nan(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert_eq!(
        bv.exponent().unwrap(),
        971,
        "conversion from f64 failed (exponent): {:.20e}",
        fp
    );
    assert!(
        bv.significand().unwrap().all(),
        "conversion from f64 failed (mantissa): {:.20e}",
        fp
    );

    let fp = f64::INFINITY;
    let bv = Double::from(fp);
    assert!(
        bv.is_infinity(),
        "conversion from f64 failed (class): {:.20e}",
        fp
    );
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);

    let fp = f64::NEG_INFINITY;
    let bv = Double::from(fp);
    assert!(
        bv.is_infinity(),
        "conversion from f64 failed (class): {}",
        fp
    );
    assert!(bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);

    // Signaling NaN with no payload
    let fp = f64::from_bits((0x7FF << 52) | (1 << 51));
    let bv = Double::from(fp);
    assert!(bv.is_nan(), "conversion from f64 failed (class): {}", fp);
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert!(
        bv.is_signaling_nan().unwrap(),
        "conversion from f64 failed (signalling): {:.20e}",
        fp
    );
    assert!(
        bv.nan_payload().unwrap().not_any(),
        "conversion from f64 failed (signalling): {:.20e}",
        fp
    );

    // Quiet NaN with payload of 0x1
    let fp = f64::from_bits((0x7FF << 52) | 0x1);
    let bv = Double::from(fp);
    assert!(bv.is_nan(), "conversion from f64 failed (class): {}", fp);
    assert!(!bv.sign(), "conversion from f64 failed (sign): {:.20e}", fp);
    assert!(
        !bv.is_signaling_nan().unwrap(),
        "conversion from f64 failed (signalling): {:.20e}",
        fp
    );
    assert!(
        bv.nan_payload().unwrap()[1..51].not_any(),
        "conversion from f64 failed (signalling): {:.20e}",
        fp
    );
}

#[test]
fn to_f64() {
    let fps = [
        1.0,
        -1.0,
        0.0,
        -0.0,
        f64::MIN_POSITIVE,
        f64::from_bits(0xF_FFFF_FFFF_FFFF),
        f64::from_bits(0x1),
        -f64::from_bits(0x1),
        f64::MAX,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::from_bits((0x7FF << 52) | (1 << 51)),
        f64::from_bits((0x7FF << 52) | 0x1),
    ];

    for fp in fps {
        let fp2: f64 = Double::from(fp).into();
        if f64::is_nan(fp) {
            assert!(
                f64::is_nan(fp2),
                "conversion to f64 failed: {} != {}",
                fp,
                fp2
            );
        } else {
            assert_eq!(fp, fp2, "conversion to f64 failed: {} != {}", fp, fp2);
        }
    }
}

#[test]
fn classify() {
    let flag_names = [
        "is_nan",
        "is_infinity",
        "is_zero",
        "is_normal",
        "is_subnormal",
    ];
    let tests = [
        (
            Double::nan(false, false, bitvec![0; Double::NAN_PAYLOAD_SIZE]),
            "nan",
            0,
        ),
        (Double::infinity(false), "infinity", 1),
        (Double::zero(false), "zero", 2),
        (Double::from(1.0), "normal", 3),
        (Double::from(1e-310), "subnormal", 4),
    ];

    for (fp, name, idx) in tests {
        let flags = [
            fp.is_nan(),
            fp.is_infinity(),
            fp.is_zero(),
            fp.is_normal(),
            fp.is_subnormal(),
        ];
        for (i, f) in flags.iter().enumerate() {
            if i == idx {
                assert!(*f, "classify failed ({}, {})", name, flag_names[i]);
            } else {
                assert!(!*f, "classify failed ({}, {})", name, flag_names[i]);
            }
        }
    }
}

#[test]
fn conversions_2_4() {
    const E: usize = 2;
    const N: usize = 4;
    type F = Float<E, N>;
    for i in 0..u32::pow(2, N as u32) {
        let mut bv = BitVec::from_element(i);
        bv.resize(N, false);
        let f = F::from(bv.clone());
        let bv2 = BitVec::from(f);
        assert_eq!(bv, bv2, "bv->fp->bv conversion failed: {} != {}", bv, bv2);
    }
}

#[test]
fn conversions_3_6() {
    const E: usize = 3;
    const N: usize = 6;
    type F = Float<E, N>;
    for i in 0..u32::pow(2, N as u32) {
        let mut bv = BitVec::from_element(i);
        bv.resize(N, false);
        let f = F::from(bv.clone());
        let bv2 = BitVec::from(f);
        assert_eq!(bv, bv2, "bv->fp->bv conversion failed: {} != {}", bv, bv2);
    }
}

#[test]
fn conversions_4_8() {
    const E: usize = 4;
    const N: usize = 8;
    type F = Float<E, N>;
    for i in 0..u32::pow(2, N as u32) {
        let mut bv = BitVec::from_element(i);
        bv.resize(N, false);
        let f = F::from(bv.clone());
        let bv2 = BitVec::from(f);
        assert_eq!(bv, bv2, "bv->fp->bv conversion failed: {} != {}", bv, bv2);
    }
}

#[test]
fn conversions_8_12() {
    const E: usize = 8;
    const N: usize = 12;
    type F = Float<E, N>;
    for i in 0..u32::pow(2, N as u32) {
        let mut bv = BitVec::from_element(i);
        bv.resize(N, false);
        let f = F::from(bv.clone());
        let bv2 = BitVec::from(f);
        assert_eq!(bv, bv2, "bv->fp->bv conversion failed: {} != {}", bv, bv2);
    }
}

#[test]
fn conversions_8_16() {
    const E: usize = 8;
    const N: usize = 16;
    type F = Float<E, N>;
    for i in 0..u32::pow(2, N as u32) {
        let mut bv = BitVec::from_element(i);
        bv.resize(N, false);
        let f = F::from(bv.clone());
        let bv2 = BitVec::from(f);
        assert_eq!(bv, bv2, "bv->fp->bv conversion failed: {} != {}", bv, bv2);
    }
}

#[test]
fn round_trivial() {
    let fps = [
        0.0,
        -0.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::from_bits((0x7FF << 52) | (1 << 51)),
        f64::from_bits((0x7FF << 52) | 0x1),
    ];

    let ctx = IEEEContext::default();
    for fp in fps {
        let fp = Double::from(fp);
        let fp128: Quad = fp.round(&ctx);
        let fp2: Double = fp128.round(&ctx);

        let bv: BitVec = fp.into();
        let bv2: BitVec = fp2.into();
        assert_eq!(bv, bv2, "fp->fp->fp conversion failed: {} != {}", bv, bv2);
    }
}

macro_rules! test_mul {
    ( $E1:expr, $N1:expr, $E2:expr, $N2:expr, $E3:expr, $N3:expr ) => {
        type F1 = Float<$E1, $N1>;
        type F2 = Float<$E2, $N2>;
        type F3 = Float<$E3, $N3>;

        let mut success: bool = true;
        let mut bad: Vec<(
            (f64, f64),
            (f64, bool, bool, bool, bool, bool),
            (f64, bool, bool, bool, bool, bool),
        )> = vec![];
        let rms = &[
            RoundingMode::NearestEven,
            // RoundingMode::ToPositive,
            // RoundingMode::ToNegative,
            // RoundingMode::ToZero,
            // RoundingMode::AwayZero,
        ];

        for rm in rms {
            let ctx = IEEEContext::default().rounding_mode(*rm);
            for i in 0..u32::pow(2, F1::N as u32) {
                let mut xv = BitVec::from_element(i);
                xv.resize(F1::N, false);
                let x = F1::from(xv.clone());
                let xf = rug::Float::with_val(53, f64::from(x.clone()));

                for j in 0..u32::pow(2, F2::N as u32) {
                    let mut yv = BitVec::from_element(j);
                    yv.resize(F2::N, false);
                    let y = F2::from(yv.clone());
                    let yf = rug::Float::with_val(53, f64::from(y.clone()));

                    let z: F3 = x.mul(&y, &ctx);
                    let zv = f64::from(z.clone());
                    let (zf, iv, dz, of, uf, ie) = mpfr_mul(&xf, &yf, F3::E, F3::PREC, *rm);

                    if match (zv.is_nan(), zf.to_f64().is_nan()) {
                        (true, true) => false,
                        (true, false) => true,
                        (false, true) => true,
                        (false, false) => zv != zf.to_f64(),
                    } {
                        success = false;
                        bad.push((
                            (xf.to_f64(), yf.to_f64()),
                            (zf.to_f64(), iv, dz, of, uf, ie),
                            (
                                zf.to_f64(),
                                z.invalid_flag(),
                                z.div_by_zero_flag(),
                                z.overflow_flag(),
                                z.underflow_flag(),
                                z.inexact_flag(),
                            ),
                        ));
                    }

                    if z.invalid_flag() != iv
                        || z.div_by_zero_flag() != dz
                        || z.overflow_flag() != of
                        || z.underflow_flag() != uf
                        || z.inexact_flag() != ie
                    {
                        success = false;
                        bad.push((
                            (xf.to_f64(), yf.to_f64()),
                            (zf.to_f64(), iv, dz, of, uf, ie),
                            (
                                zf.to_f64(),
                                z.invalid_flag(),
                                z.div_by_zero_flag(),
                                z.overflow_flag(),
                                z.underflow_flag(),
                                z.inexact_flag(),
                            ),
                        ));
                    }
                }
            }
        }

        assert!(
            success,
            "multiplication tests failed: {}",
            bad.iter()
                .map(
                    |((x, y), (z0, iv0, dz0, of0, uf0, ie0), (z1, iv1, dz1, of1, uf1, ie1))| {
                        format!(
                            "{} * {} => Exp: {} [{} {} {} {} {}] Act: {} [{} {} {} {} {}]",
                            x, y, z0, iv0, dz0, of0, uf0, ie0, z1, iv1, dz1, of1, uf1, ie1
                        )
                    }
                )
                .collect::<Vec<String>>()
                .join("\n")
        );
    };
}

#[test]
fn test_mul_2_4_2_4_2_4() {
    test_mul!(2, 4, 2, 4, 2, 4);
}

#[test]
fn test_mul_3_6_3_6_3_6() {
    test_mul!(3, 6, 3, 6, 3, 6);
}

#[test]
fn test_mul_4_8_4_8_4_8() {
    test_mul!(4, 8, 4, 8, 4, 8);
}

#[test]
fn sandbox() {
    let ctx = IEEEContext::default();
    let a = Float::<3, 6>::from(2.5);
    let b = Float::<3, 6>::from(2.5);
    let c: Float<3, 6> = a.mul(&b, &ctx);

    println!(
        "{} * {} = {}",
        BitVec::from(a.clone()),
        BitVec::from(b.clone()),
        BitVec::from(c.clone())
    );
    println!("{} * {} = {}", f64::from(a), f64::from(b), f64::from(c));
}
