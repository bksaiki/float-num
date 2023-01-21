use bitvec::prelude::Lsb0;
use float_sim::ieee754::*;

type BitVec = bitvec::prelude::BitVec<u32, Lsb0>;

macro_rules! bitvec {
    [ $($t:tt)* ] => {
        {
            bitvec::bitvec![u32, Lsb0; $($t)*]
        }
    };
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
        0,
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
        0,
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
    assert_eq!(
        bv.sign(),
        false,
        "conversion from f64 failed (sign): {:.20e}",
        fp
    );
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
    assert_eq!(
        !bv.sign(),
        false,
        "conversion from f64 failed (sign): {:.20e}",
        fp
    );
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
        -1022,
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
        -1023,
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
        -1023,
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
        1023,
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
    let rm = RoundingMode::NearestEven;
    let fps = [
        0.0,
        -0.0,
        f64::INFINITY,
        f64::NEG_INFINITY,
        f64::from_bits((0x7FF << 52) | (1 << 51)),
        f64::from_bits((0x7FF << 52) | 0x1),
    ];

    for fp in fps {
        let fp = Double::from(fp);
        let fp128: Quad = fp.round(rm);
        let fp2: Double = fp128.round(rm);

        let bv: BitVec = fp.into();
        let bv2: BitVec = fp2.into();
        assert_eq!(bv, bv2, "fp->fp->fp conversion failed: {} != {}", bv, bv2);
    }
}

#[test]
fn test_mul_2_4_2_4_2_4() {
    const E1: usize = 2;
    const N1: usize = 4;
    const E2: usize = 2;
    const N2: usize = 4;
    const E3: usize = 2;
    const N3: usize = 4;
    const RM: RoundingMode = RoundingMode::NearestEven;

    type F1 = Float<E1, N1>;
    type F2 = Float<E2, N2>;
    type F3 = Float<E3, N3>;

    for i in 0..u32::pow(2, F1::N as u32) {
        let mut xv = BitVec::from_element(i);
        xv.resize(F1::N, false);
        let x = F1::from(xv.clone());
        for j in 0..u32::pow(2, F2::N as u32) {
            let mut yv = BitVec::from_element(j);
            yv.resize(F2::N, false);
            let y = F2::from(yv.clone());

            let z: F3 = x.mul(&y, RM);
            let zv: BitVec = z.into();

            println!("{} * {} = {}", xv, yv, zv);
        }
    }
}

#[test]
fn sandbox() {
    let fp = Double::from(0.875);
    let fp2: Float<2, 4> = fp.round(RoundingMode::NearestEven);
}
