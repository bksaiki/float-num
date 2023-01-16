use bitvec::prelude::Lsb0;
use float_sim::ieee754::*;

type BitVec = bitvec::prelude::BitVec<u32, Lsb0>;

#[test]
fn parameters() {
    assert_eq!(Quad::exponent_size(), 15);
    assert_eq!(Quad::total_size(), 128);
    assert_eq!(Quad::radix(), 2);
    assert_eq!(Quad::prec(), 113);
    assert_eq!(Quad::emax(), 16383);
    assert_eq!(Quad::emin(), -16382);

    assert_eq!(Double::exponent_size(), 11);
    assert_eq!(Double::total_size(), 64);
    assert_eq!(Double::radix(), 2);
    assert_eq!(Double::prec(), 53);
    assert_eq!(Double::emax(), 1023);
    assert_eq!(Double::emin(), -1022);

    assert_eq!(Single::exponent_size(), 8);
    assert_eq!(Single::total_size(), 32);
    assert_eq!(Single::radix(), 2);
    assert_eq!(Single::prec(), 24);
    assert_eq!(Single::emax(), 127);
    assert_eq!(Single::emin(), -126);
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
        -1024,
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
        -1075,
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
