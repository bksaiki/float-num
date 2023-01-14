use float_sim::ieee754::*;

#[test]
fn init_tests() {
    // let f128 = Quad::new();
    // let f32 = Single::new();
    // let f16 = Half::new();

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
