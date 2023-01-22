/*
    The sandbox
*/

use float_sim::{ieee754::*, *};

fn mul<N: Number>(x: N, y: N, ctx: N::Ctx) -> N {
    x.mul(&y, &ctx)
}

#[test]
fn sandbox() {
    type N = Float<11, 64>;

    let a = N::from(2.0);
    let b = N::from(3.0);
    let ctx = IEEEContext::default();
    let _c = mul(a, b, ctx);
}
