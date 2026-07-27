
/* Safe Rust API over the extracted sensor fusion + plausibility gate. */

fn zlist_from<'a>(p: &'a Program, xs: &[i64]) -> &'a Corelib_Init_Datatypes_list<'a, i64> {
    let mut acc: &'a Corelib_Init_Datatypes_list<'a, i64> =
        p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &x in xs.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, x, acc));
    }
    acc
}

/// Median-fuse the readings and gate each against the fused value.
/// Returns (fused, per-reading plausibility flags).
pub fn fuse(tol: i64, readings: &[i64]) -> (i64, Vec<bool>) {
    let p = Program::new();
    let (f, flags) = p.RocqRustExamples_SensorFusion_fusion_demo(tol, zlist_from(&p, readings));
    let mut out = Vec::new();
    let mut l = flags;
    loop {
        match l {
            Corelib_Init_Datatypes_list::nil(_) => break,
            Corelib_Init_Datatypes_list::cons(_, b, rest) => {
                out.push(*b);
                l = *rest;
            }
        }
    }
    (f, out)
}
