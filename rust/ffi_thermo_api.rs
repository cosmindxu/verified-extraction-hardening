
/* Safe Rust API over the extracted hysteresis thermostat loop. */

type RateList<'a> = Corelib_Init_Datatypes_list<'a, __pair<i64, i64>>;

fn rates_from<'a>(p: &'a Program, ds: &[(i64, i64)]) -> &'a RateList<'a> {
    let mut acc: &'a RateList<'a> = p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &pr in ds.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, pr, acc));
    }
    acc
}

/// Run the closed loop from t0 (heater initially off) under per-step
/// disturbance rates. Returns (final temp, heating?).
pub fn run(t0: i64, rates: &[(i64, i64)]) -> (i64, bool) {
    let p = Program::new();
    let s = p.RocqRustExamples_Hysteresis_thermo_demo(t0, rates_from(&p, rates));
    match s {
        RocqRustExamples_Hysteresis_loop_state::mkLoop(_, t, h) => (*t, *h),
    }
}
