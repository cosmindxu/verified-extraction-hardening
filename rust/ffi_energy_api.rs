
/* Safe Rust API over the extracted hybrid energy FSM. */

fn zlist_from<'a>(p: &'a Program, xs: &[i64]) -> &'a Corelib_Init_Datatypes_list<'a, i64> {
    let mut acc: &'a Corelib_Init_Datatypes_list<'a, i64> =
        p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &x in xs.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, x, acc));
    }
    acc
}

/// Run power requests from initial SoC; returns (mode 0=EV 1=HA 2=CS, soc).
pub fn run(soc0: i64, requests: &[i64]) -> (u8, i64) {
    let p = Program::new();
    let s = p.RocqRustExamples_HybridEnergyFsm_energy_demo(soc0, zlist_from(&p, requests));
    match s {
        RocqRustExamples_HybridEnergyFsm_estate::mkE(_, m, soc) => {
            let mc = match m {
                RocqRustExamples_HybridEnergyFsm_emode::EvOnly(_) => 0,
                RocqRustExamples_HybridEnergyFsm_emode::HybridAssist(_) => 1,
                RocqRustExamples_HybridEnergyFsm_emode::ChargeSustain(_) => 2,
            };
            (mc, *soc)
        }
    }
}
