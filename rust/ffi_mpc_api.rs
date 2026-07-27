
/* Safe Rust API over the extracted finite-set MPC. */

/// One receding-horizon decision. Returns (predicted cost, action -1/0/+1).
pub fn decide(reference: i64, pos: i64, vel: i64, horizon: u64) -> (i64, i8) {
    let p = Program::new();
    let (c, a) = p.RocqRustExamples_Mpc_mpc_demo(
        reference,
        pos,
        vel,
        horizon,
    );
    let ai = match a {
        RocqRustExamples_Mpc_act::ADec(_) => -1i8,
        RocqRustExamples_Mpc_act::ACoast(_) => 0,
        RocqRustExamples_Mpc_act::AAcc(_) => 1,
    };
    (c, ai)
}
