
/* Safe Rust API over the extracted PID controller. */

fn zlist_from<'a>(p: &'a Program, xs: &[i64]) -> &'a Corelib_Init_Datatypes_list<'a, i64> {
    let mut acc: &'a Corelib_Init_Datatypes_list<'a, i64> =
        p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &x in xs.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, x, acc));
    }
    acc
}

/// Run the PID over an error sequence from the zero state.
/// Returns (outputs, final integ, final prev).
pub fn run(kp: i64, ki: i64, kd: i64, errors: &[i64]) -> (Vec<i64>, i64, i64) {
    let p = Program::new();
    let (us, st) = p.RocqRustExamples_Pid_pid_demo(kp, ki, kd, zlist_from(&p, errors));
    let mut outs = Vec::new();
    let mut l = us;
    loop {
        match l {
            Corelib_Init_Datatypes_list::nil(_) => break,
            Corelib_Init_Datatypes_list::cons(_, u, rest) => {
                outs.push(*u);
                l = *rest;
            }
        }
    }
    match st {
        RocqRustExamples_Pid_pid_state::mkPid(_, integ, prev) => (outs, *integ, *prev),
    }
}
