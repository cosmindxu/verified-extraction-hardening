
/* ------------------------------------------------------------------ *
 * Safe Rust API over the extracted order FSM.                         *
 * ------------------------------------------------------------------ */

type EvList<'a> =
    Corelib_Init_Datatypes_list<'a, &'a RocqRustExamples_OrderFsm_event<'a>>;

/// Events as (is_fill, qty): (true, n) = Fill(n), (false, _) = Cancel.
fn events_from<'a>(p: &'a Program, es: &[(bool, i64)]) -> &'a EvList<'a> {
    let mut acc: &'a EvList<'a> = p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &(fill, n) in es.iter().rev() {
        let e: &'a RocqRustExamples_OrderFsm_event<'a> = if fill {
            p.alloc(RocqRustExamples_OrderFsm_event::EvFill(PhantomData, n))
        } else {
            p.alloc(RocqRustExamples_OrderFsm_event::EvCancel(PhantomData))
        };
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, e, acc));
    }
    acc
}

/// Run an event stream against a fresh order of size `qty`.
/// Returns `(filled, canceled)`.
///
/// Safe for ALL event streams: `run_invariant` needs no hypothesis on the
/// events (negative and overfilling fills are rejected by the guard, which
/// compares before adding — `fill_add_bounded`), so even the checked build
/// cannot panic.
pub fn run(qty: i64, events: &[(bool, i64)]) -> (i64, bool) {
    let p = Program::new();
    let s = p.RocqRustExamples_OrderFsm_fsm_demo(qty, events_from(&p, events));
    match s {
        RocqRustExamples_OrderFsm_ostate::mkState(_, _qty, filled, canceled) => {
            (*filled, *canceled)
        }
    }
}
