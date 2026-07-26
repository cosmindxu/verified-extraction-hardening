
/* ------------------------------------------------------------------ *
 * Safe Rust API over the extracted trading module.                    *
 * ------------------------------------------------------------------ */

fn prices<'a>(p: &'a Program, xs: &[i64]) -> &'a Corelib_Init_Datatypes_list<'a, i64> {
    let mut acc: &'a Corelib_Init_Datatypes_list<'a, i64> =
        p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &x in xs.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, x, acc));
    }
    acc
}

type OrderList<'a> =
    Corelib_Init_Datatypes_list<'a, &'a RocqRustExamples_Trading_order<'a>>;

fn orders<'a>(p: &'a Program, os: &[(bool, i64)]) -> &'a OrderList<'a> {
    let mut acc: &'a OrderList<'a> =
        p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &(buy, qty) in os.iter().rev() {
        let o = p.alloc(RocqRustExamples_Trading_order::mkOrder(PhantomData, buy, qty));
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, o, acc));
    }
    acc
}

/// Best single buy-then-sell trade. Proved equal to `max_profit_spec`.
pub fn max_profit(px: &[i64]) -> i64 {
    let p = Program::new();
    p.RocqRustExamples_Trading_max_profit(prices(&p, px))
}

/// Worst peak-to-trough decline. Proved equal to `drawdown_spec`.
pub fn max_drawdown(px: &[i64]) -> i64 {
    let p = Program::new();
    p.RocqRustExamples_Trading_max_drawdown(prices(&p, px))
}

/// Position after running `os` through the risk gate. Proved to stay within
/// `[-limit, limit]` whenever `-limit <= initial <= limit`.
pub fn run_orders(limit: i64, initial: i64, os: &[(bool, i64)]) -> i64 {
    let p = Program::new();
    p.RocqRustExamples_Trading_run_orders(limit, initial, orders(&p, os))
}

/// All three at once: `(max_profit, max_drawdown, final_position)`.
pub fn analyze(px: &[i64], limit: i64, os: &[(bool, i64)]) -> (i64, i64, i64) {
    let p = Program::new();
    let a = p.RocqRustExamples_Trading_analyze(prices(&p, px), limit, orders(&p, os));
    match a {
        RocqRustExamples_Trading_analytics::mkAnalytics(_, profit, dd, pos) => (*profit, *dd, *pos),
    }
}
