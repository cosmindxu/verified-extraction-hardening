
/* Safe Rust API over the extracted Fletcher-16 checksum. */

fn zlist_from<'a>(p: &'a Program, xs: &[i64]) -> &'a Corelib_Init_Datatypes_list<'a, i64> {
    let mut acc: &'a Corelib_Init_Datatypes_list<'a, i64> =
        p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &x in xs.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, x, acc));
    }
    acc
}

/// Fletcher-16 over the symbols. Returns (s1, s2); packed checksum is
/// 256*s2 + s1. `single_error_detected` (Fletcher.v) guarantees any
/// single-symbol corruption changes the checksum — PROVIDED every symbol
/// is in [0, 254] (mod-255 symbols; 0 and 255 are congruent, the classic
/// Fletcher blind spot). The bindings enforce that domain.
pub fn fletcher16(data: &[i64]) -> (i64, i64) {
    let p = Program::new();
    let (s1, s2) = p.RocqRustExamples_Fletcher_fletcher_demo(zlist_from(&p, data));
    (s1, s2)
}
