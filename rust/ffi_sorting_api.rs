
/* ------------------------------------------------------------------ *
 * Safe Rust API over the extracted module.  Appended to the generated *
 * code so it can reach the private `Program` and its methods.         *
 * ------------------------------------------------------------------ */

/// Sort via the Rocq-extracted `insertion_sort`.
///
/// The output length always equals the input length -- that is
/// `insertion_sort_length` in theories/InsertionSort.v, a corollary of the
/// permutation theorem. The FFI layer relies on it to size its buffer.
pub fn sort(input: &[i64]) -> Vec<i64> {
    let p = Program::new();

    let mut acc: &Corelib_Init_Datatypes_list<'_, i64> =
        p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &x in input.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, x, acc));
    }

    let mut out = Vec::with_capacity(input.len());
    let mut l = p.RocqRustExamples_InsertionSort_insertion_sort(acc);
    loop {
        match l {
            Corelib_Init_Datatypes_list::nil(_) => return out,
            Corelib_Init_Datatypes_list::cons(_, x, rest) => {
                out.push(*x);
                l = *rest;
            }
        }
    }
}
