
/* ------------------------------------------------------------------ *
 * Safe Rust API over the extracted RLE codec.                         *
 * ------------------------------------------------------------------ */

type ZList<'a> = Corelib_Init_Datatypes_list<'a, i64>;
type PairList<'a> = Corelib_Init_Datatypes_list<'a, __pair<i64, u64>>;

fn from_slice<'a>(p: &'a Program, xs: &[i64]) -> &'a ZList<'a> {
    let mut acc: &'a ZList<'a> = p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &x in xs.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, x, acc));
    }
    acc
}

fn pairs_from<'a>(p: &'a Program, xs: &[(i64, u64)]) -> &'a PairList<'a> {
    let mut acc: &'a PairList<'a> = p.alloc(Corelib_Init_Datatypes_list::nil(PhantomData));
    for &pr in xs.iter().rev() {
        acc = p.alloc(Corelib_Init_Datatypes_list::cons(PhantomData, pr, acc));
    }
    acc
}

/// Run-length encode. Output length <= input length (`encode_length_le`);
/// every count >= 1 (`encode_counts_pos`).
pub fn encode(input: &[i64]) -> Vec<(i64, u64)> {
    let p = Program::new();
    let mut out = Vec::new();
    let mut l = p.RocqRustExamples_Rle_encode(from_slice(&p, input));
    loop {
        match l {
            Corelib_Init_Datatypes_list::nil(_) => return out,
            Corelib_Init_Datatypes_list::cons(_, pr, rest) => {
                out.push(*pr);
                l = *rest;
            }
        }
    }
}

/// Run-length decode. Inverse of `encode` on its image (`rle_roundtrip`).
pub fn decode(input: &[(i64, u64)]) -> Vec<i64> {
    let p = Program::new();
    let mut out = Vec::new();
    let mut l = p.RocqRustExamples_Rle_decode(pairs_from(&p, input));
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
