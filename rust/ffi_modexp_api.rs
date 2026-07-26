
/* ------------------------------------------------------------------ *
 * Safe Rust API over the extracted modular exponentiation.            *
 * ------------------------------------------------------------------ */

/// `(b ^ e) mod m`, by verified square-and-multiply (`pow_mod_correct`).
///
/// Caller obligations (enforced by the Python bindings, panics contained
/// by the FFI if bypassed):
///   - `m != 0`: the correctness theorem assumes it. (The checked build's
///     `checked_rem(b).unwrap_or(a)` happens to match Rocq's `x mod 0 = x`,
///     but the theorems don't cover `m = 0`, so it is rejected anyway.)
///   - `m <= 2^32` (`safe_modulus`): keeps every intermediate product
///     within u64 (`square_fits`, `mixed_fits`); the checked build panics
///     outside it rather than wrapping.
pub fn pow_mod(m: u64, b: u64, e: u64) -> u64 {
    let p = Program::new();
    p.RocqRustExamples_ModExp_pow_mod(m, b, e)
}
