(** Extraction driver: modular exponentiation -> Rust (checked arithmetic).

    Checked arith matters here: u64 overflow outside the proved
    [safe_modulus] domain becomes a contained panic instead of a silent
    wrong answer.  (It also makes [mod 0] follow Rocq's [x mod 0 = x]
    convention -- [checked_rem(b).unwrap_or(a)] -- where the unchecked [%]
    would panic; the bindings reject [m = 0] regardless, since the
    correctness theorem assumes [m <> 0].) *)

From RocqRustExamples Require Import ModExp.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/ModExp.rs" Rust Extract modexp_demo.
