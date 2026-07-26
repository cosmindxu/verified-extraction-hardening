(** * Extraction driver: trading analytics with CHECKED arithmetic

    Identical to ExtractTrading.v except for one import:

      ExtrRustUncheckedArith  ->  Z.add extracts to  a + b
      ExtrRustCheckedArith    ->  Z.add extracts to  a.checked_add(b).unwrap()

    That single swap converts silent i64 wraparound -- which makes the
    extracted code disagree with every theorem in Trading.v -- into a panic.
    The FFI layer catches the panic and reports it as a status code, so the
    failure mode becomes "loud and contained" instead of "wrong answer". *)

From RocqRustExamples Require Import Trading.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/TradingChecked.rs" Rust Extract analyze.
