(** * Extraction driver: verified trading analytics -> Rust

    Uses the plugin vernacular (see ExtractInsertionSortPlugin.v).  The entry
    point [analyze] pulls in [max_profit], [max_drawdown] and [run_orders],
    so one [Rust Extract] emits the whole module. *)

From RocqRustExamples Require Import Trading.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustUncheckedArith.

Redirect "extracted/Trading.rs" Rust Extract analyze.
