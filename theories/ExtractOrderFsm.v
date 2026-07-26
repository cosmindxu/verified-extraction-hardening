(** Extraction driver: order FSM -> Rust (checked arithmetic build).

    The machine is overflow-safe by construction ([fill_add_bounded]), so the
    checked build should never panic -- keeping it checked makes that claim
    falsifiable at runtime rather than assumed. *)

From RocqRustExamples Require Import OrderFsm.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/OrderFsm.rs" Rust Extract fsm_demo.
