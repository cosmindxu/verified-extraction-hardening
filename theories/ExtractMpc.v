(** Extraction driver: Mpc -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import Mpc.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/Mpc.rs" Rust Extract mpc_demo.
