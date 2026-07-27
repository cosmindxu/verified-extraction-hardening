(** Extraction driver: Hysteresis -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import Hysteresis.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/Hysteresis.rs" Rust Extract thermo_demo.
