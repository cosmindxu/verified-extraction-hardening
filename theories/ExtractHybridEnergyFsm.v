(** Extraction driver: HybridEnergyFsm -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import HybridEnergyFsm.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/HybridEnergyFsm.rs" Rust Extract energy_demo.
