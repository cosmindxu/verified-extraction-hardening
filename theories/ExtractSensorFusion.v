(** Extraction driver: SensorFusion -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import SensorFusion.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/SensorFusion.rs" Rust Extract fusion_demo.
