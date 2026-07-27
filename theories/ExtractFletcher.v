(** Extraction driver: Fletcher -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import Fletcher.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/Fletcher.rs" Rust Extract fletcher_demo.
