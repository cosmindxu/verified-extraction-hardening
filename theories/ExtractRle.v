(** Extraction driver: RLE codec -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import Rle.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/Rle.rs" Rust Extract rle_demo.
