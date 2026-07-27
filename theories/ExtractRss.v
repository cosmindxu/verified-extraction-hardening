(** Extraction driver: Rss -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import Rss.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/Rss.rs" Rust Extract rss_demo.
