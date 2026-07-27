(** Extraction driver: Pid -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import Pid.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/Pid.rs" Rust Extract pid_demo.
