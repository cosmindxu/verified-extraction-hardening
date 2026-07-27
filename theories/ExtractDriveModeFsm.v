(** Extraction driver: DriveModeFsm -> Rust (checked arithmetic build). *)

From RocqRustExamples Require Import DriveModeFsm.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/DriveModeFsm.rs" Rust Extract drive_demo.
