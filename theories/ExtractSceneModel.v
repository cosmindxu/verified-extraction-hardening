(** Extraction driver: ADAS scene checker -> Rust (checked arithmetic). *)

From RocqRustExamples Require Import SceneModel.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/SceneModel.rs" Rust Extract scene_demo.
