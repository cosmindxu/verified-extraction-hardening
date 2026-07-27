(** Extraction driver: world-frame scene checker -> Rust (checked arith).

    Checked arithmetic is load-bearing here: outside the proved
    [SAFE_COORD] domain the ingest subtraction/negation overflows, and the
    checked build panics (contained at the FFI) instead of silently
    checking a corrupted scene. *)

From RocqRustExamples Require Import SceneWorld.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustCheckedArith.

Redirect "extracted/SceneWorld.rs" Rust Extract scene_world_demo.
