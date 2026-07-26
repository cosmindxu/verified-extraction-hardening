(** * Extraction driver #2: same program, via the OCaml plugin

    Identical output goal to [ExtractInsertionSort.v], but using the
    vernacular from [rocq-typed-extraction-plugin]:

      - [Rust Extract <ref>] instead of quoting + calling [extract] by hand
      - [Extract Inductive] / [Extract Constant] instead of building a
        [remaps] record by hand

    The remap tables that driver #1 transcribes by hand are just
    [Require]d here from the plugin's own libraries. *)

From RocqRustExamples Require Import InsertionSort.

From TypedExtraction.Plugin Require Import Loader.
From TypedExtraction.Plugin Require Import ExtrRustBasic.
From TypedExtraction.Plugin Require Import ExtrRustUncheckedArith.

Redirect "extracted/InsertionSortPlugin.rs" Rust Extract demo.
