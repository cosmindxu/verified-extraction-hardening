(** * Extraction driver: verified insertion sort -> Rust

    [rocq-rust-extraction] 0.2.x is installed here as a theory-only package
    (no vernacular [Rust Extract] command), so we drive extraction through
    its Rocq-level API: [TypedExtraction.Rust.PluginExtract.extract], which
    - runs MetaRocq's typed erasure on the quoted program, and
    - pretty-prints the resulting lambda-box term as Rust (with preamble).

    The output is written to [extracted/InsertionSort.rs.out] via [Redirect]. *)

From RocqRustExamples Require Import InsertionSort.

From MetaRocq.Template Require Import All.
From MetaRocq.Utils Require Import bytestring.
From MetaRocq.Utils Require Import ResultMonad.
From TypedExtraction.Rust Require Import PluginExtract.
From TypedExtraction.Rust Require Import Printing.

Local Open Scope bs_scope.

(** Reflect the program (and all its dependencies) into MetaRocq syntax. *)
MetaRocq Quote Recursively Definition demo_prog := demo.

(** ** Remapping Rocq types to Rust primitives

    Without remapping, [Z] extracts to its binary inductive definition and
    [bool] to an enum whose variants are literally named [true]/[false] --
    Rust keywords, so that does not compile.  Upstream solves this with the
    [Extract Inductive] vernacular from the (unbuilt) OCaml plugin; the
    [remaps] record it produces is plain Rocq data, so we build it directly.
    Mirrors plugin/theories/ExtrRust{Basic,UncheckedArith}.v. *)

Definition ind_remap (ind : inductive) : option remapped_inductive :=
  let kn := string_of_kername (inductive_mind ind) in
  if String.eqb kn "Corelib.Init.Datatypes.bool" then
    Some {| re_ind_name := "bool";
            re_ind_ctors := ["true"; "false"];
            re_ind_match := None |}
  else if String.eqb kn "Corelib.Numbers.BinNums.Z" then
    Some {| re_ind_name := "i64";
            re_ind_ctors := ["0"; "__Z_frompos"; "__Z_fromneg"];
            re_ind_match := Some "__Z_elim!" |}
  else if String.eqb kn "Corelib.Numbers.BinNums.positive" then
    Some {| re_ind_name := "u64";
            re_ind_ctors := ["__pos_onebit"; "__pos_zerobit"; "1"];
            re_ind_match := Some "__pos_elim!" |}
  else if String.eqb kn "Corelib.Init.Datatypes.comparison" then
    Some {| re_ind_name := "std::cmp::Ordering";
            re_ind_ctors := ["std::cmp::Ordering::Equal";
                             "std::cmp::Ordering::Less";
                             "std::cmp::Ordering::Greater"];
            re_ind_match := None |}
  else None.

(** [Z.leb] becomes a primitive comparison; this also prunes the whole
    [Pos.compare_cont] / [CompOpp] dependency chain from the output. *)
Definition const_remap (kn : kername) : option string :=
  if String.eqb (string_of_kername kn) "Corelib.BinNums.IntDef.Z.leb" then
    Some "fn ##name##(&'a self, a: i64, b: i64) -> bool { a <= b }"
  else None.

Definition my_remaps : remaps :=
  {| remap_inductive := ind_remap;
     remap_constant := const_remap;
     remap_inline_constant _ := None |}.

(** Erase + print.  [fun _ => false]: inline nothing. *)
Definition rust_src : string :=
  match extract demo_prog my_remaps (fun _ => false) with
  | Ok src => src
  | Err e => "EXTRACTION FAILED: " ++ e
  end.

(** Force the computation before printing. *)
Definition rust_src_computed := Eval vm_compute in rust_src.

Redirect "extracted/InsertionSort.rs" MetaRocq Run (tmMsg rust_src_computed).
