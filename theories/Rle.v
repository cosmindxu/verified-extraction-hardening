(** * Run-length encoding with a proved round trip

    [encode] compresses runs of equal values; [decode] expands them.  The
    headline theorem is the round trip:

        decode (encode l) = l

    Two supporting theorems earn their keep at the FFI boundary:

    - [encode_length_le] : the encoded list is never longer than the input.
      This is what lets the C ABI caller allocate output buffers of the
      input's size, with a proof instead of a hope.
    - [encode_counts_pos] : every run count is at least 1, so a count of 0
      coming out of the FFI indicates corruption, not valid data.

    Overflow posture: NONE NEEDED.  Values are copied, never computed with;
    counts only ever increment, and are bounded by the input length, which
    the host cannot make exceed the machine word.  (The extracted [S] on
    [nat] is checked addition in the Rust preamble anyway.) *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

(** Counts are [nat] (extracts to u64); values are [Z] (extracts to i64). *)

Fixpoint encode (l : list Z) : list (Z * nat) :=
  match l with
  | [] => []
  | x :: r =>
      match encode r with
      | (y, n) :: t => if Z.eqb x y then (y, S n) :: t else (x, 1%nat) :: (y, n) :: t
      | [] => [(x, 1%nat)]
      end
  end.

Fixpoint decode (e : list (Z * nat)) : list Z :=
  match e with
  | [] => []
  | (x, n) :: t => repeat x n ++ decode t
  end.

Theorem rle_roundtrip : forall l, decode (encode l) = l.
Proof.
  induction l as [| x r IH]; simpl; [reflexivity |].
  destruct (encode r) as [| [y n] t] eqn:E.
  - simpl in IH. rewrite <- IH. reflexivity.
  - destruct (Z.eqb x y) eqn:Exy; simpl.
    + apply Z.eqb_eq in Exy; subst y.
      rewrite <- IH. reflexivity.
    + rewrite <- IH. reflexivity.
Qed.

(** Buffer-sizing theorem for the FFI: |encode l| <= |l|. *)
Theorem encode_length_le : forall l, (length (encode l) <= length l)%nat.
Proof.
  induction l as [| x r IH]; simpl; [lia |].
  destruct (encode r) as [| [y n] t]; simpl in *; [lia |].
  destruct (Z.eqb x y); simpl; lia.
Qed.

(** Every emitted count is positive. *)
Theorem encode_counts_pos : forall l,
  Forall (fun p => (1 <= snd p)%nat) (encode l).
Proof.
  induction l as [| x r IH]; simpl; [constructor |].
  destruct (encode r) as [| [y n] t]; simpl.
  - repeat constructor.
  - inversion IH; subst.
    destruct (Z.eqb x y).
    + constructor; [simpl in *; lia | assumption].
    + constructor; [simpl; lia |].
      constructor; assumption.
Qed.

(** Decode length is the sum of the counts -- the bindings use this to size
    the decode buffer from host-side data. *)
Theorem decode_length : forall e,
  length (decode e) = list_sum (map snd e).
Proof.
  induction e as [| [x n] t IH]; simpl; [reflexivity |].
  rewrite length_app, repeat_length, IH. reflexivity.
Qed.

(** Extraction entry point: the round trip itself, which pulls in both
    [encode] and [decode] (the FFI calls them individually). *)
Definition rle_demo (l : list Z) : list Z := decode (encode l).
