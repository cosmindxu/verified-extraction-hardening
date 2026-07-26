(** * Order-lifecycle state machine with proved invariants

    A minimal exchange-order FSM: an order for [st_qty] units accumulates
    fills and can be canceled.  [apply_evt] is the transition function;
    [run_events] folds it over an event stream.

    Quantities are [Z] rather than [N]: the [Z] remap surface
    ([Corelib.BinNums.IntDef.Z.*]) is the one this repo has already
    exercised; the stdlib [N] comparison operators resolve to kernel names
    the plugin's remap tables miss on Rocq 9.1, which extracts them from
    source and (for [N.compare]) trips an arity bug on the remapped
    [Pos.compare].  See the README note on remap namespace skew.

    Theorems:

    - [run_invariant]    : [0 <= filled <= qty] for EVERY event stream --
      fills that would overfill (or negative fills) are rejected.
    - [canceled_frozen]  : a canceled order never changes again.  Not merely
      "stays canceled": the entire state is frozen.
    - [fill_add_bounded] : the only addition the machine performs is already
      bounded by [st_qty] when it happens.

    Overflow posture: DESIGNED OUT.  The guard compares BEFORE adding
    ([0 <=? n] and [n <=? qty - filled], the subtraction well-defined under
    the invariant), so [filled + n] is evaluated only when the result is
    known to land in [0, qty].  Unlike the trading gate (which computes
    [pos + qty] first and needs a proved side condition), this machine is
    safe for ALL inputs -- the bindings enforce nothing beyond [qty >= 0].
    Contrast the three postures: RLE needs no arithmetic, modexp needs a
    proved domain, this needs neither. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

Record ostate := mkState {
  st_qty      : Z;     (* order size, immutable *)
  st_filled   : Z;     (* accumulated fills *)
  st_canceled : bool
}.

Inductive event :=
  | EvFill (n : Z)
  | EvCancel.

Definition apply_evt (s : ostate) (e : event) : ostate :=
  match e with
  | EvCancel => mkState (st_qty s) (st_filled s) true
  | EvFill n =>
      if st_canceled s then s
      else if ((0 <=? n) && (n <=? st_qty s - st_filled s))%bool
           then mkState (st_qty s) (st_filled s + n) false
           else s   (* negative or overfilling: reject *)
  end.

Definition run_events (s : ostate) (es : list event) : ostate :=
  fold_left apply_evt es s.

Definition init (q : Z) : ostate := mkState q 0 false.

(** ** Quantity is immutable *)

Lemma apply_evt_qty : forall s e, st_qty (apply_evt s e) = st_qty s.
Proof.
  intros s e. destruct e as [n |]; simpl; [| reflexivity].
  destruct (st_canceled s); [reflexivity |].
  destruct (((0 <=? n) && (n <=? st_qty s - st_filled s))%bool); reflexivity.
Qed.

(** ** The fill guard's addition is bounded when it fires *)

Lemma fill_add_bounded : forall s n,
  0 <= st_filled s <= st_qty s ->
  ((0 <=? n) && (n <=? st_qty s - st_filled s))%bool = true ->
  0 <= st_filled s + n <= st_qty s.
Proof.
  intros s n Hinv Hg.
  apply andb_true_iff in Hg as [H1 H2].
  apply Z.leb_le in H1; apply Z.leb_le in H2. lia.
Qed.

(** ** The invariant, single step then folded *)

Lemma apply_evt_invariant : forall s e,
  0 <= st_filled s <= st_qty s ->
  0 <= st_filled (apply_evt s e) <= st_qty (apply_evt s e).
Proof.
  intros s e Hinv. destruct e as [n |]; simpl; [| exact Hinv].
  destruct (st_canceled s) eqn:Hc; [exact Hinv |].
  destruct (((0 <=? n) && (n <=? st_qty s - st_filled s))%bool) eqn:Hg;
    simpl; [| exact Hinv].
  now apply fill_add_bounded.
Qed.

Theorem run_invariant : forall es s,
  0 <= st_filled s <= st_qty s ->
  0 <= st_filled (run_events s es) <= st_qty (run_events s es).
Proof.
  unfold run_events.
  induction es as [| e es IH]; intros s Hinv; simpl; [exact Hinv |].
  apply IH. now apply apply_evt_invariant.
Qed.

Corollary init_run_invariant : forall q es,
  0 <= q ->
  0 <= st_filled (run_events (init q) es) <= q.
Proof.
  intros q es Hq.
  assert (H := run_invariant es (init q) (conj (Z.le_refl 0) Hq)).
  assert (Hqty : st_qty (run_events (init q) es) = q).
  { unfold run_events. clear H.
    induction es as [| e es IH] using rev_ind; [reflexivity |].
    rewrite fold_left_app. cbn [fold_left]. now rewrite apply_evt_qty. }
  now rewrite Hqty in H.
Qed.

(** ** Cancellation freezes the entire state *)

Lemma apply_evt_frozen : forall s e,
  st_canceled s = true -> apply_evt s e = s.
Proof.
  intros s e Hc. destruct e as [n |]; simpl; rewrite ?Hc.
  - reflexivity.
  - destruct s; simpl in *; now subst.
Qed.

Theorem canceled_frozen : forall es s,
  st_canceled s = true -> run_events s es = s.
Proof.
  unfold run_events.
  induction es as [| e es IH]; intros s Hc; simpl; [reflexivity |].
  rewrite (apply_evt_frozen s e Hc). now apply IH.
Qed.

(** Extraction entry point. *)
Definition fsm_demo (q : Z) (es : list event) : ostate :=
  run_events (init q) es.
