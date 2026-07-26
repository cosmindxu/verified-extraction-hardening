(** * Verified trading analytics, extracted to Rust

    Prices are integers (ticks / cents) -- no floating point, so the Rocq
    proofs transfer to the extracted Rust without a real-arithmetic gap.

    Three components, each with a theorem that is worth having:

    1. [max_profit]     -- best single buy-then-sell trade.  The O(n) online
                           scan is proved EQUAL to the obviously-correct
                           O(n^2) specification.
    2. [max_drawdown]   -- worst peak-to-trough decline.  Same treatment.
    3. [run_orders]     -- a position/risk gate that rejects orders breaching
                           a position limit.  Proved to maintain the limit
                           as an invariant, for every order sequence.

    (1) and (2) are the interesting kind of verification: the efficient
    implementation is the one that ships, the naive one is the one you can
    read and believe, and the theorem says they never disagree. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
From Stdlib Require Import Bool.

Import ListNotations.
Local Open Scope Z_scope.

(** ** Maximum of a list, with 0 as the "do not trade" default *)

Fixpoint max_list (l : list Z) : Z :=
  match l with
  | [] => 0
  | x :: r => Z.max x (max_list r)
  end.

Lemma max_list_nonneg : forall l, 0 <= max_list l.
Proof. induction l as [| x r IH]; simpl; lia. Qed.

(** Pointwise max distributes over [max_list]; the key combinator for both
    algorithms below. *)
Lemma max_list_map_max : forall (f g : Z -> Z) l,
  max_list (map (fun q => Z.max (f q) (g q)) l)
  = Z.max (max_list (map f l)) (max_list (map g l)).
Proof.
  intros f g l. induction l as [| a r IH]; simpl; [lia |]. rewrite IH. lia.
Qed.

(** ** 1. Best single trade (buy once, sell once, later) *)

(** The specification: for each day, the best you could do buying that day is
    the max of [sell - buy] over all later days; the answer is the max of that
    over all days.  Quadratic, but you can read it and believe it. *)
Fixpoint max_profit_spec (l : list Z) : Z :=
  match l with
  | [] => 0
  | p :: rest =>
      Z.max (max_list (map (fun q => q - p) rest)) (max_profit_spec rest)
  end.

(** The implementation: one pass, carrying the cheapest price seen so far
    ([m]) and the best profit so far ([b]). *)
Fixpoint mp (m b : Z) (l : list Z) : Z :=
  match l with
  | [] => b
  | p :: rest => mp (Z.min m p) (Z.max b (p - m)) rest
  end.

Definition max_profit (l : list Z) : Z :=
  match l with
  | [] => 0
  | p :: rest => mp p 0 rest
  end.

(** The scan's accumulator, characterised.  Generalising over [m] and [b] is
    what makes the induction go through. *)
Lemma mp_spec : forall l m b, 0 <= b ->
  mp m b l
  = Z.max b (Z.max (max_list (map (fun q => q - m) l)) (max_profit_spec l)).
Proof.
  induction l as [| p rest IH]; intros m b Hb; simpl; [lia |].
  rewrite IH by lia.
  replace (map (fun q => q - Z.min m p) rest)
     with (map (fun q => Z.max (q - m) (q - p)) rest)
     by (apply map_ext; intros; lia).
  rewrite max_list_map_max.
  lia.
Qed.

Theorem max_profit_correct : forall l, max_profit l = max_profit_spec l.
Proof.
  destruct l as [| p rest]; simpl; [reflexivity |].
  rewrite mp_spec by lia.
  pose proof (max_list_nonneg (map (fun q => q - p) rest)).
  lia.
Qed.

(** You can always decline to trade, so profit is never negative. *)
Theorem max_profit_nonneg : forall l, 0 <= max_profit l.
Proof.
  intros l. rewrite max_profit_correct.
  destruct l as [| p rest]; simpl; [lia |].
  pose proof (max_list_nonneg (map (fun q => q - p) rest)). lia.
Qed.

(** ** 2. Maximum drawdown (worst peak-to-trough decline) *)

Fixpoint drawdown_spec (l : list Z) : Z :=
  match l with
  | [] => 0
  | p :: rest =>
      Z.max (max_list (map (fun q => p - q) rest)) (drawdown_spec rest)
  end.

(** One pass carrying the running peak and the worst decline so far. *)
Fixpoint mdd (peak worst : Z) (l : list Z) : Z :=
  match l with
  | [] => worst
  | p :: rest => mdd (Z.max peak p) (Z.max worst (peak - p)) rest
  end.

Definition max_drawdown (l : list Z) : Z :=
  match l with
  | [] => 0
  | p :: rest => mdd p 0 rest
  end.

Lemma mdd_spec : forall l peak worst, 0 <= worst ->
  mdd peak worst l
  = Z.max worst (Z.max (max_list (map (fun q => peak - q) l)) (drawdown_spec l)).
Proof.
  induction l as [| p rest IH]; intros peak worst Hw; simpl; [lia |].
  rewrite IH by lia.
  replace (map (fun q => Z.max peak p - q) rest)
     with (map (fun q => Z.max (peak - q) (p - q)) rest)
     by (apply map_ext; intros; lia).
  (* Pin the instantiation: left implicit, unification eta-contracts
     [fun q => peak - q] to [Z.sub peak] and lia then sees two distinct
     atoms for what is the same term. *)
  rewrite (max_list_map_max (fun q => peak - q) (fun q => p - q)).
  lia.
Qed.

Theorem max_drawdown_correct : forall l, max_drawdown l = drawdown_spec l.
Proof.
  destruct l as [| p rest]; simpl; [reflexivity |].
  rewrite mdd_spec by lia.
  pose proof (max_list_nonneg (map (fun q => p - q) rest)).
  lia.
Qed.

Theorem max_drawdown_nonneg : forall l, 0 <= max_drawdown l.
Proof.
  intros l. rewrite max_drawdown_correct.
  destruct l as [| p rest]; simpl; [lia |].
  pose proof (max_list_nonneg (map (fun q => p - q) rest)). lia.
Qed.

(** ** 3. Position limit / risk gate *)

Record order := mkOrder { ord_buy : bool ; ord_qty : Z }.

(** Apply an order only if the resulting position stays inside [-lim, lim];
    otherwise reject it and keep the current position. *)
Definition step (lim pos : Z) (o : order) : Z :=
  let want := if ord_buy o then pos + ord_qty o else pos - ord_qty o in
  if ((- lim <=? want) && (want <=? lim))%bool then want else pos.

Definition run_orders (lim pos : Z) (os : list order) : Z :=
  fold_left (step lim) os pos.

(** The safety property: no order sequence, however adversarial, can drive the
    book outside the limit.  Note there is no hypothesis on the orders at
    all -- quantities may be negative, huge, or absurd. *)
Theorem run_orders_within_limit : forall os lim pos,
  - lim <= pos <= lim ->
  - lim <= run_orders lim pos os <= lim.
Proof.
  unfold run_orders.
  induction os as [| o os IH]; intros lim pos H; [exact H |].
  simpl. apply IH. unfold step.
  set (want := if ord_buy o then pos + ord_qty o else pos - ord_qty o).
  destruct ((- lim <=? want) && (want <=? lim))%bool eqn:E; [| exact H].
  apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1; apply Z.leb_le in E2. lia.
Qed.

(** ** The extraction entry point *)

Record analytics := mkAnalytics {
  a_max_profit    : Z;
  a_max_drawdown  : Z;
  a_final_position : Z
}.

Definition analyze (prices : list Z) (lim : Z) (orders : list order) : analytics :=
  mkAnalytics (max_profit prices) (max_drawdown prices) (run_orders lim 0 orders).

(** * Overflow safety: deriving the safe input domain

    Everything above is about [Z], which is unbounded.  The extracted Rust
    uses [i64].  That remap is a TRUSTED ASSUMPTION, and it is where the
    guarantee leaks: with prices near +/-2^62, [q - p] exceeds [i64] and the
    extracted code silently returns a wrong answer while every theorem above
    remains true of the Rocq program.

    The fix is not to guess an input range in the bindings.  It is to prove
    which range is safe, here, and then have the bindings enforce exactly
    that.  The lemmas below bound EVERY intermediate the scans compute -- not
    just the final result -- by induction over the same recursion. *)

Definition i64_max : Z := 9223372036854775807.   (* 2^63 - 1 *)
Definition i64_min : Z := -9223372036854775808.  (* -2^63   *)

(** Every accumulator [mp] can hold lies in [0, 2B]; every running minimum
    lies in [-B, B].  Since the recursive call's arguments are exactly those,
    the induction covers all intermediates, not merely the return value. *)
Lemma mp_bounded : forall l m b B,
  0 <= B -> - B <= m <= B -> 0 <= b <= 2 * B ->
  Forall (fun p => - B <= p <= B) l ->
  0 <= mp m b l <= 2 * B.
Proof.
  induction l as [| p rest IH]; intros m b B HB Hm Hb H; cbn [mp]; [lia |].
  inversion H; subst.
  apply IH with (B := B); try lia; assumption.
Qed.

Theorem max_profit_bounded : forall l B,
  0 <= B -> Forall (fun p => - B <= p <= B) l ->
  0 <= max_profit l <= 2 * B.
Proof.
  intros l B HB H. destruct l as [| p rest]; cbn [max_profit]; [lia |].
  inversion H; subst.
  apply mp_bounded with (B := B); try lia; assumption.
Qed.

Lemma mdd_bounded : forall l peak worst B,
  0 <= B -> - B <= peak <= B -> 0 <= worst <= 2 * B ->
  Forall (fun p => - B <= p <= B) l ->
  0 <= mdd peak worst l <= 2 * B.
Proof.
  induction l as [| p rest IH]; intros peak worst B HB Hp Hw H; cbn [mdd]; [lia |].
  inversion H; subst.
  apply IH with (B := B); try lia; assumption.
Qed.

Theorem max_drawdown_bounded : forall l B,
  0 <= B -> Forall (fun p => - B <= p <= B) l ->
  0 <= max_drawdown l <= 2 * B.
Proof.
  intros l B HB H. destruct l as [| p rest]; cbn [max_drawdown]; [lia |].
  inversion H; subst.
  apply mdd_bounded with (B := B); try lia; assumption.
Qed.

(** The largest price bound for which [2 * B] still fits in [i64]. *)
Definition safe_price_bound : Z := 4611686018427387903.  (* 2^62 - 1 *)

(** So: bound the inputs by [safe_price_bound] and no intermediate of either
    scan can leave [i64].  This is the number the bindings must enforce. *)
Theorem max_profit_fits_i64 : forall l,
  Forall (fun p => - safe_price_bound <= p <= safe_price_bound) l ->
  i64_min <= max_profit l <= i64_max.
Proof.
  intros l H.
  pose proof (max_profit_bounded l safe_price_bound ltac:(unfold safe_price_bound; lia) H).
  unfold safe_price_bound, i64_min, i64_max in *. lia.
Qed.

Theorem max_drawdown_fits_i64 : forall l,
  Forall (fun p => - safe_price_bound <= p <= safe_price_bound) l ->
  i64_min <= max_drawdown l <= i64_max.
Proof.
  intros l H.
  pose proof (max_drawdown_bounded l safe_price_bound ltac:(unfold safe_price_bound; lia) H).
  unfold safe_price_bound, i64_min, i64_max in *. lia.
Qed.

(** ** The risk gate has its own overflow surface

    [step] computes [want] BEFORE range-checking it, so [pos + qty] is
    evaluated even for absurd quantities.  [pos] is bounded by [lim] (that is
    [run_orders_within_limit]), so bounding [qty] bounds [want]. *)
Lemma step_want_bounded : forall lim pos o B,
  0 <= lim -> 0 <= B ->
  - lim <= pos <= lim ->
  - B <= ord_qty o <= B ->
  - (lim + B) <= (if ord_buy o then pos + ord_qty o else pos - ord_qty o) <= lim + B.
Proof. intros lim pos o B H1 H2 H3 H4. destruct (ord_buy o); lia. Qed.

(** Hence the binding's obligation for the gate: [lim + B <= i64_max]. *)
Theorem step_fits_i64 : forall lim pos o B,
  0 <= lim -> 0 <= B -> lim + B <= i64_max ->
  - lim <= pos <= lim ->
  - B <= ord_qty o <= B ->
  i64_min <= (if ord_buy o then pos + ord_qty o else pos - ord_qty o) <= i64_max.
Proof.
  intros lim pos o B H1 H2 H3 H4 H5.
  pose proof (step_want_bounded lim pos o B H1 H2 H4 H5).
  unfold i64_min, i64_max in *. lia.
Qed.
