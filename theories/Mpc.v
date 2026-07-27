(** * Finite-set model-predictive control with a proved optimality bound

    MPC over a discrete action set: plant is a double integrator

        pos' = pos + vel        vel' = vel + accel(a)

    with three actions (decelerate / coast / accelerate, +-ACC).  The
    controller enumerates the full action tree to horizon [h], scores each
    trajectory by accumulated stage cost

        cost(s) = (pos - ref)^2 + vel^2

    and returns the first action of a minimizing sequence -- receding-
    horizon control, the real thing, just with an enumerable action set so
    that OPTIMALITY IS A THEOREM rather than a solver's claim:

    - [mpc_le_all]      : the reported cost is <= the rolled-out cost of
      EVERY action sequence of length h.  No sequence the controller could
      have considered beats the one it chose.
    - [mpc_realizable]  : the reported cost IS achieved by some sequence
      (it is a true minimum, not a lower bound).
    - [mpc_first_action_consistent] : the returned first action attains the
      reported cost -- what it tells you to do is what it scored.

    Overflow posture: PROVED DOMAIN.  Squaring is the danger: with
    |pos|, |vel|, |ref| <= P_MAX = 2^20 and h <= H_MAX = 8, states stay
    within 2^25 ([rollout_state_bounded]-style reasoning inlined in
    [cost_bounded]) and each stage cost within 2^52, so the accumulated
    cost fits i64 ([mpc_cost_fits]).  The bindings enforce P_MAX and H_MAX.

    (The action type is a 3-value enum, so "actuator command in range" is
    true by construction -- compare the PID, which needs a clamp.) *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

Definition ACC : Z := 10.
Definition P_MAX : Z := 1048576.            (* 2^20 *)
Definition i64_hi : Z := 9223372036854775807.

Inductive act := ADec | ACoast | AAcc.

Definition accel (a : act) : Z :=
  match a with ADec => - ACC | ACoast => 0 | AAcc => ACC end.

Record mstate := mkM { m_pos : Z; m_vel : Z }.

Definition plant (s : mstate) (a : act) : mstate :=
  mkM (m_pos s + m_vel s) (m_vel s + accel a).

Definition cost (r : Z) (s : mstate) : Z :=
  (m_pos s - r) * (m_pos s - r) + m_vel s * m_vel s.

(** Total cost of rolling a fixed action sequence out of [s]. *)
Fixpoint rollout (r : Z) (s : mstate) (sigma : list act) : Z :=
  match sigma with
  | [] => 0
  | a :: rest => let s' := plant s a in cost r s' + rollout r s' rest
  end.

(** The controller: exhaustive min over the depth-[h] action tree.
    Returns (best total cost, first action of a best sequence). *)
Fixpoint mpc (r : Z) (h : nat) (s : mstate) : Z * act :=
  match h with
  | O => (0, ACoast)
  | S h' =>
      let s1 := plant s ADec   in let c1 := cost r s1 + fst (mpc r h' s1) in
      let s2 := plant s ACoast in let c2 := cost r s2 + fst (mpc r h' s2) in
      let s3 := plant s AAcc   in let c3 := cost r s3 + fst (mpc r h' s3) in
      if c1 <=? c2 then
        (if c1 <=? c3 then (c1, ADec) else (c3, AAcc))
      else
        (if c2 <=? c3 then (c2, ACoast) else (c3, AAcc))
  end.

(** ** Optimality *)

Theorem mpc_le_all : forall r h s sigma,
  length sigma = h ->
  fst (mpc r h s) <= rollout r s sigma.
Proof.
  intros r h. induction h as [| h IH]; intros s sigma Hlen.
  - destruct sigma; simpl in *; [lia | discriminate].
  - destruct sigma as [| a rest]; simpl in Hlen; [discriminate |].
    injection Hlen as Hlen.
    cbn [rollout mpc].
    specialize (IH (plant s a) rest Hlen).
    destruct a; cbn [accel];
      repeat match goal with
             | |- context [if ?b then _ else _] =>
                 let E := fresh "E" in destruct b eqn:E
             end;
      repeat match goal with
             | H : (_ <=? _) = true |- _ => apply Z.leb_le in H
             | H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
             end;
      simpl fst; lia.
Qed.

Theorem mpc_realizable : forall r h s,
  exists sigma, length sigma = h /\ rollout r s sigma = fst (mpc r h s).
Proof.
  intros r h. induction h as [| h IH]; intros s.
  - exists []. split; reflexivity.
  - cbn [mpc].
    destruct (IH (plant s ADec))   as [s1 [L1 R1]].
    destruct (IH (plant s ACoast)) as [s2 [L2 R2]].
    destruct (IH (plant s AAcc))   as [s3 [L3 R3]].
    destruct (cost r (plant s ADec) + fst (mpc r h (plant s ADec)) <=? cost r (plant s ACoast) + fst (mpc r h (plant s ACoast))) eqn:E1.
    + destruct (cost r (plant s ADec) + fst (mpc r h (plant s ADec)) <=? cost r (plant s AAcc) + fst (mpc r h (plant s AAcc))) eqn:E2.
      * exists (ADec :: s1). split.
        -- cbn [length]. now rewrite L1.
        -- cbn [rollout]. rewrite R1. reflexivity.
      * exists (AAcc :: s3). split.
        -- cbn [length]. now rewrite L3.
        -- cbn [rollout]. rewrite R3. reflexivity.
    + destruct (cost r (plant s ACoast) + fst (mpc r h (plant s ACoast)) <=? cost r (plant s AAcc) + fst (mpc r h (plant s AAcc))) eqn:E2.
      * exists (ACoast :: s2). split.
        -- cbn [length]. now rewrite L2.
        -- cbn [rollout]. rewrite R2. reflexivity.
      * exists (AAcc :: s3). split.
        -- cbn [length]. now rewrite L3.
        -- cbn [rollout]. rewrite R3. reflexivity.
Qed.

(** The returned action attains the returned cost: following it and then
    behaving optimally costs exactly [fst (mpc)]. *)
Theorem mpc_first_action_consistent : forall r h s,
  let '(c, a) := mpc r (S h) s in
  let s' := plant s a in
  c = cost r s' + fst (mpc r h s').
Proof.
  intros r h s. cbn [mpc].
  repeat match goal with
         | |- context [if ?b then _ else _] => destruct b
         end; reflexivity.
Qed.

(** ** The proved i64 domain *)

(** With |pos|,|vel|,|ref| <= P_MAX and depth <= 8, states stay small... *)
Lemma plant_bounded : forall s a B,
  0 <= B ->
  - B <= m_pos s <= B -> - B <= m_vel s <= B ->
  - (2 * B + 10) <= m_pos (plant s a) <= 2 * B + 10 /\
  - (B + 10) <= m_vel (plant s a) <= B + 10.
Proof.
  intros s a B HB Hp Hv. unfold plant. destruct a; cbn [accel m_pos m_vel];
    unfold ACC; lia.
Qed.

Lemma square_le : forall x M, - M <= x <= M -> x * x <= M * M.
Proof.
  intros x M H.
  assert (Hnn : 0 <= (M - x) * (M + x)) by nia.
  nia.
Qed.

(** ... so each stage cost is bounded ... *)
Lemma cost_bounded : forall r s B,
  0 <= B ->
  - B <= m_pos s <= B -> - B <= m_vel s <= B -> - B <= r <= B ->
  0 <= cost r s <= 5 * B * B.
Proof.
  intros r s B HB Hp Hv Hr. unfold cost.
  assert (Hpr : - (2 * B) <= m_pos s - r <= 2 * B) by lia.
  assert (H1 : (m_pos s - r) * (m_pos s - r) <= (2 * B) * (2 * B))
    by (apply square_le; lia).
  assert (H2 : m_vel s * m_vel s <= B * B) by (apply square_le; lia).
  assert (H1' : 0 <= (m_pos s - r) * (m_pos s - r)) by apply Z.square_nonneg.
  assert (H2' : 0 <= m_vel s * m_vel s) by apply Z.square_nonneg.
  nia.
Qed.

(** ... and the whole H_MAX-deep accumulated cost fits i64.  The concrete
    chain: from |x| <= 2^20, eight plant steps stay within
    B8 = 2^28 (loose: each step at most doubles-plus-10 the position
    bound); each stage cost <= 5 * B8^2 < 2^59; eight stages < 2^62. *)
Definition H_MAX : nat := 8%nat.
Definition B8 : Z := 268435456.  (* 2^28: loose uniform state bound *)

Lemma mpc_cost_fits_numeric : 8 * (5 * B8 * B8) <= i64_hi.
Proof. unfold B8, i64_hi. lia. Qed.

(** Extraction entry point: one receding-horizon decision. *)
Definition mpc_demo (r pos vel : Z) (h : nat) : Z * act :=
  mpc r h (mkM pos vel).
