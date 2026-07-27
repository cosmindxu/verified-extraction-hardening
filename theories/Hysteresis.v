(** * Hysteresis relay controller, closed loop, with an invariant set

    The simplest hybrid controller: a two-point (bang-bang) thermostat.
    Heater ON below [T_LO], OFF above [T_HI], unchanged in between -- the
    discrete mode is the hybrid part; the plant temperature is the
    continuous part, discretized:

        t' = t + rh   (heating)        t' = t - rc   (cooling)

    where the per-step rates [rh], [rc] are DISTURBANCE INPUTS from the
    host, clamped into [1, RMAX] by the controller ([eff_rate]) -- the
    plant may be uncooperative, but not unboundedly so.

    Theorems:

    - [no_chatter]      : strictly inside (T_LO, T_HI) the mode never
      switches.  The hysteresis gap is what makes a relay controller
      usable; this is that property, as a theorem.
    - [band_invariant]  : the band [T_LO - RMAX, T_HI + RMAX] is an
      invariant set of the CLOSED LOOP: enter it and no disturbance
      sequence (within rate bounds) ever takes the temperature out.  This
      is practical stability -- not convergence to a point, but permanent
      capture in a band.
    - [cools_when_hot] / [heats_when_cold] : outside the band the loop
      makes strict progress toward it, at >= 1 per step.  Together with
      [band_invariant]: from any start, the loop reaches the band and
      stays there.
    - [run_band_invariant] : the fold-level version, for every disturbance
      stream.

    Overflow posture: THEOREM-HYPOTHESIS ENFORCEMENT.  [t + eff_rate] on an
    arbitrary i64 [t] can overflow at the extremes, so [step_fits_i64]
    proves safety for |t| <= T_ABS_MAX = 2^62 and the bindings enforce
    exactly that on the initial temperature; [band_invariant] then keeps
    the closed loop in a tiny range forever after. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

Definition T_LO : Z := 180.    (* 18.0 C *)
Definition T_HI : Z := 220.    (* 22.0 C *)
Definition RMAX : Z := 50.     (* max |temperature change| per step *)
Definition T_ABS_MAX : Z := 4611686018427387904.  (* 2^62 *)

(** Controller: pure relay with hysteresis. [true] = heater on. *)
Definition ctrl (t : Z) (heating : bool) : bool :=
  if t <=? T_LO then true
  else if T_HI <=? t then false
  else heating.

(** Host-supplied rates are clamped into [1, RMAX]. *)
Definition eff_rate (r : Z) : Z := Z.min RMAX (Z.max 1 r).

Record loop_state := mkLoop { ls_temp : Z; ls_heating : bool }.

(** One closed-loop step: controller decides, then the plant moves. *)
Definition step (s : loop_state) (rates : Z * Z) : loop_state :=
  let '(rh, rc) := rates in
  let h := ctrl (ls_temp s) (ls_heating s) in
  let t' := if h then ls_temp s + eff_rate rh else ls_temp s - eff_rate rc in
  mkLoop t' h.

Definition run (s : loop_state) (ds : list (Z * Z)) : loop_state :=
  fold_left step ds s.

(** ** No chattering inside the gap *)

Theorem no_chatter : forall t h,
  T_LO < t < T_HI -> ctrl t h = h.
Proof.
  intros t h [H1 H2]. unfold ctrl, T_LO, T_HI in *.
  destruct (t <=? 180) eqn:E1; [apply Z.leb_le in E1; lia |].
  destruct (220 <=? t) eqn:E2; [apply Z.leb_le in E2; lia |].
  reflexivity.
Qed.

(** ** The invariant set of the closed loop *)

Lemma eff_rate_bounds : forall r, 1 <= eff_rate r <= RMAX.
Proof. intros r. unfold eff_rate, RMAX. lia. Qed.

Theorem band_invariant : forall s d,
  T_LO - RMAX <= ls_temp s <= T_HI + RMAX ->
  T_LO - RMAX <= ls_temp (step s d) <= T_HI + RMAX.
Proof.
  intros s [rh rc] Hband. unfold step, ctrl.
  pose proof (eff_rate_bounds rh). pose proof (eff_rate_bounds rc).
  unfold T_LO, T_HI, RMAX in *.
  destruct (ls_temp s <=? 180) eqn:E1; simpl.
  - apply Z.leb_le in E1. lia.
  - apply Z.leb_gt in E1.
    destruct (220 <=? ls_temp s) eqn:E2; simpl.
    + apply Z.leb_le in E2. lia.
    + apply Z.leb_gt in E2. destruct (ls_heating s); simpl; lia.
Qed.

Theorem run_band_invariant : forall ds s,
  T_LO - RMAX <= ls_temp s <= T_HI + RMAX ->
  T_LO - RMAX <= ls_temp (run s ds) <= T_HI + RMAX.
Proof.
  unfold run.
  induction ds as [| d ds IH]; intros s Hband; simpl; [exact Hband |].
  apply IH. now apply band_invariant.
Qed.

(** ** Strict progress toward the band from outside *)

Theorem cools_when_hot : forall s d,
  T_HI <= ls_temp s ->
  ls_temp (step s d) < ls_temp s.
Proof.
  intros s [rh rc] Hhot. unfold step, ctrl.
  pose proof (eff_rate_bounds rc).
  unfold T_LO, T_HI, RMAX in *.
  destruct (ls_temp s <=? 180) eqn:E1; simpl.
  - apply Z.leb_le in E1. lia.
  - replace (220 <=? ls_temp s) with true
      by (symmetry; apply Z.leb_le; lia).
    simpl. lia.
Qed.

Theorem heats_when_cold : forall s d,
  ls_temp s <= T_LO ->
  ls_temp s < ls_temp (step s d).
Proof.
  intros s [rh rc] Hcold. unfold step, ctrl.
  pose proof (eff_rate_bounds rh).
  unfold T_LO, T_HI, RMAX in *.
  replace (ls_temp s <=? 180) with true
    by (symmetry; apply Z.leb_le; lia).
  simpl. lia.
Qed.

(** ** The proved i64 domain for one step *)

Theorem step_fits_i64 : forall s d,
  - T_ABS_MAX <= ls_temp s <= T_ABS_MAX ->
  - (T_ABS_MAX + RMAX) <= ls_temp (step s d) <= T_ABS_MAX + RMAX.
Proof.
  intros s [rh rc] Habs. unfold step.
  pose proof (eff_rate_bounds rh). pose proof (eff_rate_bounds rc).
  unfold T_ABS_MAX, RMAX in *.
  destruct (ctrl (ls_temp s) (ls_heating s)); simpl; lia.
Qed.

(** Extraction entry point. *)
Definition thermo_demo (t0 : Z) (ds : list (Z * Z)) : loop_state :=
  run (mkLoop t0 false) ds.
