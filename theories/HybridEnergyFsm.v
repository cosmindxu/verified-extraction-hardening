(** * Hybrid-vehicle energy-management state machine

    Battery state of charge (SoC, per-mille of capacity: 0..1000) plus an
    operating mode:

      - [EvOnly]        : electric drive only (engine off)
      - [HybridAssist]  : engine + battery under high demand
      - [ChargeSustain] : engine propels AND charges the battery

    Each tick carries the driver's power request [r] (arbitrary [Z]:
    positive = propulsion demand, negative = braking).  Mode selection uses
    SoC hysteresis: drop below [SOC_LO] and the machine enters
    [ChargeSustain]; it leaves only at [SOC_HI] -- the gap prevents mode
    thrash at the threshold.

    Theorems (for EVERY request stream, no hypotheses on the requests):

    - [run_soc_bounds]  : 0 <= soc <= 1000, always.
    - [run_ev_floor]    : in [EvOnly], soc >= SOC_LO, always -- the machine
      never lets electric-only driving strand the battery below its floor.
    - [cs_charges]      : while [ChargeSustain] persists, soc never
      decreases -- charge-sustain actually sustains.

    Overflow posture: DESIGNED OUT.  The raw request is never added to
    anything: propulsion drain is [Z.min DRN r] (a comparison + selection),
    regen charge is the constant [RGN] (deliberately NOT computed from
    [-r]: negating i64::MIN panics the checked build; see the drive-mode
    FSM header for the same principle applied to [Z.abs]).  All arithmetic
    is between soc (bounded 0..1000 by the invariant) and constants < 10,
    so no intermediate can approach the i64 edge for ANY input. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

Definition SOC_LO : Z := 200.   (* charge-sustain entry threshold *)
Definition SOC_HI : Z := 850.   (* charge-sustain exit threshold (hysteresis) *)
Definition DRN : Z := 8.        (* max battery drain per tick, EV mode *)
Definition HDRN : Z := 3.       (* battery drain per tick, hybrid assist *)
Definition CHG : Z := 5.        (* charge per tick, charge-sustain *)
Definition RGN : Z := 6.        (* regen charge per tick (braking) *)

Inductive emode := EvOnly | HybridAssist | ChargeSustain.

Record estate := mkE { em_mode : emode; em_soc : Z }.

Definition clamp_soc (x : Z) : Z := Z.min 1000 (Z.max 0 x).

Definition step (s : estate) (r : Z) : estate :=
  if r <? 0 then
    (* braking: regen at a fixed rate; mode unchanged *)
    mkE (em_mode s) (clamp_soc (em_soc s + RGN))
  else
    let d := Z.min DRN r in                    (* bounded propulsion drain *)
    match em_mode s with
    | EvOnly =>
        if em_soc s - d <? SOC_LO
        then mkE ChargeSustain (clamp_soc (em_soc s + CHG))
        else if DRN <? r
             then mkE HybridAssist (em_soc s - HDRN)
             else mkE EvOnly (em_soc s - d)
    | HybridAssist =>
        if em_soc s - HDRN <? SOC_LO
        then mkE ChargeSustain (clamp_soc (em_soc s + CHG))
        else if r <=? DRN
             then mkE EvOnly (em_soc s - HDRN)
             else mkE HybridAssist (em_soc s - HDRN)
    | ChargeSustain =>
        if SOC_HI <=? em_soc s + CHG
        then mkE EvOnly (clamp_soc (em_soc s + CHG))
        else mkE ChargeSustain (clamp_soc (em_soc s + CHG))
    end.

Definition run (s : estate) (rs : list Z) : estate := fold_left step rs s.

Definition init (soc0 : Z) : estate := mkE ChargeSustain (clamp_soc soc0).

(** ** The invariant: bounds + the EV floor *)

Definition Inv (s : estate) : Prop :=
  0 <= em_soc s <= 1000 /\
  (em_mode s = EvOnly -> SOC_LO <= em_soc s).

Lemma clamp_soc_bounds : forall x, 0 <= clamp_soc x <= 1000.
Proof. intros x. unfold clamp_soc. lia. Qed.

Lemma step_inv : forall s r, Inv s -> Inv (step s r).
Proof.
  intros s r [Hb Hev]. unfold Inv, step in *.
  unfold SOC_LO, SOC_HI, DRN, HDRN, CHG, RGN in *.
  destruct (r <? 0) eqn:Hr.
  - (* regen *)
    split; simpl; [apply clamp_soc_bounds |].
    intros Hm. specialize (Hev Hm). unfold clamp_soc. lia.
  - apply Z.ltb_ge in Hr.
    destruct (em_mode s) eqn:Hm.
    + (* EvOnly *)
      specialize (Hev eq_refl).
      destruct (em_soc s - Z.min 8 r <? 200) eqn:Hlo.
      * split; simpl; [apply clamp_soc_bounds | discriminate].
      * apply Z.ltb_ge in Hlo.
        destruct (8 <? r) eqn:Hhi.
        -- split; simpl; [lia | discriminate].
        -- split; simpl; [lia | intros _; lia].
    + (* HybridAssist *)
      destruct (em_soc s - 3 <? 200) eqn:Hlo.
      * split; simpl; [apply clamp_soc_bounds | discriminate].
      * apply Z.ltb_ge in Hlo.
        destruct (r <=? 8) eqn:Hlow.
        -- split; simpl; [lia | intros _; lia].
        -- split; simpl; [lia | discriminate].
    + (* ChargeSustain *)
      destruct (850 <=? em_soc s + 5) eqn:Hx.
      * apply Z.leb_le in Hx.
        split; simpl; [apply clamp_soc_bounds |].
        intros _. unfold clamp_soc. lia.
      * split; simpl; [apply clamp_soc_bounds | discriminate].
Qed.

Theorem run_inv : forall rs s, Inv s -> Inv (run s rs).
Proof.
  unfold run.
  induction rs as [| r rs IH]; intros s HI; simpl; [exact HI |].
  apply IH. now apply step_inv.
Qed.

Theorem run_soc_bounds : forall soc0 rs,
  0 <= em_soc (run (init soc0) rs) <= 1000.
Proof.
  intros soc0 rs.
  assert (HI : Inv (init soc0)).
  { split; simpl; [apply clamp_soc_bounds | discriminate]. }
  exact (proj1 (run_inv rs (init soc0) HI)).
Qed.

Theorem run_ev_floor : forall soc0 rs,
  em_mode (run (init soc0) rs) = EvOnly ->
  SOC_LO <= em_soc (run (init soc0) rs).
Proof.
  intros soc0 rs.
  assert (HI : Inv (init soc0)).
  { split; simpl; [apply clamp_soc_bounds | discriminate]. }
  exact (proj2 (run_inv rs (init soc0) HI)).
Qed.

(** ** Charge-sustain sustains: soc is monotone while the mode persists *)

Theorem cs_charges : forall s r,
  Inv s ->
  em_mode s = ChargeSustain ->
  em_mode (step s r) = ChargeSustain ->
  em_soc s <= em_soc (step s r).
Proof.
  intros s r [Hb _] Hm Hm'. unfold step in *.
  unfold SOC_HI, CHG, RGN in *.
  destruct (r <? 0) eqn:Hr.
  - simpl in *. unfold clamp_soc. lia.
  - rewrite Hm in *.
    destruct (850 <=? em_soc s + 5) eqn:Hx; simpl in *;
      [discriminate | unfold clamp_soc; lia].
Qed.

(** Extraction entry point. *)
Definition energy_demo (soc0 : Z) (rs : list Z) : estate := run (init soc0) rs.
