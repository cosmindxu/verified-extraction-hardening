(** * Automotive drive-mode state machine (PRND + Fault) with shift interlocks

    A shift-by-wire gear selector: Park / Reverse / Neutral / Drive, plus an
    absorbing Fault mode.  Every shift request carries the vehicle speed
    (signed, cm/s), and the interlocks a real transmission controller
    enforces are theorems here:

    - [park_interlock]     : Park engages only near standstill
      (|v| <= P_ENGAGE_MAX) -- the parking-pawl protection.
    - [reverse_interlock]  : Reverse engages only below SHIFT_DIR_MAX --
      the driveline direction-change protection.  Dually, Drive is refused
      while rolling backwards fast ([drive_interlock]).
    - [fault_absorbing]    : once in Fault, the only way out is an explicit
      FaultCleared AT STANDSTILL (v = 0), and it lands in Park.
    - [run_fault_sticky]   : over a whole event stream containing no
      standstill-clear, Fault persists -- the run-level corollary.

    A rejected shift keeps the current mode: the selector is a REQUEST, the
    machine decides.  That "reject, don't clamp" style is what makes every
    interlock a one-line case analysis instead of an arithmetic argument.

    Overflow posture: NO ARITHMETIC AT ALL.  Speeds are only ever compared
    ([<=?], [=?]); nothing is added or negated, so every i64 input --
    including i64::MIN, which would panic a [Z.abs]/[Z.opp] in the checked
    build -- is safe.  This is why the guards are written two-sided
    ([-MAX <=? v && v <=? MAX]) instead of [Z.abs v <=? MAX]. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

(** Speeds in cm/s.  Park may engage below 0.3 m/s; a direction change
    (R<->D) below 1.5 m/s. *)
Definition P_ENGAGE_MAX : Z := 30.
Definition SHIFT_DIR_MAX : Z := 150.

Inductive gear := GPark | GReverse | GNeutral | GDrive.
Inductive mode := MPark | MReverse | MNeutral | MDrive | MFault.

Inductive event :=
  | EvShift (g : gear) (v : Z)   (* driver requests gear g at speed v *)
  | EvFault                      (* diagnostic trips *)
  | EvFaultClear (v : Z).        (* technician clears, at speed v *)

Definition gear_mode (g : gear) : mode :=
  match g with
  | GPark => MPark | GReverse => MReverse
  | GNeutral => MNeutral | GDrive => MDrive
  end.

(** May gear [g] engage at speed [v]?  (Two-sided comparisons; see header.) *)
Definition shift_allowed (g : gear) (v : Z) : bool :=
  match g with
  | GPark    => (- P_ENGAGE_MAX <=? v) && (v <=? P_ENGAGE_MAX)
  | GNeutral => true
  | GReverse => (- SHIFT_DIR_MAX <=? v) && (v <=? SHIFT_DIR_MAX)
  | GDrive   => (- SHIFT_DIR_MAX <=? v)   (* not rolling backwards fast *)
  end.

Definition apply_evt (m : mode) (e : event) : mode :=
  match e with
  | EvFault => MFault
  | EvFaultClear v =>
      match m with
      | MFault => if v =? 0 then MPark else MFault
      | _ => m
      end
  | EvShift g v =>
      match m with
      | MFault => MFault
      | _ => if shift_allowed g v then gear_mode g else m
      end
  end.

Definition run_events (m : mode) (es : list event) : mode :=
  fold_left apply_evt es m.

(** ** Interlock theorems (per transition) *)

Theorem park_interlock : forall m g v,
  m <> MPark ->
  apply_evt m (EvShift g v) = MPark ->
  - P_ENGAGE_MAX <= v <= P_ENGAGE_MAX.
Proof.
  intros m g v Hm H.
  unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *.
  destruct m; try congruence; destruct g; simpl in H;
    repeat match goal with
           | H0 : (if ?b then _ else _) = _ |- _ => destruct b eqn:E
           end;
    try congruence;
    try (apply andb_true_iff in E as [E1 E2];
         apply Z.leb_le in E1; apply Z.leb_le in E2;
         unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *; lia);
    try (apply Z.leb_le in E;
         unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *; lia).
Qed.

Theorem reverse_interlock : forall m g v,
  m <> MReverse ->
  apply_evt m (EvShift g v) = MReverse ->
  - SHIFT_DIR_MAX <= v <= SHIFT_DIR_MAX.
Proof.
  intros m g v Hm H.
  unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *.
  destruct m; try congruence; destruct g; simpl in H;
    repeat match goal with
           | H0 : (if ?b then _ else _) = _ |- _ => destruct b eqn:E
           end;
    try congruence;
    try (apply andb_true_iff in E as [E1 E2];
         apply Z.leb_le in E1; apply Z.leb_le in E2;
         unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *; lia);
    try (apply Z.leb_le in E;
         unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *; lia).
Qed.

Theorem drive_interlock : forall m g v,
  m <> MDrive ->
  apply_evt m (EvShift g v) = MDrive ->
  - SHIFT_DIR_MAX <= v.
Proof.
  intros m g v Hm H.
  unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *.
  destruct m; try congruence; destruct g; simpl in H;
    repeat match goal with
           | H0 : (if ?b then _ else _) = _ |- _ => destruct b eqn:E
           end;
    try congruence;
    try (apply andb_true_iff in E as [E1 E2];
         apply Z.leb_le in E1; apply Z.leb_le in E2;
         unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *; lia);
    try (apply Z.leb_le in E;
         unfold P_ENGAGE_MAX, SHIFT_DIR_MAX in *; lia).
Qed.

(** ** Fault handling *)

Theorem fault_absorbing : forall e,
  apply_evt MFault e <> MFault ->
  e = EvFaultClear 0 /\ apply_evt MFault e = MPark.
Proof.
  intros e H. destruct e as [g v | | v]; simpl in *.
  - congruence.
  - congruence.
  - destruct (v =? 0) eqn:Ev; [| congruence].
    apply Z.eqb_eq in Ev; subst. auto.
Qed.

Definition is_standstill_clear (e : event) : bool :=
  match e with EvFaultClear v => v =? 0 | _ => false end.

Theorem run_fault_sticky : forall es,
  forallb (fun e => negb (is_standstill_clear e)) es = true ->
  run_events MFault es = MFault.
Proof.
  unfold run_events.
  induction es as [| e es IH]; intros H; simpl; [reflexivity |].
  simpl in H. apply andb_true_iff in H as [He Hes].
  destruct e as [g v | | v]; simpl.
  - now apply IH.
  - now apply IH.
  - simpl in He. destruct (v =? 0); simpl in He; [discriminate |].
    now apply IH.
Qed.

(** Extraction entry point. *)
Definition drive_demo (es : list event) : mode := run_events MPark es.
