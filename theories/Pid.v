(** * Integer PID controller with anti-windup, saturation proved

    Classical discrete PID in pure integer (fixed-point) arithmetic:

      integ' = clamp(-I_MAX, I_MAX, integ + e)          (anti-windup)
      raw    = kp*e + ki*integ' + kd*(e - prev)
      u      = clamp(-U_MAX, U_MAX, raw)                (actuator limit)

    Theorems, in two tiers that deliberately have DIFFERENT strengths:

    Unconditional (hold for every input, every gain -- designed out):
    - [output_saturated]  : -U_MAX <= u <= U_MAX.  The actuator command is
      bounded no matter what; a wild gain or sensor spike cannot command
      more than the hardware limit.
    - [integral_bounded]  : the integral state never escapes
      [-I_MAX, I_MAX] -- anti-windup as an invariant, not a hope.

    Conditional (the proved i64 domain):
    - [raw_fits_i64], [pre_clamp_fits_i64] : with |gains| <= G_MAX and
      |errors| <= E_MAX, every intermediate the formula computes fits i64.
      G_MAX = 2^15 and E_MAX = 2^31 give |raw| <= 2^48 + margin -- see the
      arithmetic in [raw_fits_i64].  The bindings enforce exactly these
      constants; outside them, the checked build panics (contained at the
      FFI) instead of wrapping.

    The two tiers matter: saturation alone does NOT make the computation
    safe, because [raw] is computed BEFORE the clamp -- the same
    evaluate-before-check obligation as the trading gate, discharged here
    by the domain theorems. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

Definition G_MAX : Z := 32768.               (* 2^15: max |gain| *)
Definition E_MAX : Z := 2147483648.          (* 2^31: max |error| *)
Definition I_MAX : Z := 2147483648.          (* 2^31: integral clamp *)
Definition U_MAX : Z := 1000000.             (* actuator authority *)
Definition i64_lo : Z := -9223372036854775808.
Definition i64_hi : Z := 9223372036854775807.

Definition clamp (lo hi x : Z) : Z := Z.min hi (Z.max lo x).

Record pid_state := mkPid { pid_integ : Z; pid_prev : Z }.

(** One step: returns (command, new state). *)
Definition pid_step (kp ki kd : Z) (st : pid_state) (e : Z)
  : Z * pid_state :=
  let integ' := clamp (- I_MAX) I_MAX (pid_integ st + e) in
  let raw := kp * e + ki * integ' + kd * (e - pid_prev st) in
  (clamp (- U_MAX) U_MAX raw, mkPid integ' e).

Fixpoint pid_run (kp ki kd : Z) (st : pid_state) (es : list Z)
  : list Z * pid_state :=
  match es with
  | [] => ([], st)
  | e :: rest =>
      let '(u, st') := pid_step kp ki kd st e in
      let '(us, stf) := pid_run kp ki kd st' rest in
      (u :: us, stf)
  end.

Definition pid_init : pid_state := mkPid 0 0.

(** ** Tier 1: unconditional saturation *)

Lemma clamp_bounds : forall lo hi x, lo <= hi -> lo <= clamp lo hi x <= hi.
Proof. intros. unfold clamp. lia. Qed.

Theorem output_saturated : forall kp ki kd st e,
  - U_MAX <= fst (pid_step kp ki kd st e) <= U_MAX.
Proof.
  intros. unfold pid_step. simpl.
  apply clamp_bounds. unfold U_MAX. lia.
Qed.

Theorem integral_bounded : forall kp ki kd st e,
  - I_MAX <= pid_integ (snd (pid_step kp ki kd st e)) <= I_MAX.
Proof.
  intros. unfold pid_step. simpl.
  apply clamp_bounds. unfold I_MAX. lia.
Qed.

(** ** Tier 2: the proved i64 domain for the intermediates *)

(** The pre-clamp integral sum. *)
Lemma pre_clamp_fits_i64 : forall st e,
  - I_MAX <= pid_integ st <= I_MAX ->
  - E_MAX <= e <= E_MAX ->
  i64_lo <= pid_integ st + e <= i64_hi.
Proof. unfold I_MAX, E_MAX, i64_lo, i64_hi. intros. lia. Qed.

(** Bounded times bounded is bounded (the workhorse). *)
Lemma mul_bound : forall a b A B,
  0 <= A -> 0 <= B -> - A <= a <= A -> - B <= b <= B ->
  - (A * B) <= a * b <= A * B.
Proof. intros. nia. Qed.

Theorem raw_fits_i64 : forall kp ki kd st e,
  - G_MAX <= kp <= G_MAX ->
  - G_MAX <= ki <= G_MAX ->
  - G_MAX <= kd <= G_MAX ->
  - I_MAX <= pid_integ st <= I_MAX ->
  - E_MAX <= pid_prev st <= E_MAX ->
  - E_MAX <= e <= E_MAX ->
  let integ' := clamp (- I_MAX) I_MAX (pid_integ st + e) in
  i64_lo <= kp * e + ki * integ' + kd * (e - pid_prev st) <= i64_hi.
Proof.
  intros kp ki kd st e Hkp Hki Hkd Hi Hp He integ'.
  assert (Hi' : - I_MAX <= integ' <= I_MAX)
    by (apply clamp_bounds; unfold I_MAX; lia).
  assert (H1 : - (G_MAX * E_MAX) <= kp * e <= G_MAX * E_MAX)
    by (apply mul_bound; unfold G_MAX, E_MAX in *; lia).
  assert (H2 : - (G_MAX * I_MAX) <= ki * integ' <= G_MAX * I_MAX)
    by (apply mul_bound; unfold G_MAX, I_MAX in *; lia).
  assert (H3 : - (G_MAX * (2 * E_MAX)) <= kd * (e - pid_prev st)
               <= G_MAX * (2 * E_MAX))
    by (apply mul_bound; unfold G_MAX, E_MAX in *; lia).
  unfold G_MAX, E_MAX, I_MAX, i64_lo, i64_hi in *. lia.
Qed.

(** The invariant threaded through a whole run: integral clamped, previous
    error inside the error domain. *)
Definition PidInv (st : pid_state) : Prop :=
  - I_MAX <= pid_integ st <= I_MAX /\ - E_MAX <= pid_prev st <= E_MAX.

Theorem pid_step_inv : forall kp ki kd st e,
  PidInv st -> - E_MAX <= e <= E_MAX ->
  PidInv (snd (pid_step kp ki kd st e)).
Proof.
  intros kp ki kd st e [Hi Hp] He. unfold pid_step, PidInv. simpl.
  split; [apply clamp_bounds; unfold I_MAX; lia | exact He].
Qed.

Theorem pid_run_inv : forall kp ki kd es st,
  PidInv st ->
  Forall (fun e => - E_MAX <= e <= E_MAX) es ->
  PidInv (snd (pid_run kp ki kd st es)).
Proof.
  intros kp ki kd es.
  induction es as [| e rest IH]; intros st HI HF; cbn [pid_run]; [exact HI |].
  inversion HF as [| ? ? He1 HFrest]; subst.
  destruct (pid_step kp ki kd st e) eqn:Hs.
  destruct (pid_run kp ki kd p rest) eqn:Hr. simpl.
  assert (Hinv' : PidInv p).
  { replace p with (snd (pid_step kp ki kd st e)) by (rewrite Hs; reflexivity).
    now apply pid_step_inv. }
  specialize (IH p Hinv' HFrest). rewrite Hr in IH. exact IH.
Qed.

(** Every emitted command over a run is saturated (unconditionally). *)
Theorem pid_run_outputs_saturated : forall kp ki kd es st,
  Forall (fun u => - U_MAX <= u <= U_MAX) (fst (pid_run kp ki kd st es)).
Proof.
  intros kp ki kd es.
  induction es as [| e rest IH]; intros st; cbn [pid_run]; [constructor |].
  destruct (pid_step kp ki kd st e) eqn:Hs.
  destruct (pid_run kp ki kd p rest) eqn:Hr. simpl.
  constructor.
  - replace z with (fst (pid_step kp ki kd st e)) by (rewrite Hs; reflexivity).
    apply output_saturated.
  - specialize (IH p). rewrite Hr in IH. exact IH.
Qed.

(** Extraction entry point. *)
Definition pid_demo (kp ki kd : Z) (es : list Z) : list Z * pid_state :=
  pid_run kp ki kd pid_init es.
