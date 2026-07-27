(** * RSS-style longitudinal safe distance, division-free

    The Responsibility-Sensitive Safety minimum following distance (the
    formal safety envelope popularized for AVs): a rear vehicle at speed
    [vr] behind a front vehicle at [vf] is safe at gap [d] iff even in the
    worst case -- rear accelerates at [a] for the response time [rho],
    then brakes at its WEAKEST [b], while the front brakes at its
    STRONGEST [B] -- no collision occurs:

        d  >=  vr*rho + a*rho^2/2 + (vr + rho*a)^2/(2b) - vf^2/(2B)

    Units: cm, cm/s, cm/s^2, and [rho] in DECISECONDS (0.1 s) so that
    realistic response times (0.1 s .. 5 s) are representable as integers.
    With rho in ds, vr*rho is in cm/10 and rho*a in (cm/s)/10, so the
    inequality is multiplied through by [200 * b * B > 0] to clear every
    denominator at once -- an EQUIVALENT polynomial inequality over the
    integers, division-free, exactly representable, and provable:

        200*b*B*d  >=  20*b*B*vr*rho + b*B*a*rho^2
                       + B*(10*vr + rho*a)^2 - 100*b*vf^2

    (Getting these scale factors wrong is exactly the class of bug the
    smoke tests caught in this file's first draft -- an integer-unit
    inconsistency that type-checks fine and quietly makes every verdict
    wrong.  The monotonicity theorems below survived it; the DEMO's
    physical sanity checks did not.  Both layers earn their keep.)

    Theorems:

    - [rss_monotone_distance]   : more gap never turns safe into unsafe.
    - [rss_antitone_rear_speed] : slowing the rear vehicle down never
      turns safe into unsafe.
    - [rss_monotone_front_speed]: a faster front vehicle never turns safe
      into unsafe.
      Together: the check is monotone in the direction physics says it
      must be -- a checker without these properties would flicker between
      verdicts as the situation strictly improves.
    - [rss_standstill_safe]     : a stationary, non-accelerating rear
      vehicle is safe at any nonnegative gap.
    - [rss_fits_i64]            : the proved domain.  With d <= 10 km,
      speeds <= 70 m/s, rho <= 5 s, accelerations in [1, 15 m/s^2],
      every product the margin computes is below 2^50 -- the bindings
      enforce exactly these bounds, and the checked build panics
      (contained) if they are bypassed.

    Scope honesty: this is the longitudinal, same-lane RSS check with
    worst-case constant accelerations; lateral RSS, cut-ins, and occlusion
    are out of scope.  The parameters (response time, braking envelopes)
    are inputs -- choosing them is regulatory/engineering judgment; the
    theorems say the CHECK is faithful and stable once they are chosen. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.

Local Open Scope Z_scope.

(** [rss_margin b B d vr vf rho a]: the safety margin, scaled by 2*b*B.
    Nonnegative iff the RSS inequality holds. *)
Definition rss_margin (b B d vr vf rho a : Z) : Z :=
  200 * b * B * d
  - (b * B * (20 * vr * rho + a * rho * rho)
     + B * (10 * vr + rho * a) * (10 * vr + rho * a)
     - 100 * b * (vf * vf)).

Definition rss_safe (b B d vr vf rho a : Z) : bool :=
  0 <=? rss_margin b B d vr vf rho a.

(** The parameter domain the bindings enforce. *)
Definition D_MAX : Z := 1000000.     (* 10 km  *)
Definition V_MAX : Z := 7000.        (* 70 m/s *)
Definition RHO_MAX : Z := 50.   (* 5 s *)
Definition ACC_MAX : Z := 1500.      (* 15 m/s^2 *)

Definition rss_dom (b B d vr vf rho a : Z) : Prop :=
  1 <= b <= ACC_MAX /\ 1 <= B <= ACC_MAX /\
  0 <= d <= D_MAX /\ 0 <= vr <= V_MAX /\ 0 <= vf <= V_MAX /\
  1 <= rho <= RHO_MAX /\ 0 <= a <= ACC_MAX.

(* ------------------------------------------------------------------ *)
(** ** Monotonicity: the verdict moves the way physics says it must *)

Theorem rss_monotone_distance : forall b B d d' vr vf rho a,
  1 <= b -> 1 <= B -> d <= d' ->
  rss_safe b B d vr vf rho a = true ->
  rss_safe b B d' vr vf rho a = true.
Proof.
  intros b B d d' vr vf rho a Hb HB Hd H.
  unfold rss_safe, rss_margin in *.
  apply Z.leb_le in H. apply Z.leb_le.
  assert (Hg : 200 * b * B * d <= 200 * b * B * d').
  { apply Z.mul_le_mono_nonneg_l; [nia | exact Hd]. }
  lia.
Qed.

Theorem rss_antitone_rear_speed : forall b B d vr vr' vf rho a,
  1 <= b -> 1 <= B -> 1 <= rho -> 0 <= a ->
  0 <= vr' <= vr ->
  rss_safe b B d vr vf rho a = true ->
  rss_safe b B d vr' vf rho a = true.
Proof.
  intros b B d vr vr' vf rho a Hb HB Hrho Ha Hvr H.
  unfold rss_safe, rss_margin in *.
  apply Z.leb_le in H. apply Z.leb_le.
  assert (Hsq : (10 * vr' + rho * a) * (10 * vr' + rho * a)
                <= (10 * vr + rho * a) * (10 * vr + rho * a))
    by (apply Z.mul_le_mono_nonneg; lia).
  assert (H1 : B * ((10 * vr' + rho * a) * (10 * vr' + rho * a))
               <= B * ((10 * vr + rho * a) * (10 * vr + rho * a)))
    by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (Ha1 : B * (10 * vr' + rho * a) * (10 * vr' + rho * a)
                = B * ((10 * vr' + rho * a) * (10 * vr' + rho * a))) by ring.
  assert (Ha2 : B * (10 * vr + rho * a) * (10 * vr + rho * a)
                = B * ((10 * vr + rho * a) * (10 * vr + rho * a))) by ring.
  assert (H2 : b * B * (20 * vr' * rho + a * rho * rho)
               <= b * B * (20 * vr * rho + a * rho * rho)).
  { apply Z.mul_le_mono_nonneg_l; nia. }
  lia.
Qed.

Theorem rss_monotone_front_speed : forall b B d vr vf vf' rho a,
  1 <= b -> 0 <= vf <= vf' ->
  rss_safe b B d vr vf rho a = true ->
  rss_safe b B d vr vf' rho a = true.
Proof.
  intros b B d vr vf vf' rho a Hb Hvf H.
  unfold rss_safe, rss_margin in *.
  apply Z.leb_le in H. apply Z.leb_le.
  assert (Hsq : vf * vf <= vf' * vf')
    by (apply Z.mul_le_mono_nonneg; lia).
  assert (H1 : b * (vf * vf) <= b * (vf' * vf')).
  { apply Z.mul_le_mono_nonneg_l; nia. }
  lia.
Qed.

(** A stationary, non-accelerating rear vehicle threatens nobody. *)
Theorem rss_standstill_safe : forall b B d vf rho,
  1 <= b -> 1 <= B -> 0 <= d -> 0 <= vf ->
  rss_safe b B d 0 vf rho 0 = true.
Proof.
  intros b B d vf rho Hb HB Hd Hvf.
  unfold rss_safe, rss_margin. apply Z.leb_le. nia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The proved i64 domain *)

Lemma bounded_mul : forall x y X Y,
  0 <= x <= X -> 0 <= y <= Y -> 0 <= x * y <= X * Y.
Proof. intros. nia. Qed.

Theorem rss_fits_i64 : forall b B d vr vf rho a,
  rss_dom b B d vr vf rho a ->
  - 1125899906842624 <= rss_margin b B d vr vf rho a <= 1125899906842624.
  (* +- 2^50: every term individually below ~2^49, sum with margin *)
Proof.
  intros b B d vr vf rho a (Hb & HB & Hd & Hvr & Hvf & Hrho & Ha).
  unfold rss_margin, D_MAX, V_MAX, RHO_MAX, ACC_MAX in *.
  assert (A1 : 0 <= b * B <= 1500 * 1500) by (apply bounded_mul; lia).
  assert (A2 : 0 <= b * B * d <= 1500 * 1500 * 1000000)
    by (apply bounded_mul; lia).
  assert (E1 : 200 * b * B * d = 200 * (b * B * d)) by ring.
  assert (A3 : 0 <= rho * a <= 50 * 1500) by (apply bounded_mul; lia).
  assert (Hin : 0 <= 10 * vr + rho * a <= 145000) by lia.
  assert (A4 : 0 <= (10 * vr + rho * a) * (10 * vr + rho * a)
               <= 145000 * 145000) by (apply bounded_mul; lia).
  assert (A5 : 0 <= B * ((10 * vr + rho * a) * (10 * vr + rho * a))
               <= 1500 * (145000 * 145000)) by (apply bounded_mul; lia).
  assert (E2 : B * (10 * vr + rho * a) * (10 * vr + rho * a)
               = B * ((10 * vr + rho * a) * (10 * vr + rho * a))) by ring.
  assert (A6 : 0 <= vf * vf <= 7000 * 7000) by (apply bounded_mul; lia).
  assert (A7 : 0 <= b * (vf * vf) <= 1500 * (7000 * 7000))
    by (apply bounded_mul; lia).
  assert (E3 : 100 * b * (vf * vf) = 100 * (b * (vf * vf))) by ring.
  assert (A8 : 0 <= vr * rho <= 7000 * 50) by (apply bounded_mul; lia).
  assert (A9 : 0 <= rho * rho <= 50 * 50) by (apply bounded_mul; lia).
  assert (A10 : 0 <= a * (rho * rho) <= 1500 * (50 * 50))
    by (apply bounded_mul; lia).
  assert (Hlin : 0 <= 20 * vr * rho + a * rho * rho <= 10750000).
  { assert (E4 : 20 * vr * rho = 20 * (vr * rho)) by ring.
    assert (E5 : a * rho * rho = a * (rho * rho)) by ring.
    lia. }
  assert (A11 : 0 <= b * B * (20 * vr * rho + a * rho * rho)
                <= 1500 * 1500 * 10750000).
  { apply bounded_mul; lia. }
  lia.
Qed.

(** Extraction entry point: verdict plus the (scaled) margin, which the
    caller can use as a graded severity signal. *)
Definition rss_demo (b B d vr vf rho a : Z) : bool * Z :=
  (rss_safe b B d vr vf rho a, rss_margin b B d vr vf rho a).
