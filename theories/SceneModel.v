(** * ADAS scene model with plausibility / consistency checking

    An ego-centric scene for a level-5 stack: a road model, the ego state,
    and a list of detected objects (vehicles, the ACC target, pedestrians,
    bicycles, traffic signs, traffic lights).  The checker's PURPOSE is to
    invalidate false positives and flag low-confidence detections -- with a
    citable rule for every downgrade.

    Units: positions cm (x forward, y left, ego at origin), speeds cm/s,
    confidence percent, curvature bounded in 1e-9/cm (participates in
    validation only in this version; lateral positions are interpreted in a
    road-aligned frame).

    ** Rule catalog (bit = position in the per-object violation mask)

    Hard rules (physically impossible -> the object is Implausible):
      0  ENV_DIM    class dimension envelope (a 5 m-wide pedestrian is not
                    a pedestrian)
      1  ENV_SPEED  class speed envelope, incl. |vy| <= 5 m/s for vehicles
                    (cars do not translate sideways) and near-static signs
                    and lights
      2  ENV_FOV    inside the sensor field of view/range (the sensor
                    cannot have produced a detection at 1 km)
      3  ENV_CONF   confidence in [0, 100] (malformed input)
      4  TGT_CLASS  the ACC target must be a vehicle
      5  OVERLAP    deep bounding-box interpenetration with another
                    validated object -- the LOWER-PRIORITY one is killed

    Soft rules (unusual -> confidence penalty):
      7  OFFROAD_VEHICLE   vehicle far outside the road surface      (-15)
      8  OFFROAD_BIKE      bicycle far outside the road surface      (-15)
      9  PED_ON_FAST_ROAD  pedestrian on the carriageway of a road
                           with limit >= 22 m/s                      (-25)
      10 FURNITURE_IN_ROAD sign or light in the middle of the road   (-20)
      11 LIGHT_CONFLICT    two co-located lights showing red vs
                           green -- lower-priority one flagged       (-25)
      12 DUPLICATE         same class, nearly same pose and velocity
                           as a higher-priority object               (-30)
      13 TGT_BEHIND        ACC target behind the ego                 (-20)
      14 TGT_OFFLANE       ACC target far outside the ego lane       (-15)
      15 TGT_EXTRA         more than one target -- all but the best  (-25)

    Verdict: any hard rule -> Implausible (score 0); otherwise
    score = max(0, confidence - penalties), Confirmed iff score >= 60.

    ** What is proved

    - [check_length]          : one entry per object (FFI sizing).
    - [hard_env_implausible]  : an envelope violation forces Implausible --
      no aggregation path can resurrect a physically impossible object.
    - [clean_confirmed]       : if nothing fired, the score IS the sensor
      confidence -- the checker never manufactures doubt; every downgrade
      is backed by a rule in the mask.
    - [score_bounds]          : 0 <= score <= 100, for EVERY input.
    - [score_le_conf]         : score never exceeds sensor confidence.
    - [loser_antisym] + [dup_at_most_one], [overlap_at_most_one] : the
      pair rules kill/penalize at most ONE of any pair -- a duplicate or
      overlap can never eliminate BOTH copies of a real object.
    - [overlap_close_sym]     : the geometric overlap predicate is
      symmetric (which side gets penalized is decided by priority, not by
      evaluation order).
    - [validated_bounds] + [pair_arith_fits] : the overflow architecture.
      Unary rules use COMPARISONS ONLY (total on any i64, including
      i64::MIN -- no abs, no negation of raw input); every subtraction or
      product in the pair rules happens strictly AFTER both operands passed
      the envelope, and on validated values every such intermediate is
      within +-2^17.  Validate-then-compute: the checker is total by
      construction, not by a domain the caller must respect.  *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Scene data *)

Inductive oclass := CVehicle | CPedestrian | CBicycle | CSign | CLight.

(** Traffic-light state: 0 none/unknown, 1 red, 2 yellow, 3 green
    (plain [Z] so the record stays uniform across classes). *)
Record obj := mkObj {
  o_class : oclass;
  o_x : Z; o_y : Z;          (* position, cm            *)
  o_vx : Z; o_vy : Z;        (* velocity, cm/s          *)
  o_w : Z; o_l : Z;          (* width / length, cm      *)
  o_conf : Z;                (* sensor confidence, %    *)
  o_target : bool;           (* ACC target flag         *)
  o_tl : Z                   (* traffic-light state     *)
}.

Record road := mkRoad {
  r_lanes : Z;               (* 1..6                    *)
  r_lane_w : Z;              (* cm, 250..500            *)
  r_curv : Z;                (* bounded, 1e-9/cm        *)
  r_limit : Z                (* speed limit, cm/s       *)
}.

Inductive verdict := VConfirmed | VLow | VImplausible.

Record entry := mkEntry { en_ver : verdict; en_score : Z; en_mask : Z }.

Record report := mkReport { rp_scene_ok : bool; rp_entries : list entry }.

(* ------------------------------------------------------------------ *)
(** ** Hard envelopes: comparisons only, total on any i64 *)

Definition FOV_X : Z := 20000.   (* 200 m *)
Definition FOV_Y : Z := 5000.    (*  50 m *)

(** [inb lo hi v]: two-sided compare -- never negates or abs-es [v]. *)
Definition inb (lo hi v : Z) : bool := (lo <=? v) && (v <=? hi).

Definition dim_ok (o : obj) : bool :=
  match o_class o with
  | CPedestrian => inb 20 150 (o_w o)  && inb 20 150 (o_l o)
  | CBicycle    => inb 30 120 (o_w o)  && inb 100 250 (o_l o)
  | CVehicle    => inb 120 300 (o_w o) && inb 200 2500 (o_l o)
  | CSign       => inb 5 200 (o_w o)   && inb 5 200 (o_l o)
  | CLight      => inb 5 200 (o_w o)   && inb 5 200 (o_l o)
  end.

Definition speed_ok (o : obj) : bool :=
  match o_class o with
  | CPedestrian => inb (-1500) 1500 (o_vx o) && inb (-1500) 1500 (o_vy o)
  | CBicycle    => inb (-2500) 2500 (o_vx o) && inb (-2500) 2500 (o_vy o)
  | CVehicle    => inb (-7000) 7000 (o_vx o) && inb (-500) 500 (o_vy o)
  | CSign       => inb (-300) 300 (o_vx o)   && inb (-300) 300 (o_vy o)
  | CLight      => inb (-300) 300 (o_vx o)   && inb (-300) 300 (o_vy o)
  end.

Definition fov_ok (o : obj) : bool :=
  inb (- FOV_X) FOV_X (o_x o) && inb (- FOV_Y) FOV_Y (o_y o).

Definition conf_ok (o : obj) : bool := inb 0 100 (o_conf o).

Definition tgt_class_ok (o : obj) : bool :=
  if o_target o
  then match o_class o with CVehicle => true | _ => false end
  else true.

Definition envelope_ok (o : obj) : bool :=
  dim_ok o && speed_ok o && fov_ok o && conf_ok o && tgt_class_ok o.

(** Scene-level input validation (comparisons only). *)
Definition road_ok (rd : road) : bool :=
  inb 1 6 (r_lanes rd) && inb 250 500 (r_lane_w rd)
  && inb (-200000) 200000 (r_curv rd) && inb 0 4000 (r_limit rd).

Definition ego_ok (ego_v : Z) : bool := inb (-3000) 7000 ego_v.

(* ------------------------------------------------------------------ *)
(** ** Pair rules: arithmetic, gated behind validation *)

(** Absolute value of a VALIDATED quantity (bounded, so [0 - x] is safe;
    never applied to raw input). *)
Definition zabs (x : Z) : Z := if x <? 0 then 0 - x else x.

(** Priority: higher confidence wins; ties broken by position (lower
    index wins).  [loser ci i cj j] = object at position i loses. *)
Definition loser (ci : Z) (i : nat) (cj : Z) (j : nat) : bool :=
  (ci <? cj) || ((ci =? cj) && (Nat.ltb j i)).

(** Deep interpenetration of axis-aligned footprints (validated objs). *)
Definition PEN : Z := 60.  (* required penetration, cm, per axis *)

Definition overlap_close (oi oj : obj) : bool :=
  (2 * zabs (o_x oi - o_x oj) + PEN <? o_l oi + o_l oj)
  && (2 * zabs (o_y oi - o_y oj) + PEN <? o_w oi + o_w oj).

Definition dynamic (o : obj) : bool :=
  match o_class o with CVehicle | CPedestrian | CBicycle => true | _ => false end.

(** Same class, nearly same pose and velocity. *)
Definition same_class (a b : oclass) : bool :=
  match a, b with
  | CVehicle, CVehicle | CPedestrian, CPedestrian | CBicycle, CBicycle
  | CSign, CSign | CLight, CLight => true
  | _, _ => false
  end.

Definition dup_close (oi oj : obj) : bool :=
  same_class (o_class oi) (o_class oj)
  && (zabs (o_x oi - o_x oj) <=? 150) && (zabs (o_y oi - o_y oj) <=? 150)
  && (zabs (o_vx oi - o_vx oj) <=? 200) && (zabs (o_vy oi - o_vy oj) <=? 200).

(** Co-located lights showing contradictory states (red vs green). *)
Definition light_conflict (oi oj : obj) : bool :=
  match o_class oi, o_class oj with
  | CLight, CLight =>
      (zabs (o_x oi - o_x oj) <=? 300) && (zabs (o_y oi - o_y oj) <=? 300)
      && (((o_tl oi =? 1) && (o_tl oj =? 3))
          || ((o_tl oi =? 3) && (o_tl oj =? 1)))
  | _, _ => false
  end.

(* ------------------------------------------------------------------ *)
(** ** Road-relative soft rules (gated on road_ok and envelope_ok) *)

Definition road_width (rd : road) : Z := r_lanes rd * r_lane_w rd.

Definition offroad (rd : road) (o : obj) : bool :=
  road_width rd + 200 <? 2 * zabs (o_y o).

Definition on_carriageway (rd : road) (o : obj) : bool :=
  2 * zabs (o_y o) <? road_width rd.

Definition soft_offroad_vehicle (rd : road) (o : obj) : bool :=
  match o_class o with CVehicle => offroad rd o | _ => false end.

Definition soft_offroad_bike (rd : road) (o : obj) : bool :=
  match o_class o with CBicycle => offroad rd o | _ => false end.

Definition soft_ped_fast_road (rd : road) (o : obj) : bool :=
  match o_class o with
  | CPedestrian => on_carriageway rd o && (2200 <=? r_limit rd)
  | _ => false
  end.

Definition soft_furniture_in_road (rd : road) (o : obj) : bool :=
  match o_class o with
  | CSign | CLight => 2 * zabs (o_y o) + 100 <? road_width rd
  | _ => false
  end.

Definition soft_tgt_behind (o : obj) : bool :=
  o_target o && (o_x o <=? 0).

Definition soft_tgt_offlane (rd : road) (o : obj) : bool :=
  o_target o && (3 * r_lane_w rd <? 2 * zabs (o_y o)).

(* ------------------------------------------------------------------ *)
(** ** The checker *)

(** Pair-scan accumulator: does any validated partner overlap us (and
    win), duplicate us (and win), or contradict our light state (and
    win)?  Booleans, so the mask gets each bit at most once no matter how
    many pairs fire. *)
Record pacc := mkP { p_ovl : bool; p_dup : bool; p_cfl : bool }.

Definition pair_step (i : nat) (oi : obj) (acc : pacc)
                     (jo : nat * obj) : pacc :=
  let '(j, oj) := jo in
  if Nat.eqb i j then acc
  else if negb (envelope_ok oj) then acc
  else
    let lose := loser (o_conf oi) i (o_conf oj) j in
    mkP (p_ovl acc
          || (dynamic oi && dynamic oj && overlap_close oi oj && lose))
        (p_dup acc || (dup_close oi oj && lose))
        (p_cfl acc || (light_conflict oi oj && lose)).

Definition pair_scan (i : nat) (oi : obj) (iobjs : list (nat * obj)) : pacc :=
  fold_left (pair_step i oi) iobjs (mkP false false false).

Definition bit (b : bool) (k : Z) : Z := if b then k else 0.
Definition pen (b : bool) (k : Z) : Z := if b then k else 0.

(** Is this validated target the best one (highest priority)?  A target
    at position i is EXTRA iff some other validated target beats it. *)
Definition beaten_as_target (i : nat) (oi : obj)
                            (iobjs : list (nat * obj)) : bool :=
  existsb (fun '(j, oj) =>
             negb (Nat.eqb i j) && envelope_ok oj && o_target oj
             && loser (o_conf oi) i (o_conf oj) j)
          iobjs.

Definition finalize (hard : bool) (conf pens mask : Z) : entry :=
  if hard then mkEntry VImplausible 0 mask
  else
    let score := Z.max 0 (conf - pens) in
    mkEntry (if 60 <=? score then VConfirmed else VLow) score mask.

Definition check_one (rok : bool) (rd : road) (iobjs : list (nat * obj))
                     (i : nat) (o : obj) : entry :=
  if negb (envelope_ok o) then
    (* report exactly which envelope failed, then stop: no arithmetic on
       unvalidated data *)
    mkEntry VImplausible 0
      (bit (negb (dim_ok o)) 1 + bit (negb (speed_ok o)) 2
       + bit (negb (fov_ok o)) 4 + bit (negb (conf_ok o)) 8
       + bit (negb (tgt_class_ok o)) 16)
  else
    let pa := pair_scan i o iobjs in
    let b_orv := rok && soft_offroad_vehicle rd o in
    let b_orb := rok && soft_offroad_bike rd o in
    let b_ped := rok && soft_ped_fast_road rd o in
    let b_fur := rok && soft_furniture_in_road rd o in
    let b_beh := soft_tgt_behind o in
    let b_off := rok && soft_tgt_offlane rd o in
    let b_ext := o_target o && beaten_as_target i o iobjs in
    let pens :=
      pen b_orv 15 + pen b_orb 15 + pen b_ped 25 + pen b_fur 20
      + pen (p_cfl pa) 25 + pen (p_dup pa) 30
      + pen b_beh 20 + pen b_off 15 + pen b_ext 25 in
    let mask :=
      bit (p_ovl pa) 32
      + bit b_orv 128 + bit b_orb 256 + bit b_ped 512 + bit b_fur 1024
      + bit (p_cfl pa) 2048 + bit (p_dup pa) 4096
      + bit b_beh 8192 + bit b_off 16384 + bit b_ext 32768 in
    finalize (p_ovl pa) (o_conf o) pens mask.

Fixpoint index_from (k : nat) (l : list obj) : list (nat * obj) :=
  match l with
  | [] => []
  | o :: r => (k, o) :: index_from (S k) r
  end.

Definition check_scene (rd : road) (ego_v : Z) (objs : list obj) : report :=
  let rok := road_ok rd && ego_ok ego_v
             && Nat.leb (length objs) 128 in
  let iobjs := index_from 0%nat objs in
  mkReport rok (map (fun '(i, o) => check_one rok rd iobjs i o) iobjs).

(* ------------------------------------------------------------------ *)
(** ** Theorems *)

Lemma index_from_length : forall l k, length (index_from k l) = length l.
Proof. induction l; intros; simpl; auto. Qed.

(** One entry per object. *)
Theorem check_length : forall rd v objs,
  length (rp_entries (check_scene rd v objs)) = length objs.
Proof.
  intros. unfold check_scene. cbn [rp_entries].
  now rewrite length_map, index_from_length.
Qed.

(** Envelope violations are fatal, whatever else is in the scene. *)
Theorem hard_env_implausible : forall rok rd iobjs i o,
  envelope_ok o = false ->
  en_ver (check_one rok rd iobjs i o) = VImplausible.
Proof. intros. unfold check_one. now rewrite H. Qed.

(** The score is bounded for EVERY input -- no hypotheses at all. *)
Lemma finalize_score_bounds : forall h c p m,
  0 <= c <= 100 -> 0 <= p ->
  0 <= en_score (finalize h c p m) <= 100.
Proof.
  intros h c p m Hc Hp. unfold finalize.
  destruct h; cbn [en_score]; lia.
Qed.

Lemma pen_nonneg : forall b k, 0 <= k -> 0 <= pen b k.
Proof. intros [] k Hk; cbn; lia. Qed.

Theorem score_bounds : forall rok rd iobjs i o,
  0 <= en_score (check_one rok rd iobjs i o) <= 100.
Proof.
  intros. unfold check_one.
  destruct (negb (envelope_ok o)) eqn:He; cbn [en_score]; [lia |].
  apply negb_false_iff in He.
  assert (Hc : 0 <= o_conf o <= 100).
  { unfold envelope_ok, conf_ok, inb in He.
    repeat (apply andb_true_iff in He as [He ?]).
    repeat match goal with
           | H : (_ && _)%bool = true |- _ =>
               apply andb_true_iff in H as [? ?]
           end.
    match goal with
    | H1 : (0 <=? o_conf o) = true, H2 : (o_conf o <=? 100) = true |- _ =>
        apply Z.leb_le in H1; apply Z.leb_le in H2; lia
    end. }
  apply finalize_score_bounds; [exact Hc |].
  repeat apply Z.add_nonneg_nonneg; apply pen_nonneg; lia.
Qed.

(** The checker never raises confidence. *)
Theorem score_le_conf : forall rok rd iobjs i o,
  envelope_ok o = true ->
  en_score (check_one rok rd iobjs i o) <= o_conf o.
Proof.
  intros rok rd iobjs i o He. unfold check_one.
  rewrite He. cbn [negb].
  assert (Hc : 0 <= o_conf o <= 100).
  { unfold envelope_ok, conf_ok, inb in He.
    repeat (apply andb_true_iff in He as [He ?]).
    repeat match goal with
           | H : (_ && _)%bool = true |- _ =>
               apply andb_true_iff in H as [? ?]
           end.
    match goal with
    | H1 : (0 <=? o_conf o) = true, H2 : (o_conf o <=? 100) = true |- _ =>
        apply Z.leb_le in H1; apply Z.leb_le in H2; lia
    end. }
  assert (Hp : 0 <=
    pen (rok && soft_offroad_vehicle rd o) 15
    + pen (rok && soft_offroad_bike rd o) 15
    + pen (rok && soft_ped_fast_road rd o) 25
    + pen (rok && soft_furniture_in_road rd o) 20
    + pen (p_cfl (pair_scan i o iobjs)) 25
    + pen (p_dup (pair_scan i o iobjs)) 30
    + pen (soft_tgt_behind o) 20
    + pen (rok && soft_tgt_offlane rd o) 15
    + pen (o_target o && beaten_as_target i o iobjs) 25)
    by (repeat apply Z.add_nonneg_nonneg; apply pen_nonneg; lia).
  unfold finalize.
  destruct (p_ovl (pair_scan i o iobjs)); cbn [en_score]; lia.
Qed.

(** No rule fired => the score IS the sensor confidence: the checker
    only ever downgrades WITH a citable rule. *)
Theorem clean_confirmed : forall rok rd iobjs i o,
  envelope_ok o = true ->
  en_mask (check_one rok rd iobjs i o) = 0 ->
  en_score (check_one rok rd iobjs i o) = o_conf o /\
  (60 <= o_conf o -> en_ver (check_one rok rd iobjs i o) = VConfirmed).
Proof.
  intros rok rd iobjs i o He Hm.
  unfold check_one in *. rewrite He in *. cbn [negb] in *.
  assert (Hc : 0 <= o_conf o <= 100).
  { unfold envelope_ok, conf_ok, inb in He.
    repeat (apply andb_true_iff in He as [He ?]).
    repeat match goal with
           | H : (_ && _)%bool = true |- _ =>
               apply andb_true_iff in H as [? ?]
           end.
    match goal with
    | H1 : (0 <=? o_conf o) = true, H2 : (o_conf o <=? 100) = true |- _ =>
        apply Z.leb_le in H1; apply Z.leb_le in H2; lia
    end. }
  (* a zero mask forces every contributing bool to false *)
  unfold finalize in *.
  destruct (p_ovl (pair_scan i o iobjs)) eqn:B0;
  destruct (rok && soft_offroad_vehicle rd o) eqn:B1;
  destruct (rok && soft_offroad_bike rd o) eqn:B2;
  destruct (rok && soft_ped_fast_road rd o) eqn:B3;
  destruct (rok && soft_furniture_in_road rd o) eqn:B4;
  destruct (p_cfl (pair_scan i o iobjs)) eqn:B5;
  destruct (p_dup (pair_scan i o iobjs)) eqn:B6;
  destruct (soft_tgt_behind o) eqn:B7;
  destruct (rok && soft_tgt_offlane rd o) eqn:B8;
  destruct (o_target o && beaten_as_target i o iobjs) eqn:B9;
  cbn [bit pen en_mask en_score en_ver] in *; try lia.
  split.
  - lia.
  - intros H60.
    replace (Z.max 0 (o_conf o - (0+0+0+0+0+0+0+0+0))) with (o_conf o) by lia.
    replace (60 <=? o_conf o) with true by (symmetry; apply Z.leb_le; lia).
    reflexivity.
Qed.

(** ** Pair fairness: at most one of a pair is ever penalized *)

Theorem loser_antisym : forall ci i cj j,
  (i <> j)%nat ->
  loser ci i cj j = true -> loser cj j ci i = false.
Proof.
  intros ci i cj j Hij H. unfold loser in *.
  apply orb_true_iff in H as [H | H].
  - apply Z.ltb_lt in H. apply orb_false_iff. split.
    + apply Z.ltb_ge. lia.
    + apply andb_false_iff. left. apply Z.eqb_neq. lia.
  - apply andb_true_iff in H as [H1 H2].
    apply Z.eqb_eq in H1. apply Nat.ltb_lt in H2.
    apply orb_false_iff. split.
    + apply Z.ltb_ge. lia.
    + apply andb_false_iff. right. apply Nat.ltb_ge. lia.
Qed.

(** The geometric predicates are symmetric... *)
Theorem overlap_close_sym : forall a b,
  overlap_close a b = overlap_close b a.
Proof.
  intros a b. unfold overlap_close, zabs.
  repeat match goal with |- context [?x - ?y] => idtac end.
  destruct (o_x a - o_x b <? 0) eqn:E1;
  destruct (o_x b - o_x a <? 0) eqn:E2;
  destruct (o_y a - o_y b <? 0) eqn:E3;
  destruct (o_y b - o_y a <? 0) eqn:E4;
  repeat match goal with
         | H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
         | H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
         end;
  repeat (f_equal; try lia).
Qed.

(** ... so with antisymmetric priority, a duplicate/overlap pair can
    never lose BOTH members: the winner's own scan cannot fire. *)
Theorem dup_at_most_one : forall i j oi oj,
  (i <> j)%nat ->
  (dup_close oi oj && loser (o_conf oi) i (o_conf oj) j)%bool = true ->
  (dup_close oj oi && loser (o_conf oj) j (o_conf oi) i)%bool = false.
Proof.
  intros i j oi oj Hij H.
  apply andb_true_iff in H as [_ HL].
  apply andb_false_iff. right. now apply loser_antisym.
Qed.

Theorem overlap_at_most_one : forall i j oi oj,
  (i <> j)%nat ->
  (overlap_close oi oj && loser (o_conf oi) i (o_conf oj) j)%bool = true ->
  (overlap_close oj oi && loser (o_conf oj) j (o_conf oi) i)%bool = false.
Proof.
  intros i j oi oj Hij H.
  apply andb_true_iff in H as [_ HL].
  apply andb_false_iff. right. now apply loser_antisym.
Qed.

(** ** The overflow architecture: validate, then compute *)

Lemma inb_bounds : forall lo hi v, inb lo hi v = true -> lo <= v <= hi.
Proof.
  intros lo hi v H. unfold inb in H.
  apply andb_true_iff in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

(** What passing the envelope guarantees numerically. *)
Theorem validated_bounds : forall o,
  envelope_ok o = true ->
  - FOV_X <= o_x o <= FOV_X /\ - FOV_Y <= o_y o <= FOV_Y /\
  - 7000 <= o_vx o <= 7000 /\ - 7000 <= o_vy o <= 7000 /\
  5 <= o_w o <= 2500 /\ 5 <= o_l o <= 2500 /\
  0 <= o_conf o <= 100.
Proof.
  intros o He.
  unfold envelope_ok in He.
  repeat (apply andb_true_iff in He as [He ?]).
  unfold fov_ok in *.
  match goal with
  | H : (inb (- FOV_X) FOV_X (o_x o) && inb (- FOV_Y) FOV_Y (o_y o))%bool
        = true |- _ =>
      apply andb_true_iff in H as [Hx Hy];
      apply inb_bounds in Hx; apply inb_bounds in Hy
  end.
  unfold conf_ok in *.
  match goal with
  | H : inb 0 100 (o_conf o) = true |- _ => apply inb_bounds in H
  end.
  unfold dim_ok, speed_ok in *.
  destruct (o_class o);
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_true_iff in H as [? ?]
           | H : inb _ _ _ = true |- _ => apply inb_bounds in H
           end;
    unfold FOV_X, FOV_Y in *; repeat split; lia.
Qed.

(** Every intermediate the pair rules compute on validated objects is
    tiny -- nowhere near the i64 edge. *)
Theorem pair_arith_fits : forall a b,
  envelope_ok a = true -> envelope_ok b = true ->
  - 131072 <= o_x a - o_x b <= 131072 /\
  - 131072 <= o_y a - o_y b <= 131072 /\
  - 131072 <= o_vx a - o_vx b <= 131072 /\
  - 131072 <= o_vy a - o_vy b <= 131072 /\
  0 <= o_l a + o_l b <= 131072 /\
  0 <= o_w a + o_w b <= 131072 /\
  0 <= 2 * zabs (o_x a - o_x b) + PEN <= 131072.
Proof.
  intros a b Ha Hb.
  apply validated_bounds in Ha. apply validated_bounds in Hb.
  unfold FOV_X, FOV_Y in *. unfold zabs, PEN.
  destruct (o_x a - o_x b <? 0) eqn:E;
    [apply Z.ltb_lt in E | apply Z.ltb_ge in E]; repeat split; lia.
Qed.

(** Extraction entry point. *)
Definition scene_demo (rd : road) (ego_v : Z) (objs : list obj) : report :=
  check_scene rd ego_v objs.
