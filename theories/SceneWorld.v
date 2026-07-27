(** * World-frame ingestion for the scene checker: a domain the caller CAN
      get wrong

    [SceneModel.v] is total for any i64 input because its interface is
    ego-centric: every unary rule is a comparison on a raw field, and all
    arithmetic is gated behind validation.  This file adapts the SAME
    checker to the interface many real stacks actually have: upstream
    fusion delivers tracks in WORLD coordinates plus an ego pose, and the
    consistency rules are ego-relative -- so ingestion must compute

        dx = x_world - ego_x        (subtraction of two RAW inputs)
        rotate by ego heading       (negations of raw differences)

    BEFORE any envelope can be checked.  That arithmetic cannot be gated:
    it is what produces the values the gates need.  A caller domain is now
    unavoidable, and the discipline changes from "architecture makes it
    total" to "derive the domain, prove it, enforce it":

    - [SAFE_COORD] = 2^62 - 1 : the proved bound on every world coordinate,
      velocity, and ego-pose field.
    - [ingest_fits_i64] : under that bound, every intermediate of the
      transform -- both differences AND their negations -- lies within
      [-(2^63 - 1), 2^63 - 1].  The negation clause is the sharp edge:
      [i64::MIN] has no i64 negation, so the theorem shows the transform
      never produces a value whose negation is demanded but undefined
      (2 * SAFE_COORD = 2^63 - 2 keeps a margin of one).
    - [egress_ingest_id] : the pose transform is invertible (headings are
      quarter-turns), so ingestion loses no information -- checking in the
      ego frame is faithful to the world-frame scene.
    - [world_check_length], [world_scores_bounded] : the SceneModel
      guarantees lift through ingestion unchanged.

    Heading is quantized to quarter-turns (0..3, CCW from world +x to ego
    forward): rotation is then exact integer swapping/negation.  Arbitrary
    headings would need trigonometry and a fixed-point error analysis --
    out of scope, and orthogonal to the point of this file.

    Contrast with [SceneModel.v], deliberately: same rules, same theorems
    downstream, but THIS interface has a domain, the bindings must enforce
    it, and bypassing it turns into a contained panic in the checked build
    instead of silence.  When you can choose the interface, choose the one
    from [SceneModel.v]; when upstream chooses for you, this is the
    fallback discipline. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

From RocqRustExamples Require Import SceneModel.

Import ListNotations.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** The pose transform *)

(** Rotate a vector by [h] quarter-turns, world frame -> ego frame.
    [h] outside [0,3] is treated as identity; [check_scene_world] flags
    such scenes invalid ([pose_ok]) rather than guessing. *)
Definition rot (h x y : Z) : Z * Z :=
  if h =? 1 then (y, 0 - x)
  else if h =? 2 then (0 - x, 0 - y)
  else if h =? 3 then (0 - y, x)
  else (x, y).

Definition unrot (h x y : Z) : Z * Z :=
  if h =? 1 then (0 - y, x)
  else if h =? 2 then (0 - x, 0 - y)
  else if h =? 3 then (y, 0 - x)
  else (x, y).

(** World-frame object -> ego-frame object.  Positions are translated then
    rotated; velocities are ground velocities, so they are only rotated
    (a parked car stays a 0-speed object regardless of ego motion). *)
Definition ingest (px py ph : Z) (o : obj) : obj :=
  let '(rx, ry) := rot ph (o_x o - px) (o_y o - py) in
  let '(rvx, rvy) := rot ph (o_vx o) (o_vy o) in
  mkObj (o_class o) rx ry rvx rvy
        (o_w o) (o_l o) (o_conf o) (o_target o) (o_tl o).

Definition egress (px py ph : Z) (o : obj) : obj :=
  let '(ux, uy) := unrot ph (o_x o) (o_y o) in
  let '(uvx, uvy) := unrot ph (o_vx o) (o_vy o) in
  mkObj (o_class o) (ux + px) (uy + py) uvx uvy
        (o_w o) (o_l o) (o_conf o) (o_target o) (o_tl o).

(* ------------------------------------------------------------------ *)
(** ** The proved caller domain *)

Definition SAFE_COORD : Z := 4611686018427387903.   (* 2^62 - 1 *)
Definition i64_hi : Z := 9223372036854775807.

(** Under the domain, every intermediate of the transform -- the two
    differences and every negation the rotation may take -- fits i64,
    with a one-off margin below |i64::MIN| so no negation is ever
    undefined. *)
Theorem ingest_fits_i64 : forall px py o,
  - SAFE_COORD <= px <= SAFE_COORD ->
  - SAFE_COORD <= py <= SAFE_COORD ->
  - SAFE_COORD <= o_x o <= SAFE_COORD ->
  - SAFE_COORD <= o_y o <= SAFE_COORD ->
  - SAFE_COORD <= o_vx o <= SAFE_COORD ->
  - SAFE_COORD <= o_vy o <= SAFE_COORD ->
  - i64_hi <= o_x o - px <= i64_hi /\
  - i64_hi <= o_y o - py <= i64_hi /\
  - i64_hi <= 0 - (o_x o - px) <= i64_hi /\
  - i64_hi <= 0 - (o_y o - py) <= i64_hi /\
  - i64_hi <= 0 - o_vx o <= i64_hi /\
  - i64_hi <= 0 - o_vy o <= i64_hi.
Proof. unfold SAFE_COORD, i64_hi. intros. lia. Qed.

(** The transform is lossless: egress inverts ingest for any valid
    heading, so ego-frame checking is faithful to the world scene. *)
Theorem egress_ingest_id : forall px py ph o,
  0 <= ph <= 3 ->
  egress px py ph (ingest px py ph o) = o.
Proof.
  intros px py ph o Hph.
  assert (H : ph = 0 \/ ph = 1 \/ ph = 2 \/ ph = 3) by lia.
  destruct H as [-> | [-> | [-> | ->]]];
    destruct o; unfold ingest, egress, rot, unrot; cbn;
    f_equal; lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The world-frame checker: ingest, then the verified checker *)

Definition check_scene_world (rd : road)
                             (px py ph pvx pvy : Z)
                             (objs : list obj) : report :=
  let pose_ok := inb 0 3 ph in
  let '(evx, _) := rot ph pvx pvy in       (* ego longitudinal speed *)
  let r := check_scene rd evx (map (ingest px py ph) objs) in
  mkReport (pose_ok && rp_scene_ok r) (rp_entries r).

(** The SceneModel guarantees lift through ingestion. *)

Theorem world_check_length : forall rd px py ph pvx pvy objs,
  length (rp_entries (check_scene_world rd px py ph pvx pvy objs))
  = length objs.
Proof.
  intros. unfold check_scene_world.
  destruct (rot ph pvx pvy) as [evx evy]. cbn [rp_entries].
  now rewrite check_length, length_map.
Qed.

Lemma scene_scores_bounded : forall rd v objs,
  Forall (fun e => 0 <= en_score e <= 100)
         (rp_entries (check_scene rd v objs)).
Proof.
  intros. unfold check_scene. cbn [rp_entries].
  apply Forall_forall. intros e He.
  apply in_map_iff in He as [[i o] [Heq _]].
  subst e. apply score_bounds.
Qed.

Theorem world_scores_bounded : forall rd px py ph pvx pvy objs,
  Forall (fun e => 0 <= en_score e <= 100)
         (rp_entries (check_scene_world rd px py ph pvx pvy objs)).
Proof.
  intros. unfold check_scene_world.
  destruct (rot ph pvx pvy) as [evx evy]. cbn [rp_entries].
  apply scene_scores_bounded.
Qed.

(** Extraction entry point. *)
Definition scene_world_demo (rd : road) (px py ph pvx pvy : Z)
                            (objs : list obj) : report :=
  check_scene_world rd px py ph pvx pvy objs.
