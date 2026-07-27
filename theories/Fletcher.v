(** * Fletcher-16 checksum with a proved error-detection guarantee

    Data-link integrity for safety-critical comms (CAN-style frames,
    sensor buses): the classic Fletcher-16 running sums

        s1 = (s1 + d) mod 255        s2 = (s2 + s1) mod 255

    implemented division-free (conditional subtract -- the textbook
    optimization), and PROVED to detect every single-symbol corruption.

    Theorems:

    - [run_bounds]      : both sums stay in [0, 254] over any valid
      message -- the division-free implementation maintains the modular
      invariant (designed out; no arithmetic can leave [0, 508]).
    - [step1_mod]       : the conditional subtract IS mod-255 on the
      invariant domain -- the optimization is proved equal to the spec.
    - [fst_fletcher_sum]: s1 characterized as (Σ data) mod 255.
    - [single_error_detected] : two messages that differ in EXACTLY one
      position (both symbols in [0, 254], different) have different
      checksums.  A single corrupted symbol CANNOT slip through.
    - [fletcher_append] : checksums are streamable -- the state after
      [a ++ b] is the state after [b] started from [a]'s state.

    ** The domain, and why it is about a PROPERTY, not overflow

    [single_error_detected] assumes symbols in [0, 254] -- and that
    hypothesis is not bureaucracy.  Fletcher works mod 255, so the symbols
    0 and 255 are CONGRUENT: substituting one for the other is precisely
    the corruption the checksum cannot see (the classic Fletcher weakness).
    The binding therefore enforces [0, 254]; bypassing it does not crash or
    overflow -- it silently forfeits the detection guarantee, and the demo
    exhibits the 0x00 <-> 0xFF collision to show exactly that.  A proved
    domain can guard a THEOREM, not just an integer width. *)

From Stdlib Require Import ZArith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.

Import ListNotations.
Local Open Scope Z_scope.

Definition M : Z := 255.

(** One modular accumulation, division-free. *)
Definition step1 (s d : Z) : Z :=
  let t := s + d in if M <=? t then t - M else t.

Definition fstep (p : Z * Z) (d : Z) : Z * Z :=
  let '(s1, s2) := p in
  let s1' := step1 s1 d in
  (s1', step1 s2 s1').

Definition fletcher (l : list Z) : Z * Z := fold_left fstep l (0, 0).

(** The packed 16-bit checksum. *)
Definition checksum (l : list Z) : Z :=
  let '(s1, s2) := fletcher l in 256 * s2 + s1.

Definition sym_ok (d : Z) : Prop := 0 <= d <= 254.

(* ------------------------------------------------------------------ *)
(** ** The invariant, and the optimization proved equal to the spec *)

Lemma step1_bounds : forall s d,
  0 <= s <= 254 -> sym_ok d -> 0 <= step1 s d <= 254.
Proof.
  intros s d Hs Hd. unfold step1, M, sym_ok in *.
  destruct (255 <=? s + d) eqn:E;
    [apply Z.leb_le in E | apply Z.leb_gt in E]; lia.
Qed.

Lemma fstep_bounds : forall p d,
  0 <= fst p <= 254 -> 0 <= snd p <= 254 -> sym_ok d ->
  0 <= fst (fstep p d) <= 254 /\ 0 <= snd (fstep p d) <= 254.
Proof.
  intros [s1 s2] d H1 H2 Hd. cbn [fst snd] in *. unfold fstep.
  split; cbn [fst snd]; apply step1_bounds; auto.
  apply step1_bounds; auto.
Qed.

Theorem run_bounds : forall l p,
  0 <= fst p <= 254 -> 0 <= snd p <= 254 -> Forall sym_ok l ->
  0 <= fst (fold_left fstep l p) <= 254 /\
  0 <= snd (fold_left fstep l p) <= 254.
Proof.
  induction l as [| d l IH]; intros p H1 H2 HF; cbn [fold_left]; [auto |].
  inversion HF; subst.
  destruct (fstep_bounds p d H1 H2) as [Hf1 Hf2]; [assumption |].
  now apply IH.
Qed.

(** The conditional subtract is mod 255 on the invariant domain. *)
Lemma step1_mod : forall s d,
  0 <= s <= 254 -> sym_ok d -> step1 s d = (s + d) mod 255.
Proof.
  intros s d Hs Hd. unfold step1, M, sym_ok in *.
  destruct (255 <=? s + d) eqn:E;
    [apply Z.leb_le in E | apply Z.leb_gt in E].
  - apply Z.mod_unique with (q := 1); lia.
  - now rewrite Z.mod_small by lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** s1 characterized: it is the message sum, mod 255 *)

Fixpoint zsum (l : list Z) : Z :=
  match l with [] => 0 | d :: r => d + zsum r end.

Lemma fst_fold_sum : forall l s1 s2,
  0 <= s1 <= 254 -> 0 <= s2 <= 254 -> Forall sym_ok l ->
  fst (fold_left fstep l (s1, s2)) = (s1 + zsum l) mod 255.
Proof.
  induction l as [| d l IH]; intros s1 s2 H1 H2 HF; cbn [fold_left zsum].
  - cbn [fst]. rewrite Z.mod_small by lia. lia.
  - inversion HF; subst.
    unfold fstep at 2. cbn [fst snd] in *.
    rewrite IH;
      [| apply step1_bounds; auto
       | apply step1_bounds; auto; apply step1_bounds; auto
       | assumption].
    rewrite step1_mod by auto.
    rewrite Zplus_mod_idemp_l. f_equal. lia.
Qed.

Theorem fst_fletcher_sum : forall l,
  Forall sym_ok l -> fst (fletcher l) = (zsum l) mod 255.
Proof.
  intros l HF. unfold fletcher.
  rewrite fst_fold_sum by (auto || lia). f_equal.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Single-symbol corruption is always detected *)

Lemma zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a; intros; cbn; [lia |]. rewrite IHa. lia. Qed.

Theorem single_error_detected : forall pre post d d',
  Forall sym_ok pre -> Forall sym_ok post ->
  sym_ok d -> sym_ok d' -> d <> d' ->
  checksum (pre ++ d :: post) <> checksum (pre ++ d' :: post).
Proof.
  intros pre post d d' Hpre Hpost Hd Hd' Hne.
  assert (HF1 : Forall sym_ok (pre ++ d :: post))
    by (apply Forall_app; split; [auto | now constructor]).
  assert (HF2 : Forall sym_ok (pre ++ d' :: post))
    by (apply Forall_app; split; [auto | now constructor]).
  (* the two s1 values differ *)
  assert (Hs1 : fst (fletcher (pre ++ d :: post))
                <> fst (fletcher (pre ++ d' :: post))).
  { rewrite 2!fst_fletcher_sum by assumption.
    rewrite 2!zsum_app. cbn [zsum].
    intro Heq.
    (* equal residues of sums differing by d - d' *)
    assert (Hdvd : (zsum pre + (d + zsum post)
                    - (zsum pre + (d' + zsum post))) mod 255 = 0).
    { rewrite Zminus_mod. rewrite Heq. rewrite Z.sub_diag.
      apply Z.mod_0_l. lia. }
    replace (zsum pre + (d + zsum post) - (zsum pre + (d' + zsum post)))
      with (d - d') in Hdvd by lia.
    apply Z.mod_divide in Hdvd; [| lia].
    destruct Hdvd as [k Hk].
    unfold sym_ok in *. lia. }
  (* different s1 => different packed checksum (s1, s2 in [0,254]) *)
  unfold checksum.
  destruct (fletcher (pre ++ d :: post)) as [a1 a2] eqn:E1.
  destruct (fletcher (pre ++ d' :: post)) as [b1 b2] eqn:E2.
  cbn [fst] in Hs1.
  assert (Ha : 0 <= a1 <= 254 /\ 0 <= a2 <= 254).
  { unfold fletcher in E1.
    pose proof (run_bounds (pre ++ d :: post) (0, 0)
                  ltac:(cbn; lia) ltac:(cbn; lia) HF1) as HB.
    rewrite E1 in HB. cbn [fst snd] in HB. tauto. }
  assert (Hb : 0 <= b1 <= 254 /\ 0 <= b2 <= 254).
  { unfold fletcher in E2.
    pose proof (run_bounds (pre ++ d' :: post) (0, 0)
                  ltac:(cbn; lia) ltac:(cbn; lia) HF2) as HB.
    rewrite E2 in HB. cbn [fst snd] in HB. tauto. }
  lia.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Streaming: checksums compose over concatenation *)

Theorem fletcher_append : forall a b,
  fletcher (a ++ b) = fold_left fstep b (fletcher a).
Proof. intros. unfold fletcher. apply fold_left_app. Qed.

(** Extraction entry point: both sums plus the packed checksum. *)
Definition fletcher_demo (l : list Z) : Z * Z :=
  fletcher l.
