(** * Multi-sensor fusion by median, with plausibility / scene consistency

    [k] sensors measure the same quantity (say vehicle speed: wheel
    odometry, GPS, radar).  Fusion is the MEDIAN of the readings -- and the
    median is computed by THE VERIFIED INSERTION SORT from
    [InsertionSort.v], so the sortedness and permutation theorems proved
    there are load-bearing here: cross-example reuse, not a fresh trusted
    sorting routine.

    On top of the fused value, a plausibility gate marks each reading
    consistent iff it lies within [tol] of the median.

    Theorems:

    - [median_in_inputs]     : the fused value IS one of the readings --
      fusion never fabricates a value that no sensor reported.  (Direct
      corollary of [insertion_sort_perm].)
    - [majority_band]        : if a strict majority of sensors agree within
      a band [lo, hi], the median lies in that band -- up to
      ceil(k/2) - 1 arbitrarily-faulty sensors cannot drag the fused
      value out of the band the healthy majority spans.  This is the
      fault-masking theorem that justifies median fusion.  (Uses
      [insertion_sort_sorted] via rank-counting lemmas.)
    - [accepted_near_fused]  : every reading the gate accepts is within
      [tol] of the fused value (the gate's contract).
    - [accepted_pairwise_consistent] : any two accepted readings are within
      [2*tol] of each other -- the SCENE-CONSISTENCY guarantee: the
      accepted picture is mutually coherent, not merely individually
      plausible.

    Overflow posture: PROVED DOMAIN (small).  The gate compares
    [fused - tol <= r <= fused + tol]; the two additions can overflow at
    the i64 edges, so the bindings enforce |reading| <= SAFE and
    0 <= tol <= SAFE with SAFE = 2^62 - 1 ([gate_fits_i64]; 2^62 itself
    fails: f + tol could reach exactly 2^63, one past i64::MAX -- the
    prover caught that off-by-one during development).  The median
    itself involves no arithmetic at all. *)

From Stdlib Require Import List.
From Stdlib Require Import ZArith.
From Stdlib Require Import Sorted.
From Stdlib Require Import Permutation.
From Stdlib Require Import Bool.
From Stdlib Require Import Lia.

From RocqRustExamples Require Import InsertionSort.

Import ListNotations.
Local Open Scope Z_scope.

(** ** Fusion *)

Definition fused (readings : list Z) : Z :=
  nth (Nat.div2 (length readings)) (insertion_sort readings) 0.

(** ** Plausibility gate *)

Definition SAFE_SENSOR_BOUND : Z := 4611686018427387903.  (* 2^62 - 1 *)

Definition plausible (f tol r : Z) : bool :=
  (f - tol <=? r) && (r <=? f + tol).

Definition gate (tol : Z) (readings : list Z) : list bool :=
  let f := fused readings in
  map (plausible f tol) readings.

(** ** The fused value is a real reading *)

Lemma insertion_sort_length_eq : forall l,
  length (insertion_sort l) = length l.
Proof. intro l. symmetry. apply Permutation_length, insertion_sort_perm. Qed.

Theorem median_in_inputs : forall readings,
  readings <> [] -> In (fused readings) readings.
Proof.
  intros readings Hne.
  eapply Permutation_in.
  - apply Permutation_sym, insertion_sort_perm.
  - unfold fused. apply nth_In.
    rewrite insertion_sort_length_eq.
    destruct readings as [| x r]; [congruence |].
    cbn [length]. apply Nat.lt_div2. lia.
Qed.

(** ** Rank-counting lemmas on sorted lists

    [cnt p l] counts satisfying elements.  On a sorted list, if fewer than
    [k+1] elements are below [lo], then index [k] is at least [lo]; dually
    above.  These two are what turn "a majority is in the band" into "the
    middle index is in the band". *)

Definition cnt (p : Z -> bool) (l : list Z) : nat :=
  length (filter p l).

Lemma sorted_hd_all : forall x l,
  Sorted Z.le (x :: l) -> Forall (fun y => x <= y) l.
Proof.
  intros x l H.
  apply Sorted_StronglySorted in H; [| exact Z.le_trans].
  now inversion H.
Qed.

Lemma sorted_nth_lower : forall l k lo,
  Sorted Z.le l ->
  (k < length l)%nat ->
  (cnt (fun x => (x <? lo)%Z) l <= k)%nat ->
  lo <= nth k l 0.
Proof.
  induction l as [| x l IH]; intros k lo Hs Hk Hc; cbn [length] in *; [lia |].
  unfold cnt in Hc. cbn [filter] in Hc.
  destruct (x <? lo) eqn:Hx.
  - (* head below lo: it is counted, so k >= 1; recurse *)
    cbn [length] in Hc.
    destruct k as [| k']; [lia |].
    cbn [nth]. apply IH.
    + now inversion Hs.
    + lia.
    + unfold cnt. lia.
  - (* head >= lo: everything is >= lo by sortedness *)
    apply Z.ltb_ge in Hx.
    destruct k as [| k']; cbn [nth]; [lia |].
    pose proof (sorted_hd_all x l Hs) as Hall.
    assert (Hin : (k' < length l)%nat) by lia.
    pose proof (nth_In l 0 Hin) as HIn.
    rewrite Forall_forall in Hall.
    specialize (Hall _ HIn). lia.
Qed.

Lemma filter_all : forall (p : Z -> bool) l,
  Forall (fun y => p y = true) l -> filter p l = l.
Proof.
  intros p l H. induction l as [| y l IH]; [reflexivity |].
  inversion H; subst. cbn [filter].
  rewrite H2. f_equal. now apply IH.
Qed.

Lemma sorted_nth_upper : forall l k hi,
  Sorted Z.le l ->
  (k < length l)%nat ->
  (cnt (Z.ltb hi) l <= length l - 1 - k)%nat ->
  nth k l 0 <= hi.
Proof.
  induction l as [| x l IH]; intros k hi Hs Hk Hc; cbn [length] in *; [lia |].
  unfold cnt in Hc. cbn [filter] in Hc.
  destruct (hi <? x) eqn:Hx.
  - (* head above hi: by sortedness ALL are above hi, so the count is the
       whole list -- contradiction with the budget *)
    apply Z.ltb_lt in Hx.
    pose proof (sorted_hd_all x l Hs) as Hall.
    assert (Hcnt_all : cnt (Z.ltb hi) l = length l).
    { unfold cnt. rewrite filter_all; [reflexivity |].
      eapply Forall_impl; [| exact Hall].
      intros y Hy. simpl in Hy. apply Z.ltb_lt. lia. }
    unfold cnt in Hcnt_all. cbn [length] in Hc. lia.
  - (* head <= hi *)
    apply Z.ltb_ge in Hx.
    destruct k as [| k']; cbn [nth]; [lia |].
    apply IH.
    + now inversion Hs.
    + lia.
    + unfold cnt. lia.
Qed.

(** ** Fault masking: a majority band captures the median *)

Definition in_band (lo hi x : Z) : bool := (lo <=? x) && (x <=? hi).



(** Below-lo and in-band are mutually exclusive predicates, so their
    counts over the same list sum to at most its length -- no NoDup
    argument (readings may repeat). *)

Lemma cnt_le_length : forall (p : Z -> bool) l, (cnt p l <= length l)%nat.
Proof.
  intros p l. unfold cnt.
  induction l as [| x l IH]; cbn [filter length]; [lia |].
  destruct (p x); cbn [length]; lia.
Qed.

Lemma cnt_disjoint_le : forall (p q : Z -> bool) l,
  (forall x, p x = true -> q x = false) ->
  (cnt p l + cnt q l <= length l)%nat.
Proof.
  intros p q l Hex.
  induction l as [| x l IH]; cbn [cnt filter length]; [lia |].
  unfold cnt in *. cbn [filter].
  destruct (p x) eqn:Hp.
  - rewrite (Hex x Hp). cbn [length]. lia.
  - destruct (q x); cbn [length]; lia.
Qed.

Lemma Permutation_filter' : forall (p : Z -> bool) l l',
  Permutation l l' -> Permutation (filter p l) (filter p l').
Proof.
  intros p l l' H. induction H; simpl.
  - constructor.
  - destruct (p x); [now constructor | assumption].
  - destruct (p x); destruct (p y); simpl;
      try apply perm_swap; apply Permutation_refl.
  - eapply Permutation_trans; eauto.
Qed.

Lemma div2_double_le : forall n, (2 * Nat.div2 n <= n)%nat.
Proof.
  intro n. pose proof (Nat.div2_odd n) as H.
  destruct (Nat.odd n); simpl in H; lia.
Qed.

Lemma le_div2_of_double_lt : forall c n,
  (2 * c < n)%nat -> (c <= Nat.div2 n)%nat.
Proof.
  intros c n H. pose proof (Nat.div2_odd n) as Ho.
  destruct (Nat.odd n); simpl in Ho; lia.
Qed.

Theorem majority_band : forall readings lo hi,
  lo <= hi ->
  (2 * cnt (in_band lo hi) readings > length readings)%nat ->
  lo <= fused readings <= hi.
Proof.
  intros readings lo hi Hlohi Hmaj.
  set (s := insertion_sort readings).
  assert (Hsort : Sorted Z.le s) by apply insertion_sort_sorted.
  assert (Hlen : length s = length readings)
    by (unfold s; apply insertion_sort_length_eq).
  (* count is permutation-invariant *)
  assert (Hcnt' : cnt (in_band lo hi) s = cnt (in_band lo hi) readings).
  { unfold cnt, s.
    now rewrite (Permutation_length
                   (Permutation_filter' (in_band lo hi) _ _
                      (Permutation_sym (insertion_sort_perm readings)))). }
  pose proof (cnt_le_length (in_band lo hi) readings) as Hcle.
  assert (Hne : (0 < length readings)%nat) by lia.
  assert (Hkm : (Nat.div2 (length readings) < length s)%nat).
  { rewrite Hlen. now apply Nat.lt_div2. }
  assert (Hdisj_lo : forall x, (x <? lo)%Z = true -> in_band lo hi x = false).
  { intros x Hx. apply Z.ltb_lt in Hx. unfold in_band.
    replace (lo <=? x) with false by (symmetry; apply Z.leb_gt; lia).
    reflexivity. }
  assert (Hdisj_hi : forall x, (hi <? x)%Z = true -> in_band lo hi x = false).
  { intros x Hx. apply Z.ltb_lt in Hx. unfold in_band.
    replace (x <=? hi) with false by (symmetry; apply Z.leb_gt; lia).
    now rewrite andb_false_r. }
  pose proof (cnt_disjoint_le _ _ s Hdisj_lo) as Hsum_lo.
  pose proof (cnt_disjoint_le _ _ s Hdisj_hi) as Hsum_hi.
  pose proof (div2_double_le (length readings)) as Hd2.
  unfold fused. fold s.
  split.
  - apply sorted_nth_lower; [exact Hsort | exact Hkm |].
    rewrite Hcnt' in Hsum_lo. rewrite Hlen in Hsum_lo.
    apply le_div2_of_double_lt. lia.
  - apply sorted_nth_upper; [exact Hsort | exact Hkm |].
    rewrite Hcnt' in Hsum_hi. rewrite Hlen in Hsum_hi. rewrite Hlen.
    assert (Hgt : (Nat.div2 (length readings)
                   < cnt (in_band lo hi) readings)%nat) by lia.
    lia.
Qed.

(** ** The gate's contracts *)

Theorem accepted_near_fused : forall tol readings i r,
  0 <= tol ->
  nth_error readings i = Some r ->
  nth_error (gate tol readings) i = Some true ->
  fused readings - tol <= r <= fused readings + tol.
Proof.
  intros tol readings i r Htol Hr Hg.
  unfold gate in Hg.
  rewrite nth_error_map, Hr in Hg. simpl in Hg.
  injection Hg as Hg.
  unfold plausible in Hg.
  apply andb_true_iff in Hg as [H1 H2].
  apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Theorem accepted_pairwise_consistent : forall tol readings i j ri rj,
  0 <= tol ->
  nth_error readings i = Some ri ->
  nth_error readings j = Some rj ->
  nth_error (gate tol readings) i = Some true ->
  nth_error (gate tol readings) j = Some true ->
  - (2 * tol) <= ri - rj <= 2 * tol.
Proof.
  intros tol readings i j ri rj Htol Hi Hj Hgi Hgj.
  pose proof (accepted_near_fused tol readings i ri Htol Hi Hgi).
  pose proof (accepted_near_fused tol readings j rj Htol Hj Hgj).
  lia.
Qed.

(** ** The proved i64 domain for the gate's two additions *)

Theorem gate_fits_i64 : forall f tol,
  - SAFE_SENSOR_BOUND <= f <= SAFE_SENSOR_BOUND ->
  0 <= tol <= SAFE_SENSOR_BOUND ->
  - 9223372036854775808 <= f - tol /\ f + tol <= 9223372036854775807.
Proof. unfold SAFE_SENSOR_BOUND. intros. lia. Qed.

(** Extraction entry point: fused value plus per-sensor plausibility. *)
Definition fusion_demo (tol : Z) (readings : list Z) : Z * list bool :=
  (fused readings, gate tol readings).
