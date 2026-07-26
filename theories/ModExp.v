(** * Modular exponentiation, proved equal to its specification

    Square-and-multiply over the binary structure of the exponent
    ([positive]), against the spec [(b ^ e) mod m].  The recursion on
    [positive] is O(log e) and extracts to Rust's shift-based [__pos_elim],
    so the extracted code really is the fast algorithm.

    Overflow posture: PROVED DOMAIN.  [N] extracts to [u64].  Every
    intermediate is a product of two values [< m] (that is [pow_mod_lt] and
    [N.mod_lt]), so [m <= 2^32] keeps every product below [2^64]
    ([square_fits], [mixed_fits]).  The bindings enforce exactly that bound.

    A second, sneakier near-leak this example documents: [x mod 0].  Rocq's
    convention is [x mod 0 = x].  The UNCHECKED remap computes [x % 0],
    which panics; the checked remap ([checked_rem(b).unwrap_or(a)]) happens
    to reproduce Rocq's convention exactly.  Either way the correctness
    theorem assumes [m <> 0], so the bindings reject [m = 0] -- the
    theorem's hypothesis, enforced at the door, independent of which build
    is loaded. *)

From Stdlib Require Import NArith.
From Stdlib Require Import Lia.

Local Open Scope N_scope.

Fixpoint pow_mod_pos (m b : N) (e : positive) : N :=
  match e with
  | xH => b mod m
  | xO e' => let r := pow_mod_pos m b e' in (r * r) mod m
  | xI e' => let r := pow_mod_pos m b e' in ((r * r) mod m) * (b mod m) mod m
  end.

Definition pow_mod (m b e : N) : N :=
  match e with
  | N0 => 1 mod m
  | Npos p => pow_mod_pos m b p
  end.

(** ** Correctness *)

Lemma pow_pos_double : forall b (e : positive),
  b ^ (N.pos e~0) = b ^ (N.pos e) * b ^ (N.pos e).
Proof.
  intros b e.
  replace (N.pos e~0) with (N.pos e + N.pos e) by lia.
  apply N.pow_add_r.
Qed.

Lemma pow_pos_double_succ : forall b (e : positive),
  b ^ (N.pos e~1) = b ^ (N.pos e) * b ^ (N.pos e) * b.
Proof.
  intros b e.
  replace (N.pos e~1) with (N.pos e + N.pos e + 1) by lia.
  rewrite 2!N.pow_add_r, N.pow_1_r. reflexivity.
Qed.

Lemma pow_mod_pos_correct : forall e m b,
  m <> 0 -> pow_mod_pos m b e = (b ^ N.pos e) mod m.
Proof.
  induction e as [e IH | e IH |]; intros m b Hm; simpl pow_mod_pos.
  - (* xI: e~1, exponent 2e+1 *)
    rewrite IH by exact Hm.
    rewrite pow_pos_double_succ.
    symmetry.
    rewrite (N.Div0.mul_mod (b ^ N.pos e * b ^ N.pos e) b m).
    rewrite (N.Div0.mul_mod (b ^ N.pos e) (b ^ N.pos e) m).
    reflexivity.
  - (* xO: e~0, exponent 2e *)
    rewrite IH by exact Hm.
    rewrite pow_pos_double.
    now rewrite <- N.Div0.mul_mod.
  - (* xH *)
    now rewrite N.pow_1_r.
Qed.

Theorem pow_mod_correct : forall m b e,
  m <> 0 -> pow_mod m b e = (b ^ e) mod m.
Proof.
  intros m b [| p] Hm; simpl.
  - reflexivity.
  - now apply pow_mod_pos_correct.
Qed.

(** ** Overflow safety: the proved domain

    Every intermediate the algorithm multiplies is [< m]: *)

Theorem pow_mod_lt : forall m b e, m <> 0 -> pow_mod m b e < m.
Proof.
  intros m b e Hm. destruct e as [| p]; simpl.
  - now apply N.mod_lt.
  - induction p as [p IH | p IH |]; simpl; now apply N.mod_lt.
Qed.

Definition safe_modulus : N := 4294967296.  (* 2^32 *)
Definition u64_max : N := 18446744073709551615.  (* 2^64 - 1 *)

(** With [m <= 2^32], squaring an [< m] value stays within u64 ... *)
Lemma square_fits : forall r m,
  r < m -> m <= safe_modulus -> r * r <= u64_max.
Proof. intros r m H1 H2. unfold safe_modulus, u64_max in *. nia. Qed.

(** ... as does multiplying two [< m] values. *)
Lemma mixed_fits : forall a b m,
  a < m -> b < m -> m <= safe_modulus -> a * b <= u64_max.
Proof. intros a b m H1 H2 H3. unfold safe_modulus, u64_max in *. nia. Qed.

(** So: enforce [1 <= m <= 2^32] at the binding and no product the
    extracted code forms can leave u64.  ([b] itself may be any u64: the
    first thing that touches it is [mod m].) *)

(** Extraction entry point. *)
Definition modexp_demo (m b e : N) : N := pow_mod m b e.
