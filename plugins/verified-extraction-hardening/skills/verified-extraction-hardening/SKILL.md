---
name: verified-extraction-hardening
description: Harden formally verified code (Rocq/Coq, Lean, F*) that is extracted to a native language (Rust, OCaml, C) and consumed from a host language (Python, etc). Closes the three guarantee leaks — numeric-width remaps (Z→i64), FFI marshalling, host-language coercion — with proved input domains, checked-arithmetic builds, panic containment, and differential tests. Use when extracting verified code to a shared library, writing FFI/ctypes/PyO3 bindings over it, or auditing why a "proved" component can still return wrong answers.
---

# Hardening verified-extracted code across trust boundaries

A theorem proved about a program in the prover does **not** automatically hold
of the extracted binary. The guarantee leaks at three places, and each needs
its own defense. This skill is the generalized method; a complete working
instance (Rocq 9.1 → Rust → Python/ctypes) lives at the root of this
repository (see the README section "Where the guarantee leaks"), with a
worked audit record in `audits/`.

## The three leaks

1. **Width remap** (the dangerous one). Proofs are about unbounded `Z`/`nat`;
   extraction remaps them to `i64`/`u64` for usable code. Any intermediate
   that exceeds the machine width silently wraps. Every theorem remains true
   of the *source* program; the binary is no longer running that program.
   The inputs that trigger it are individually legal machine ints, so no
   type/range validation at the binding catches it.
2. **FFI marshalling**. The host↔native conversion code (list building,
   struct unpacking, pointer/length contracts) is ordinary unverified code.
   No prover theorem says anything about it.
3. **Host coercion**. Python's numeric tower (bool ⊂ int, float→int
   truncation, unbounded int) will hand the binding values the proofs never
   covered, and the result looks identical to a covered one.

Also enumerate the **residual trusted base** honestly in the README: the
extractor's pretty-printer, the remap table itself (`Z.add` ↦ `checked_add`
is an axiom connecting two languages), the native compiler. The goal is not
zero trust; it is that every trusted item is small, named, and defended.

## Defense in depth — build all layers, they protect against different failures

### Layer 1 — checked arithmetic build (turns *wrong* into *loud*)

Extract a second copy of the same entry point with checked numeric remaps.
In Rocq rust-extraction this is a one-line swap:
`ExtrRustUncheckedArith` → `ExtrRustCheckedArith`
(`a + b` becomes `a.checked_add(b).unwrap()`; overflow panics instead of
wrapping). Keep BOTH builds in the cdylib (`mod thing; mod thing_checked;`)
and make **checked the default** in the bindings, unchecked opt-in for
benchmarks. If the toolchain has no checked remap set, write one: remap each
arithmetic primitive to the target's checked op with a trap on failure.

### Layer 2 — prove the safe domain, then enforce exactly it (the core move)

Do **not** guess an input range in the bindings. Derive it in the prover:

1. For each extracted function, prove a bounds lemma **over the same
   recursion as the implementation**, bounding **every accumulator /
   intermediate**, not just the result. Shape (Rocq):

   ```coq
   Lemma scan_bounded : forall l acc B,
     0 <= B -> (* acc within its inductive bound *) ->
     Forall (fun x => -B <= x <= B) l ->
     (* every value scan computes stays within f(B) *).
   ```

   A theorem about the result alone does NOT rule out intermediate overflow.
   Generalize over the accumulators so the induction goes through; the
   recursive call's arguments must be exactly what the hypotheses bound.
2. Solve `f(B) <= machine_max` for the largest safe `B`; define it as a named
   constant in the theory (e.g. `safe_price_bound : Z := 2^62 - 1`) and prove
   the end-to-end corollary `..._fits_i64 : Forall (bounded B) l ->
   i64_min <= f l <= i64_max`. Check `Print Assumptions` — must be closed.
3. Mirror the constant in the bindings (`SAFE_X_BOUND = ...`) with a comment
   naming the theorem, and reject inputs outside it with a dedicated error
   type (`DomainError`) whose message **cites the theorem file/name**.
4. Hunt for *evaluate-before-check* obligations: code that computes a value
   and THEN range-checks it (e.g. a gate computing `pos + qty` before
   rejecting) needs the computed value representable too — often a separate
   inequality like `limit + max|qty| <= MAX`. Prove and enforce those as well.
5. Enforce every **theorem hypothesis** at the binding (e.g. a safety theorem
   assuming `-lim <= pos0 <= lim` means the binding must reject `lim < 0` —
   empty interval, no guarantee — and out-of-range initial state).
6. Sanity-check the boundary is usable: a test at exactly ±BOUND must return
   the true answer.

### Layer 3 — differential tests across the FULL stack

Transliterate the *specification* (the naive, readable version the proofs
reference) into the host language and, from the host, compare it against the
extracted implementation on thousands of randomized inputs inside the proved
domain. This is the only layer that exercises the marshalling — proofs cannot
see leak #2. Also re-check the theorems' properties themselves at runtime
(sortedness, permutation, invariants) as cheap witnesses.

### Binding hygiene (leak #3)

- Reject, never coerce: floats → `TypeError` (proofs are about integers;
  `1.5→1` yields an answer the proofs cover for an input the user didn't
  send). Reject `bool` where int is meant (Python `bool ⊂ int`). Reject
  values outside the machine width → `OverflowError`.
- Distinct error types: host-validation errors (`TypeError`/`OverflowError`),
  proved-domain violations (`DomainError`), native-side failures
  (`RocqError`-style, from status codes).

## FFI construction rules (native side)

- **C ABI cdylib + ctypes** is the default (zero host build tooling, callable
  from any language). PyO3/maturin only when a pip-installable wheel is the
  deliverable; then split core into an rlib with cdylib + pymodule frontends.
- Every export returns a **status code**; results via out-pointers. Codes:
  OK / null-pointer / panicked. `len == 0` must be valid regardless of ptr.
- **`catch_unwind` around every call into extracted code** — it can panic
  (`panic!("Absurd case!")` on empty matches, `unwrap` in numeric preambles,
  and all of layer 1). Unwinding across `extern "C"` is UB.
- Install a quiet panic hook (a library must not write to caller's stderr),
  opt-out via env var for debugging.
- Do not assume prover theorems at the FFI edge (e.g. clamp output length
  even if a theorem says it equals input length — the boundary defends
  itself).
- Generated-code mechanics (Rocq rust-extraction specifically): everything
  extracted is private, so **append** a small `pub` API to the generated file
  rather than writing a sibling module; each extracted file declares
  identically-named types (`Program`, list enum, macros) so each goes in its
  **own `mod`**; strip `^Debug` timing lines from `Redirect` output; wire the
  concatenation (generated + suffix) into the Makefile so `make` regenerates
  it from the proofs.

## Audit output (machine-readable evidence)

When applying this skill as an audit, do not stop at prose. Emit a JSON
record conforming to `checklist.schema.json` (next to this file) and save it
in the audited repo at `audits/hardening-<YYYY-MM-DD>.json`. Rules:

- Every checklist item appears with `status` pass/fail/partial/n-a — an
  inapplicable item is recorded as `n/a` with a reason, never omitted.
- `evidence` must be replayable: theorem name + file (and it must be
  `Print Assumptions`-closed), a test command with observed output, or a
  code location. "Looks correct" is not evidence.
- `toolchain` versions are mandatory — the audit is evidence only for those
  versions; re-audit on upgrade.
- Demonstrated divergences go in `known_leaks` with the triggering input and
  which layer now closes them (`closed_by: "OPEN"` if none does).
- List every residual trusted-base component individually.

## Checklist

- [ ] Checked-arith extraction exists and is the bindings' default
- [ ] Bounds lemmas cover every intermediate, induction over impl's recursion
- [ ] Safe-domain constant proved (`Print Assumptions` closed), exported,
      enforced with theorem-citing error messages
- [ ] Evaluate-before-check obligations found and separately enforced
- [ ] All theorem hypotheses enforced at the binding
- [ ] Boundary-value test passes at exactly ±BOUND
- [ ] Differential test host-vs-spec over randomized in-domain inputs
- [ ] Panics contained; status codes; quiet hook
- [ ] Floats/bools/out-of-width rejected, never coerced
- [ ] README names the residual trusted base
