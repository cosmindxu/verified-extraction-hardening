# Verified-extraction hardening — skill + worked example

Two things live here:

1. **A Claude Code skill** ([SKILL.md](plugins/verified-extraction-hardening/skills/verified-extraction-hardening/SKILL.md))
   for hardening formally verified code that is extracted to a native
   language and consumed over FFI. It names the three places the proof's
   guarantee leaks — numeric-width remaps (`Z`→`i64`), FFI marshalling, and
   host-language coercion — and gives a defense layer for each, plus a
   [machine-readable audit schema](plugins/verified-extraction-hardening/skills/verified-extraction-hardening/checklist.schema.json)
   (worked audit record: [`audits/`](audits/)).

   ```bash
   claude plugin marketplace add cosmindxu/verified-extraction-hardening
   claude plugin install verified-extraction-hardening
   ```

2. **The complete worked instance** the skill was distilled from — the rest
   of this README. Programs written and proved in **Rocq 9.1.1**, extracted
   to **Rust** via
   [`rocq-typed-extraction`](https://github.com/peregrine-project/rocq-typed-extraction)
   (MetaRocq typed erasure), compiled with `cargo`, and consumed from
   **Python** over ctypes — including a reproducible demonstration of the
   width-remap leak and the three layers that close it.

# Rocq → Rust extraction examples

Two examples:

1. **Insertion sort** — the "hello world", extracted two different ways so you
   can compare the plugin-free and plugin-based pipelines.
2. **Trading analytics** ([`theories/Trading.v`](theories/Trading.v)) — best
   single trade, maximum drawdown, and a position-limit risk gate. The
   interesting one: the O(n) online algorithms that ship are *proved equal* to
   obviously-correct O(n²) specifications.

## Layout

| Path | What it is |
| --- | --- |
| `theories/InsertionSort.v` | The program + the two correctness theorems |
| `theories/ExtractInsertionSort.v` | Driver #1 — Rocq-level API, no plugin |
| `theories/ExtractInsertionSortPlugin.v` | Driver #2 — `Rust Extract` vernacular |
| `extracted/*.rs.out` | **Generated** Rust (do not edit) |
| `rust/main_suffix.rs` | Hand-written `main` + marshalling (unverified) |
| `rust/insertion_sort{,_plugin}/` | Cargo crates; `src/main.rs` = generated + suffix |

Both drivers extract the *same* `demo` constant; the crates share
`main_suffix.rs`, so any difference in output is a difference in extraction.

## Build & run

```sh
eval $(opam env --switch=coq-switch)
make           # proofs -> both extractions -> cargo build -> run both
make compare   # diff generated source and program output
make clean
```

## What is proved

```coq
Theorem insertion_sort_sorted : forall l, Sorted Z.le (insertion_sort l).
Theorem insertion_sort_perm   : forall l, Permutation l (insertion_sort l).
```

Both are `Closed under the global context` (no axioms — check with
`Print Assumptions`). The Rust code is produced from the *same* definitions
these theorems talk about, by MetaRocq's verified erasure pipeline.

## The two drivers

`rocq-rust-extraction` 0.2.1 is a **theory-only** opam package — the
pretty-printer, no OCaml plugin. The `Rust Extract` vernacular and the
`Extract Inductive` commands live in the separate
`rocq-typed-extraction-plugin` package (`TypedExtraction.Plugin.*`).

**Driver #1** works without that plugin. It calls the Rocq-level API
(`TypedExtraction.Rust.PluginExtract.extract`) and builds the `remaps` record
by hand — it is plain Rocq data. `ind_remap` / `const_remap` transcribe the
subset of upstream's `ExtrRustBasic.v` + `ExtrRustUncheckedArith.v` that this
program needs.

**Driver #2** needs the plugin, and is four lines: `Require` the two remap
libraries, then `Redirect "..." Rust Extract demo`.

Remapping is not cosmetic. Without it `Z` extracts as its binary inductive and
`bool` as an enum whose variants are literally named `true` and `false` —
Rust keywords, which do not compile. With remaps, `Z` becomes `i64`, `bool`
becomes Rust `bool`, and the output drops from 585 to 283 lines.

### How the two compare

Runtime output: **identical**. Generated source: identical except for one
choice, because driver #1 remaps `Z.leb` straight to `a <= b` while upstream's
`ExtrRustUncheckedArith` remaps `Z.compare` and lets `Z.leb` be extracted from
its Rocq definition:

```rust
// driver #1
fn ..._Z_leb(&'a self, a: i64, b: i64) -> bool { a <= b }

// driver #2
fn ..._Z_compare(&'a self, a: i64, b: i64) -> std::cmp::Ordering { a.cmp(&b) }
fn ..._Z_leb(&'a self, x: i64, y: i64) -> bool {
  match self...._Z_compare(x, y) {
    std::cmp::Ordering::Equal   => { true  },
    std::cmp::Ordering::Less    => { true  },
    std::cmp::Ordering::Greater => { false },
  }
}
```

Driver #2 is the more conservative pipeline: it trusts a Rust primitive only
for `Z.compare`, and derives `Z.leb` from the erased Rocq definition. Driver #1
trusts one more hand-written line. Both are 283 vs 310 lines.

The plugin also prints `Debug: ... executed in: ...s` timing lines into the
`Redirect` output; the Makefile strips them with `sed '/^Debug/d'`, same as
upstream's `process-extraction-examples.sh`.

Lists are deliberately *not* remapped, so `insertion_sort` operates on a real
extracted `enum` allocated in a `bumpalo` arena — that is the interesting part
to look at.

## Boundary code

`rust/main_suffix.rs` is not verified. It only converts between
`Vec<i64>` and the extracted cons-list, and re-checks the two theorems at
runtime (`is_sorted`, `is_permutation`) as a smoke test on 1000 pseudo-random
inputs.

---

# Example 2: trading analytics

`theories/Trading.v` → `extracted/Trading.rs.out` → `rust/trading/`.
Run it alone with `make trading`.

Prices are integers (ticks/cents). No floating point, so the proofs transfer
to the extracted Rust without a real-arithmetic gap — this is the single most
important design decision in the file.

| Component | Theorem |
| --- | --- |
| `max_profit` — best buy-then-sell | `max_profit l = max_profit_spec l` |
| `max_drawdown` — worst peak-to-trough | `max_drawdown l = drawdown_spec l` |
| `run_orders` — position-limit risk gate | `-lim <= pos <= lim → -lim <= run_orders lim pos os <= lim` |

All three are `Closed under the global context`.

The first two are the useful pattern: `max_profit` is a single pass carrying
the cheapest price seen so far; `max_profit_spec` is the quadratic
max-over-all-pairs you can read and believe. The theorem says they never
disagree, so you ship the fast one. `rust/trading_main.rs` re-runs that
comparison at runtime against naive O(n²) transliterations on 5000 random
series — a witness for the theorem, not a substitute.

The risk-gate theorem has **no hypothesis on the orders at all**: quantities
may be negative, absurd, or adversarial, and the position still cannot leave
`[-lim, lim]`. It does require `-lim <= pos <= lim` to start, which for the
`pos = 0` entry point means `lim >= 0`; the stress test honours that. That is
not a technicality — with `lim < 0` the interval is empty and no position
could satisfy it.

---

# Example 3–5: three overflow postures

Three further examples, chosen so that each handles the width-remap leak a
*different* way. Together they are the skill's taxonomy, executable:

| Example | Theory | Headline theorems | Overflow posture |
| --- | --- | --- | --- |
| RLE codec | [`theories/Rle.v`](theories/Rle.v) | `rle_roundtrip`, `encode_length_le`, `encode_counts_pos`, `decode_length` | **No arithmetic to leak** — values are copied, counts are bounded by input length |
| Modular exponentiation | [`theories/ModExp.v`](theories/ModExp.v) | `pow_mod_correct`, `pow_mod_lt`, `square_fits`, `mixed_fits` | **Proved domain** — `modulus <= 2^32` (`safe_modulus`) keeps every product in u64; enforced by the bindings |
| Order FSM | [`theories/OrderFsm.v`](theories/OrderFsm.v) | `run_invariant`, `canceled_frozen`, `fill_add_bounded` | **Designed out** — the guard compares *before* adding, so it is safe for ALL inputs and the bindings enforce nothing |

Notes worth stealing:

- `encode_length_le` is a theorem doing FFI work: it justifies allocating the
  encode output buffer at the input's size.
- `pow_mod` is square-and-multiply by structural recursion on `positive`,
  which extracts to Rust's shift-based `__pos_elim` — the extracted code
  really is O(log e). `python/demo_more.py` checks 2000 random `(m, b, e)`
  against Python's built-in `pow`.
- The FSM guard (`0 <=? n && n <=? qty - filled`) evaluates no arithmetic
  that can leave the invariant's range — contrast the trading gate, which
  computes `pos + qty` first and therefore needs a proved side condition
  (`step_fits_i64`). Designing the check to come first is cheaper than
  proving the extra obligation.
- The order FSM demo throws fills drawn from the whole i64 range at the
  checked build: it never panics, because there is nothing to catch.

# Examples 6–11: safety-critical cores

Six examples in the domains where a verified core earns its keep: automotive
state machines, feedback controllers, and multi-sensor fusion. Run them with
`make python` (section `demo_safety.py`).

| Example | Theory | Headline theorems | Posture |
| --- | --- | --- | --- |
| Drive-mode FSM (PRND+Fault) | [`DriveModeFsm.v`](theories/DriveModeFsm.v) | `park_interlock`, `reverse_interlock`, `drive_interlock`, `fault_absorbing`, `run_fault_sticky` | no arithmetic at all |
| Hybrid energy FSM (SoC hysteresis) | [`HybridEnergyFsm.v`](theories/HybridEnergyFsm.v) | `run_soc_bounds`, `run_ev_floor`, `cs_charges` | designed out |
| PID w/ anti-windup | [`Pid.v`](theories/Pid.v) | `output_saturated` + `integral_bounded` (unconditional), `raw_fits_i64` (proved domain) | two-tier |
| Hysteresis relay (hybrid control) | [`Hysteresis.v`](theories/Hysteresis.v) | `no_chatter`, `band_invariant`, `cools_when_hot`/`heats_when_cold`, `step_fits_i64` | hypothesis-enforced |
| Finite-set MPC | [`Mpc.v`](theories/Mpc.v) | `mpc_le_all`, `mpc_realizable`, `mpc_first_action_consistent`, `mpc_fits_i64` | proved domain |
| Sensor fusion + plausibility | [`SensorFusion.v`](theories/SensorFusion.v) | `median_in_inputs`, `majority_band`, `accepted_near_fused`, `accepted_pairwise_consistent` | proved domain |

All 19 theorems `Closed under the global context`. Highlights:

**State machines.** The drive-mode FSM proves real transmission interlocks:
Park engages only near standstill (parking-pawl protection), a direction
change only below 1.5 m/s, and Fault is absorbing until an explicit clear
*at standstill*. Rejected shifts keep the current mode — "reject, don't
clamp" is what makes each interlock a case analysis instead of an arithmetic
argument. There is **no arithmetic on speeds at all**: guards are two-sided
comparisons rather than `Z.abs`, deliberately, because `Z.abs`/`Z.opp` on
`i64::MIN` panics the checked build. The energy FSM adds hysteresis
(enter charge-sustain at SoC 200‰, leave at 850‰) with the invariant that
EV-only mode never operates below its floor — for *every* request stream.

**Controllers.** The PID's two theorem tiers are the point: saturation and
anti-windup hold *unconditionally* (clamps), but the raw command is computed
**before** the clamp — the same evaluate-before-check obligation as the
trading gate — so `raw_fits_i64` proves the domain (|gain| ≤ 2¹⁵,
|error| ≤ 2³¹) and the bindings enforce it. The hysteresis loop proves an
**invariant set of the closed loop**: enter `[130, 270]` and no bounded
disturbance sequence ever exits it, plus strict progress toward the band
from outside — practical stability as theorems. The MPC enumerates the full
action tree, so optimality is a theorem, not a solver's claim: the reported
cost is ≤ *every* length-h rollout and is achieved by one of them. The demo
checks it against an exhaustive Python min over all 3⁵ sequences. Its i64
bound is airtight end to end: `CB` is a cost budget defined by recursion
over the *same* structure as `mpc`, `mpc_cost_bounded` proves the returned
cost — and via `mpc_intermediate_fits` every candidate the minimization
compares — stays within it, and `CB_cap` evaluates the budget at the
enforced domain against `i64::MAX` by computation.

**Sensor fusion.** The median is computed by **the verified insertion sort
from example 1** — cross-example reuse; its sortedness/permutation theorems
are load-bearing here. `majority_band` is the fault-masking theorem: a
strict majority of sensors agreeing within a band captures the fused value,
so a minority of arbitrarily-faulty sensors cannot drag it out.
`accepted_pairwise_consistent` is the scene-consistency guarantee: everything
the plausibility gate accepts is mutually within `2·tol`. During
development the prover caught an off-by-one in the sensor bound (2⁶² admits
`f + tol = 2⁶³`, one past `i64::MAX`); the shipped bound is 2⁶²−1.

## Remap namespace skew (Rocq 9.1 gotcha)

The plugin's `N.*` remaps target `Stdlib.NArith.BinNatDef`, but some stdlib
`N` operators (`N.leb`, `N.compare` via `<=?`) resolve to kernel names under
`Corelib.BinNums.NatDef` — those remaps miss, the operators extract from
source, and the source of `N.compare` trips an arity error on the remapped
`Pos.compare` (which is a partial application in Rocq, so its remapped call
sites print with arity 0). Symptom: `this method takes 2 arguments but 0
arguments were supplied` on generated code. Workaround used by
`OrderFsm.v`: model quantities in `Z`, whose remap surface
(`Corelib.BinNums.IntDef.Z.*`) matches. `ModExp.v` is unaffected because
`N.mul`/`N.modulo` do resolve to the `Stdlib.NArith` names.

---

# Calling it from Python

`make python`. No pip install, no build tooling beyond cargo — the bindings
are `ctypes` over a `cdylib`.

```python
import rocq

rocq.sort([5, 3, 8, 1])                  # -> [1, 3, 5, 8]
rocq.max_profit([10, 7, 5, 8, 11, 9])    # -> 6
rocq.max_drawdown(prices)
rocq.run_orders(limit=100, orders=[rocq.Order(buy=True, qty=60), ...])
rocq.analyze(prices, limit, orders)      # -> Analytics(max_profit=…, …)
```

| Path | |
| --- | --- |
| `rust/rocq_ffi/src/lib.rs` | Hand-written C ABI (`rocq_sort_i64`, `rocq_analyze`, …) |
| `rust/ffi_{sorting,trading}_api.rs` | `pub` Rust API suffixes appended to the generated code |
| `python/rocq.py` | The binding module |
| `python/demo.py` | Worked example + differential test |

Three things this layer has to get right:

**Both extracted modules go in separate Rust modules.** Each generated file
declares its own `Program`, `Corelib_Init_Datatypes_list`, arena and macros,
under the same names. `mod sorting;` / `mod trading;` keeps them apart in one
`cdylib`.

**The API suffixes are appended to the generated files**, not written
alongside them, because everything the extractor emits is private — `Program`,
its `alloc`, and the algorithm methods. Same trick as `main_suffix.rs`.

**Panics are caught at the boundary.** The extracted code can panic
(`panic!("Absurd case!")` for empty matches, `unwrap` in the numeric
preamble). `catch_unwind` turns that into a status code rather than letting it
unwind into the Python interpreter.

---

# Where the guarantee leaks, and how to close it

The proofs are about `Z`, which is unbounded. The extracted Rust uses `i64`.
That remap is a **trusted assumption**, and it is reachable from the fully
validated Python API:

```python
>>> rocq.max_profit([-2**62, 2**62], checked=False, enforce_domain=False)
0                        # true answer: 9223372036854775808
```

Both inputs are legal `i64`. No type check, no overflow check, no marshalling
check rejects them. Every theorem in `Trading.v` remains true of the *Rocq*
program — but the Rust you are running is not that program.

Three layers close it, in increasing order of strength.

### Layer 1 — checked arithmetic (one import)

`ExtrRustCheckedArith` instead of `ExtrRustUncheckedArith`:

```
Z.add  =>  a + b                        # unchecked: wraps
Z.add  =>  a.checked_add(b).unwrap()    # checked:   panics
```

`theories/ExtractTradingChecked.v` differs from `ExtractTrading.v` by that one
line. The FFI already catches panics, so silent corruption becomes
`RocqError`. Cheap, and it converts *wrong* into *loud*.

### Layer 2 — prove the safe domain, then enforce it

Better than failing at runtime is not entering the bad region. But the bound
must be **derived, not guessed** — so `theories/Trading.v` proves it:

```coq
Lemma mp_bounded : forall l m b B,          (* bounds every intermediate, *)
  0 <= B -> - B <= m <= B -> 0 <= b <= 2 * B ->   (* not just the result: *)
  Forall (fun p => - B <= p <= B) l ->      (* the induction is over the  *)
  0 <= mp m b l <= 2 * B.                   (* same recursion as the scan *)

Definition safe_price_bound : Z := 4611686018427387903.  (* 2^62 - 1 *)

Theorem max_profit_fits_i64 : forall l,
  Forall (fun p => - safe_price_bound <= p <= safe_price_bound) l ->
  i64_min <= max_profit l <= i64_max.
```

`rocq.SAFE_PRICE_BOUND` is that constant, and the binding rejects anything
outside it, citing the theorem. The risk gate gets the same treatment via
`step_fits_i64` — `step` evaluates `pos + qty` *before* range-checking it, so
that sum must be representable too, which is a separate obligation
(`limit + max|qty| <= i64_max`).

Note `mp_bounded` bounds the accumulators, not merely the return value. A
theorem about the result alone would not rule out an intermediate overflow.

### Layer 3 — differential testing across the boundary

`python/demo.py` and `rust/trading_main.rs` re-run the theorems' claims at
runtime against naive O(n²) implementations. That catches marshalling bugs,
which no Rocq proof can see: the proof is about the algorithm, not about the
`Vec<i64>` ↔ cons-list conversion or the ctypes packing.

### What it looks like

```
prices: [-4611686018427387904, 4611686018427387904]   (true answer 2^63)

layer 0  raw extracted  -> 0                    *** SILENTLY WRONG ***
layer 1  checked arith  -> RocqError: the extracted code panicked
layer 2  proved domain  -> DomainError: prices[0] exceeds SAFE_PRICE_BOUND
                                        (see max_profit_fits_i64)
```

And the proved boundary is usable, not merely conservative — at exactly
`±SAFE_PRICE_BOUND` the answer is still correct.

### What is still trusted

Being honest about the residue:

- **MetaRocq's erasure** — verified, but its Rust pretty-printer is not.
- **The remap table itself** — that `Z.add` really is `checked_add`, that
  `bool` really is Rust `bool`. Unproved by construction; it is the axiom that
  connects the two languages.
- **The FFI marshalling and ctypes packing** — ordinary unverified code,
  which is why layer 3 exists.
- **`rustc` and `cargo`.**

The point is not that the residue vanishes. It is that each item is small,
named, and individually cheap to defend — which is not true of a system where
the boundary was never identified.

## The bindings refuse what the proofs do not cover

This is the part worth copying. The theorems are about **integers**, so the
bindings reject floats rather than silently rounding, reject values outside
`int64`, and reject `limit < 0` — where `[-limit, limit]` is empty and
`run_orders_within_limit` guarantees nothing:

```
TypeError: values[0] must be an int (ticks/cents), got float: 1.5
OverflowError: prices[1] does not fit in int64: 18446744073709551616
ValueError: limit must be >= 0, got -5: the interval [5, -5] is empty, so
            run_orders_within_limit offers no guarantee
```

A verified core reached through a binding that quietly coerces its inputs is
a verified core you are no longer running.

## Proof note

`mdd_spec` pins its rewrite explicitly:

```coq
rewrite (max_list_map_max (fun q => peak - q) (fun q => p - q)).
```

Left implicit, higher-order unification eta-contracts `fun q => peak - q` into
`Z.sub peak`, and `lia` then sees two distinct atoms for the same term and
fails with `Cannot find witness`. The sibling lemma `mp_spec` needs no such
pinning because `fun q => q - m` has the bound variable in the first argument
and cannot be eta-contracted.
