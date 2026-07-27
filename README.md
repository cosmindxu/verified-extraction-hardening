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

# Why: interoperability

Safety cores do not live alone. Even in safety-critical systems, the
complete ecosystem mixes with LLMs, machine learning, multimedia, and
augmented user interfaces — and, at the very least in the **testing
environments**, the safety cores interact with non-safe languages. The
scenario generators, SiL/HiL harnesses, data pipelines, visualization
dashboards, and increasingly the LLM agents that drive exploratory testing
are Python (or JS, or notebooks) — so a verified core whose guarantees
evaporate the moment it is called from the messy side has not actually
shipped its guarantees anywhere.

That is the motivation for this repo's shape:

- **The boundary is the product.** The theorems live in Rocq; the callers
  live everywhere else. Everything here — the C ABI (`cdylib`, callable
  from any language, not just Python), the protection matrix, the
  theorem-citing `DomainError`s, the checked-build backstop — is about
  making the *crossing* preserve what was proved. Python in these examples
  is a stand-in for the whole non-safe ecosystem.
- **Degrees of trust can coexist.** This mirrors how safety standards
  already think (ASIL-decomposed components interacting with QM software
  under freedom-from-interference): the verified core does not require the
  ML perception stack, the AR HMI, or the test rig to be trustworthy — it
  requires the *interface* to reject, contain, or prove away everything
  those callers can do wrong. The scene checker's validate-then-compute
  architecture is that idea taken to its limit: a core that assumes
  nothing at all about its caller.
- **Machine-readable refusals are LLM-ready guardrails.** Every rejection
  here cites a theorem (`"exceeds SAFE_COORD; see ingest_fits_i64 in
  theories/SceneWorld.v"`). For a human that is documentation; for an LLM
  agent calling the core as a tool, it is structured, actionable feedback —
  the error message tells the model exactly which constraint to satisfy,
  backed by a proof instead of a comment. A verified core with
  theorem-citing errors is the right shape for the agentic ecosystems these
  systems are growing into.

The examples that follow are the working demonstration: fifteen verified
cores from five domains, each crossing Rocq → Rust → C ABI → Python with
its guarantees intact and its residual trust documented.

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

# Example 12: ADAS scene model with plausibility checking

[`theories/SceneModel.v`](theories/SceneModel.v) — the capstone: an
ego-centric L5 scene (road model, ego state, and detected vehicles, the ACC
target, pedestrians, bicycles, traffic signs, traffic lights) with a
consistency checker whose purpose is to **invalidate false positives and
flag low confidence — with a citable rule for every downgrade**.

## The rule catalog

**Hard** (physically impossible → `implausible`): class dimension envelopes
(a 5 m-wide "pedestrian" is not a pedestrian), class speed envelopes
(including |v_lateral| ≤ 5 m/s for vehicles and near-static signs/lights),
sensor FOV/range, malformed confidence, non-vehicle ACC target, and deep
bounding-box interpenetration with a validated object (the lower-priority
one is killed).

**Soft** (unusual → confidence penalty): vehicle/bicycle far off-road,
pedestrian on the carriageway of a fast road, sign/light in the middle of
the road, co-located lights showing red vs green, duplicate detections
(same class, nearly same pose and velocity), and target-vehicle rules
(behind ego, far off-lane, more than one target).

Verdict: any hard rule → `implausible` (score 0); otherwise
`score = max(0, confidence − penalties)`, `confirmed` iff score ≥ 60.

## The product theorems (11, all axiom-free)

| Theorem | The guarantee, in product terms |
| --- | --- |
| `check_length` | one entry per detection, in order |
| `hard_env_implausible` | no aggregation path resurrects a physically impossible object |
| `clean_confirmed` | a clean detection keeps its sensor confidence — **the checker never manufactures doubt**; every downgrade cites a rule |
| `score_bounds` | 0 ≤ score ≤ 100 for *every* input |
| `score_le_conf` | the checker never raises confidence |
| `loser_antisym`, `dup_at_most_one`, `overlap_at_most_one` | a duplicate/overlap pair never loses **both** members — deduplication cannot delete a real object twice over |
| `overlap_close_sym` | the geometry is symmetric; *who* gets penalized is decided by priority, not evaluation order |
| `validated_bounds`, `pair_arith_fits` | the overflow architecture (below) |

## Validate-then-compute: totality as architecture

This example's overflow posture is the strongest in the repo: **the checker
is total for any i64 inputs, with no domain for the caller to respect.**
Unary rules are comparisons only — no `abs`, no negation of raw input, so
even `i64::MIN` in every field is handled. All subtraction/multiplication
lives in the pair rules, which run strictly *after* both operands passed
the envelope; `validated_bounds` says what passing guarantees numerically,
and `pair_arith_fits` bounds every pair-rule intermediate within ±2¹⁷.
`demo_scene.py` feeds the checker scenes of pure i64 extremes: hard-rejected
by comparisons, zero arithmetic performed on the wild values.

The `dup_at_most_one` family deserves a highlight: penalizing the
lower-priority member of a duplicate pair is easy to get subtly wrong (kill
both and a real object vanishes from the scene). Here priority is a strict
total order (confidence, then position), its antisymmetry is a theorem, and
the pair rules inherit at-most-one from it.

Scope honesty: curvature participates in validation only in this version
(lateral positions are road-aligned); there is no occlusion reasoning, no
temporal consistency (single-frame), and the constants (envelopes,
penalties, thresholds) are engineering judgment — documented in the rule
catalog, not derived. The theorems are about the *checker's logic*: rule
extensions inherit the same guarantees as long as they keep the
validate-then-compute discipline.

# Example 13: world-frame ingestion — a domain the caller CAN get wrong

[`theories/SceneWorld.v`](theories/SceneWorld.v) adapts example 12 to the
interface many real stacks actually have: upstream fusion delivers tracks in
**world coordinates** plus an ego pose, and the rules are ego-relative — so
ingestion must compute `dx = x_world − ego_x` and rotate (negate) **before**
any envelope can run. That arithmetic cannot be gated: it *produces* the
values the gates need. A caller domain is now unavoidable:

- `SAFE_COORD = 2⁶²−1`, proved sufficient by `ingest_fits_i64` — including
  the sharp edge: the theorem's margin-of-one guarantees no intermediate
  ever equals `i64::MIN`, whose negation is undefined.
- `egress_ingest_id`: the quarter-turn pose transform is lossless, so
  ego-frame checking is faithful to the world scene (the demo verifies
  world-frame and ego-frame calls return identical entries).
- `world_check_length`, `world_scores_bounded`: the example-12 guarantees
  lift through ingestion unchanged.

The pair of examples is the point: **same checker, two interfaces** — one
with no domain at all (12), one where the domain is forced by the interface
and must be derived, proved, and enforced (13). When you can choose the
interface, choose 12's; when upstream chooses for you, 13 is the fallback
discipline. `demo_scene.py` §5 shows all layers: `DomainError` citing
`ingest_fits_i64`, then (bypassed) the checked build panicking — contained —
on both the subtraction overflow and the `i64::MIN` negation.

---

# Example 14: Fletcher-16 — a domain that guards a THEOREM, not a width

[`theories/Fletcher.v`](theories/Fletcher.v): the classic data-link checksum
(CAN-style frames, sensor buses), implemented division-free (conditional
subtract, proved equal to mod-255 — `step1_mod`) and proved to **detect
every single-symbol corruption** (`single_error_detected`), with the sums
characterized (`fst_fletcher_sum`), bounded (`run_bounds`), and streamable
(`fletcher_append`).

The novel lesson is the *kind* of domain: `single_error_detected` assumes
symbols in `[0, 254]`, and that hypothesis is load-bearing — Fletcher works
mod 255, so **0 and 255 are congruent**: substituting one for the other is
precisely the corruption the checksum cannot see (the classic Fletcher
blind spot). Bypassing the binding's `DomainError` neither crashes nor
overflows; it silently forfeits the *detection guarantee*, and
`demo_integrity.py` exhibits the 0x00 ↔ 0xFF collision to prove it. Until
now every proved domain in this repo guarded an integer width; this one
guards a theorem. Both are "outside the proofs" — the failure mode just
differs (wrong-answer risk vs lost-property risk).

# Example 15: RSS safe following distance, division-free

[`theories/Rss.v`](theories/Rss.v): the Responsibility-Sensitive Safety
minimum-distance check — the formal safety envelope popularized for AVs.
The textbook formula divides by braking rates; multiplying through by
`200·b_min·b_max` yields an **equivalent polynomial inequality over the
integers**: division-free, exactly representable (the demo shows exact
agreement with the float reference on 2000 random situations — no epsilon),
and provable:

- `rss_monotone_distance` / `rss_antitone_rear_speed` /
  `rss_monotone_front_speed`: the verdict moves the way physics demands —
  more gap, a slower rear vehicle, or a faster front vehicle can never turn
  safe into unsafe. A checker without these would flicker between verdicts
  as a situation strictly improves.
- `rss_standstill_safe`: a stationary, non-accelerating rear vehicle is
  safe at any gap.
- `rss_fits_i64`: the proved domain (gap ≤ 10 km, speeds ≤ 70 m/s,
  ρ ≤ 5 s, accelerations ≤ 15 m/s²) keeps every product within ±2⁵⁰.

Development honesty, recorded in the file header: the first draft had an
integer *unit* inconsistency (ρ in whole seconds) that type-checked and
proved fine — the monotonicity theorems are unit-blind — and was caught by
the demo's physical sanity check against the float formula. Proofs catch
logic; differential tests against an independent reference catch units.
Scope: longitudinal, same-lane, worst-case constant accelerations; the
parameters are regulatory/engineering inputs.

# Python interface protections, by example

Every entry point applies the same layered model — **(a)** host-type
validation: true ints only, within i64, floats/bools rejected never coerced
(`TypeError`/`OverflowError`); **(b)** proved-domain enforcement, with the
error message citing the theorem (`DomainError`); **(c)** theorem-hypothesis
enforcement (`ValueError`); **(d)** the checked-arithmetic native build as
backstop — a bypassed or missed overflow panics and is contained at the FFI
(`RocqError`), never silent. What varies per example is *which* layers are
needed:

| Entry point | (b) proved domain (theorem) | (c) hypotheses enforced | Why / notes |
| --- | --- | --- | --- |
| `sort` | — none needed | — | comparisons only; total on any i64 |
| `max_profit`, `max_drawdown` | `\|price\| ≤ 2⁶²−1` (`max_profit_fits_i64`) | — | scans subtract prices |
| `run_orders` | `limit + max\|qty\| ≤ i64::MAX` (`step_fits_i64`) | `limit ≥ 0`, initial ∈ `[-limit, limit]` | gate computes `pos+qty` **before** checking it |
| `analyze` | both of the above | both of the above | composite call, same protections as its parts |
| `rle_encode` / `rle_decode` | — none needed | decode size cap (allocation sanity) | counts bounded by input length; buffer sized by `encode_length_le` |
| `pow_mod` | `m ≤ 2³²` (`square_fits`/`mixed_fits`) | `m ≠ 0` (`pow_mod_correct`) | products of values `< m` |
| `run_order_events` | — none needed | `qty ≥ 0` (`init_run_invariant`) | guard compares **before** adding |
| `drive_fsm_run` | — none needed | — | no arithmetic at all; two-sided compares, no `abs`/`opp` |
| `energy_fsm_run` | — none needed | — | designed out: raw request only min-ed/compared |
| `pid_run` | `\|gain\| ≤ 2¹⁵`, `\|err\| ≤ 2³¹` (`raw_fits_i64`) | — | `raw` computed before the output clamp |
| `thermo_run` | `\|t0\| ≤ 2⁶²` (`step_fits_i64`) | — | plant adds a bounded rate to `t` |
| `mpc_decide` | `\|state\|,\|ref\| ≤ 2²⁰`, `h ≤ 8` (`mpc_fits_i64`, `CB_cap`) | — | squared tracking costs over the horizon |
| `fuse` | `\|reading\|, tol ≤ 2⁶²−1` (`gate_fits_i64`) | non-empty readings, `tol ≥ 0` | gate computes `fused ± tol` |
| `check_scene` | — **none exists** | — | validate-then-compute: total for any i64 (`validated_bounds`, `pair_arith_fits`) |
| `check_scene_world` | `\|coord\|,\|vel\|,\|pose\| ≤ 2⁶²−1` (`ingest_fits_i64`) | `heading ∈ 0..3` (`egress_ingest_id`) | ingest subtracts/negates raw input, pre-validation |
| `fletcher16` | symbols ∈ `[0, 254]` (`single_error_detected` **hypothesis** — guards the detection *property*, not a width) | — | bypass = silent loss of the guarantee (0≡255 mod 255), not overflow |
| `rss_check` | full `rss_dom` (`rss_fits_i64`) | — | polynomial margin: products of speeds/accelerations |

Reading the table top to bottom is reading the skill's argument: the "none
needed" rows are designs that made the domain vanish; the theorem-cited rows
are domains that were **derived and proved**, not guessed; and every row has
layer (d) underneath — `enforce_domain=False` (where offered) demonstrates
the contained panic rather than a wrong answer. Full docstrings on every
function in [`python/rocq.py`](python/rocq.py) restate the applicable
protections and theorems.

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
