#!/usr/bin/env python3
"""Use the Rocq-proved, Rust-extracted algorithms from Python.

Run:  python3 python/demo.py     (or: make python)
"""

import random
import sys
import time

import rocq


def rule(title):
    print(f"\n{'=' * 68}\n{title}\n{'=' * 68}")


def main() -> int:
    rule("Rocq -> Rust -> Python")
    print(f"native library: {rocq.library_path()}")

    # ---------------------------------------------------------------- sort
    rule("1. sort  (proved: sorted, and a permutation of the input)")

    xs = [5, 3, 8, 1, 9, 2, 7, -4, 0, 6]
    print(f"  rocq.sort({xs})")
    print(f"    -> {rocq.sort(xs)}")

    for case in ([], [42], [3, 3, 3], [-1, -2, -3], [2**62, -(2**62), 0]):
        got = rocq.sort(case)
        assert got == sorted(case), (case, got)
        print(f"  {str(case):<32} -> {got}")

    random.seed(7)
    trials = 2_000
    for _ in range(trials):
        case = [random.randint(-10_000, 10_000) for _ in range(random.randint(0, 60))]
        got = rocq.sort(case)
        assert got == sorted(case), case
        assert sorted(got) == sorted(case)
    print(f"\n  {trials} random lists agree with Python's sorted(): OK")

    # ------------------------------------------------------------- trading
    rule("2. trading analytics")

    path = [
        10_000, 10_240, 9_870, 9_610, 10_120, 10_890, 11_450, 10_980,
        9_940, 9_320, 9_780, 10_310, 11_020, 11_890, 11_400, 11_960,
    ]
    orders = [
        rocq.Order(buy=True, qty=60),
        rocq.Order(buy=True, qty=60),    # would breach
        rocq.Order(buy=True, qty=40),
        rocq.Order(buy=False, qty=250),  # would breach
        rocq.Order(buy=False, qty=180),
    ]
    limit = 100

    a = rocq.analyze(path, limit, orders)
    print(f"  prices ({len(path)} points, cents), limit +/-{limit}")
    print(f"    max_profit     = {a.max_profit}")
    print(f"    max_drawdown   = {a.max_drawdown}")
    print(f"    final_position = {a.final_position}")

    # Same numbers via the individual entry points.
    assert a.max_profit == rocq.max_profit(path)
    assert a.max_drawdown == rocq.max_drawdown(path)
    assert a.final_position == rocq.run_orders(limit, orders)
    print("    (individual calls agree with analyze())")

    # --------------------------------------- differential test vs Python
    rule("3. differential test: extracted code vs Python reference")

    def py_max_profit(p):
        best = 0
        for i in range(len(p)):
            for j in range(i + 1, len(p)):
                best = max(best, p[j] - p[i])
        return best

    def py_max_drawdown(p):
        worst = 0
        for i in range(len(p)):
            for j in range(i + 1, len(p)):
                worst = max(worst, p[i] - p[j])
        return worst

    def py_run_orders(limit, initial, os_):
        pos = initial
        for buy, qty in os_:
            want = pos + qty if buy else pos - qty
            if -limit <= want <= limit:
                pos = want
        return pos

    random.seed(11)
    trials = 2_000
    breaches = 0
    for _ in range(trials):
        series = [random.randint(-50_000, 50_000) for _ in range(random.randint(0, 40))]
        assert rocq.max_profit(series) == py_max_profit(series), series
        assert rocq.max_drawdown(series) == py_max_drawdown(series), series

        lim = random.randint(0, 1_000)
        os_ = [(random.random() < 0.5, random.randint(-5_000, 5_000))
               for _ in range(random.randint(0, 30))]
        got = rocq.run_orders(lim, os_)
        assert got == py_run_orders(lim, 0, os_)
        if not -lim <= got <= lim:
            breaches += 1

    print(f"  {trials} random price series: max_profit agrees with the naive spec")
    print(f"  {trials} random price series: max_drawdown agrees with the naive spec")
    print(f"  {trials} random order sequences: position limit breached {breaches} times")
    assert breaches == 0

    # --------------------------------------------------- input validation
    rule("4. the bindings refuse inputs the proofs do not cover")

    for bad, why in (
        (lambda: rocq.sort([1.5, 2.0]), "floats are not integers"),
        (lambda: rocq.max_profit([1, 2**64]), "does not fit in int64"),
        (lambda: rocq.run_orders(-5, []), "initial position outside [-limit, limit]"),
    ):
        try:
            bad()
        except (TypeError, OverflowError, ValueError) as e:
            print(f"  rejected ({why}):\n      {type(e).__name__}: {e}")
        else:
            print(f"  NOT rejected, but should have been: {why}")
            return 1

    # ----------------------------------------------- the Z -> i64 leak
    rule("5. the Z -> i64 leak, and the three layers that close it")

    leak = [-(2**62), 2**62]
    true_answer = py_max_profit(leak)
    print(f"  prices        : {leak}")
    print(f"  true answer   : {true_answer}   (Rocq's Z is unbounded)")
    print("  both inputs are perfectly legal int64 -- nothing above rejects them\n")

    raw = rocq.max_profit(leak, checked=False, enforce_domain=False)
    print(f"  layer 0  raw extracted  -> {raw}    *** SILENTLY WRONG ***")
    print("           i64 wraps; every theorem in Trading.v still holds of the")
    print("           Rocq program, but the Rust you are running is not it.\n")

    try:
        rocq.max_profit(leak, checked=True, enforce_domain=False)
        print("  layer 1  checked arith  -> no error (unexpected)")
        return 1
    except rocq.RocqError as e:
        print(f"  layer 1  checked arith  -> RocqError: {e}")
        print("           ExtrRustCheckedArith makes it panic; the FFI contains it.")
        print("           Loud and wrong-free, but still a runtime failure.\n")

    try:
        rocq.max_profit(leak)
        print("  layer 2  proved domain  -> no error (unexpected)")
        return 1
    except rocq.DomainError as e:
        first = str(e).splitlines()[0]
        print(f"  layer 2  proved domain  -> DomainError: {first}")
        print("           Rejected before reaching Rust, using the bound proved by")
        print("           max_profit_fits_i64 -- not a bound someone guessed.\n")

    try:
        rocq.run_orders(2**62, [rocq.Order(True, 2**62)])
        print("  gate domain -> no error (unexpected)")
        return 1
    except rocq.DomainError as e:
        print(f"  risk gate               -> DomainError: {str(e).splitlines()[0]}")
        print("           step evaluates `pos + qty` before rejecting it, so that")
        print("           sum must fit too -- step_fits_i64.\n")

    # And the safe domain is genuinely usable: right at the boundary it works.
    edge = [-rocq.SAFE_PRICE_BOUND, rocq.SAFE_PRICE_BOUND]
    assert rocq.max_profit(edge) == py_max_profit(edge)
    print(f"  at the proved boundary (+/-{rocq.SAFE_PRICE_BOUND}):")
    print(f"    max_profit -> {rocq.max_profit(edge)}  (matches the true answer)")

    # ------------------------------------------------------------- timing
    rule("6. cost of the FFI round trip")

    big = [random.randint(0, 1_000_000) for _ in range(2_000)]
    t0 = time.perf_counter()
    rocq.max_profit(big)
    t_rocq = time.perf_counter() - t0

    t0 = time.perf_counter()
    py_max_profit(big)
    t_py = time.perf_counter() - t0

    print(f"  max_profit over {len(big)} points")
    print(f"    extracted (O(n),   via ctypes) : {t_rocq * 1e3:8.3f} ms")
    print(f"    Python    (O(n^2), naive spec) : {t_py * 1e3:8.3f} ms")
    print("  (different complexity classes -- this compares the shipped")
    print("   algorithm against the specification, not Rust against Python)")

    print("\nAll checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
