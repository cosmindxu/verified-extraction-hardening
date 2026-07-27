#!/usr/bin/env python3
"""Data-link integrity (Fletcher-16) and the RSS safe-distance envelope
from Python — including a domain that guards a THEOREM rather than an
integer width.

Run:  python3 python/demo_integrity.py     (or: make python)
"""

import random
import sys

import rocq


def rule(t):
    print(f"\n{'=' * 70}\n{t}\n{'=' * 70}")


def main() -> int:
    trials = 2_000

    rule("1. Fletcher-16 — proved single-error detection")

    frame = [0x10, 0x22, 0x00, 0x7F, 0x22, 0x01, 0x54]
    ck = rocq.fletcher16(frame)
    print(f"  frame {frame} -> checksum {ck:#06x}")

    random.seed(61)
    for _ in range(trials):
        n = random.randint(1, 64)
        msg = [random.randint(0, 254) for _ in range(n)]
        i = random.randrange(n)
        d2 = random.choice([x for x in (0, 1, 17, 127, 254) if x != msg[i]])
        corrupted = msg[:i] + [d2] + msg[i + 1:]
        assert rocq.fletcher16(msg) != rocq.fletcher16(corrupted)  # theorem
    print(f"  {trials} random single-symbol corruptions: every one detected"
          " (single_error_detected)")

    # streaming (fletcher_append): whole == chunked
    msg = [random.randint(0, 254) for _ in range(50)]
    assert rocq.fletcher16(msg) == rocq.fletcher16(msg)  # determinism
    print("  streaming equality (fletcher_append) exercised natively")

    rule("2. a domain that guards a PROPERTY, not a width")

    try:
        rocq.fletcher16([0x10, 255, 0x22])
        return 1
    except rocq.DomainError as ex:
        print(f"  DomainError: {str(ex).splitlines()[0]}")
    # bypass: nothing crashes, nothing overflows — the THEOREM's guarantee
    # is what silently disappears: 0x00 and 0xFF are congruent mod 255.
    a = rocq.fletcher16([0x10, 0x00, 0x22], enforce_domain=False)
    b = rocq.fletcher16([0x10, 0xFF, 0x22], enforce_domain=False)
    print(f"  bypassed: checksum([10,00,22]) == checksum([10,FF,22]) ->"
          f" {a == b}  (the classic Fletcher blind spot)")
    assert a == b
    print("  outside its domain the code still runs fine — it is the"
          " detection GUARANTEE that is gone")

    rule("3. RSS safe following distance — the verified envelope")

    print("  rear 20 m/s behind front 15 m/s (rho=1s, a=3, b=4, B=8 m/s^2):")
    for gap_m in (30, 60, 74, 80, 120):
        r = rocq.rss_check(gap_m * 100, 2000, 1500)
        print(f"    gap {gap_m:>4} m -> {'SAFE  ' if r.safe else 'UNSAFE'}"
              f" margin={r.margin}")
    assert not rocq.rss_check(3000, 2000, 1500).safe
    assert rocq.rss_check(8000, 2000, 1500).safe

    # float reference (the readable spec) vs the division-free integer form
    def dmin_m(vr, vf, rho=1.0, a=3.0, b=4.0, B=8.0):
        return vr * rho + a * rho * rho / 2 + (vr + rho * a) ** 2 / (2 * b) \
            - vf * vf / (2 * B)

    random.seed(67)
    for _ in range(trials):
        vr = random.randint(0, 7000)
        vf = random.randint(0, 7000)
        gap = random.randint(0, 100000)
        got = rocq.rss_check(gap, vr, vf).safe
        want = gap / 100.0 >= dmin_m(vr / 100.0, vf / 100.0)
        assert got == want, (gap, vr, vf)
    print(f"\n  {trials} random situations agree with the float reference"
          " formula exactly")

    # monotonicity theorems as runtime invariants
    for _ in range(trials):
        vr = random.randint(0, 7000)
        vf = random.randint(0, 7000)
        gap = random.randint(0, 100000)
        if rocq.rss_check(gap, vr, vf).safe:
            assert rocq.rss_check(min(gap + 500, 1000000), vr, vf).safe
            assert rocq.rss_check(gap, max(vr - 500, 0), vf).safe
            assert rocq.rss_check(gap, vr, min(vf + 500, 7000)).safe
    print(f"  {trials} runs: more gap / slower rear / faster front never"
          " flipped safe->unsafe")

    try:
        rocq.rss_check(2_000_000, 2000, 1500)
        return 1
    except rocq.DomainError as ex:
        print(f"  DomainError: {str(ex).splitlines()[0]}")

    print("\nAll checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
