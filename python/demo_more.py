#!/usr/bin/env python3
"""Three more Rocq-proved algorithms from Python — three overflow postures.

  RLE codec   : no arithmetic to leak       (roundtrip + buffer theorems)
  pow_mod     : proved domain, enforced     (modulus <= 2^32)
  order FSM   : overflow designed out       (safe for ALL inputs)

Run:  python3 python/demo_more.py     (or: make python)
"""

import random
import sys

import rocq


def rule(title):
    print(f"\n{'=' * 68}\n{title}\n{'=' * 68}")


def main() -> int:
    rule("1. RLE codec — posture: no arithmetic to leak")

    xs = [7, 7, 7, 7, 2, 2, 9, 9, 9, 9, 9, 9, 1]
    runs = rocq.rle_encode(xs)
    back = rocq.rle_decode(runs)
    print(f"  input  : {xs}")
    print(f"  encode : {runs}")
    print(f"  decode : {back}")
    assert back == xs

    random.seed(3)
    trials = 2_000
    for _ in range(trials):
        n = random.randint(0, 50)
        # small alphabet -> long runs
        case = [random.randint(-3, 3) for _ in range(n)]
        runs = rocq.rle_encode(case)
        assert rocq.rle_decode(runs) == case          # rle_roundtrip
        assert len(runs) <= len(case)                 # encode_length_le
        assert all(c >= 1 for _, c in runs)           # encode_counts_pos
    print(f"\n  {trials} random lists: roundtrip, length bound, positive counts OK")

    rule("2. pow_mod — posture: proved domain (modulus <= 2^32)")

    m, b, e = 1_000_000_007, 2, 10**18
    got = rocq.pow_mod(m, b, e)
    want = pow(b, e, m)
    print(f"  pow_mod({m}, {b}, {e})")
    print(f"    extracted: {got}")
    print(f"    python   : {want}")
    assert got == want

    random.seed(5)
    for _ in range(trials):
        m = random.randint(1, rocq.SAFE_MODULUS)
        b = random.randint(0, 2**64 - 1)
        e = random.randint(0, 2**64 - 1)
        assert rocq.pow_mod(m, b, e) == pow(b, e, m), (m, b, e)
    print(f"  {trials} random (m,b,e) with m in [1, 2^32]: agree with pow(b,e,m)")

    # At the proved boundary, and just past it.
    m_edge = rocq.SAFE_MODULUS
    assert rocq.pow_mod(m_edge, 2**63, 2**63) == pow(2**63, 2**63, m_edge)
    print(f"  at the boundary m = 2^32: correct")
    for bad, why in (
        (lambda: rocq.pow_mod(0, 2, 3), "m = 0 outside pow_mod_correct"),
        (lambda: rocq.pow_mod(rocq.SAFE_MODULUS + 1, 2, 3), "m > SAFE_MODULUS"),
    ):
        try:
            bad()
            print(f"  NOT rejected: {why}")
            return 1
        except rocq.DomainError as exc:
            print(f"  rejected ({why}): {str(exc).splitlines()[0]}")

    rule("3. order FSM — posture: overflow designed out (safe for ALL inputs)")

    st = rocq.run_order_events(
        100,
        [("fill", 60), ("fill", 60), ("fill", 40), ("fill", -5), "cancel", ("fill", 1)],
    )
    print("  order qty=100, events: fill 60, fill 60(reject: overfill), fill 40,")
    print("                         fill -5(reject: negative), cancel, fill 1(frozen)")
    print(f"  -> filled={st.filled}, canceled={st.canceled}")
    assert st == (100, True)

    def py_fsm(qty, events):
        filled, canceled = 0, False
        for ev in events:
            if canceled:
                continue
            if ev == "cancel":
                canceled = True
            else:
                _, n = ev
                if 0 <= n <= qty - filled:
                    filled += n
        return filled, canceled

    random.seed(9)
    for _ in range(trials):
        qty = random.randint(0, 10**12)
        evs = []
        for _ in range(random.randint(0, 30)):
            if random.random() < 0.1:
                evs.append("cancel")
            else:
                # adversarial: quantities across the whole i64 range
                evs.append(("fill", random.randint(-(2**63), 2**63 - 1)))
        got = rocq.run_order_events(qty, evs)
        assert (got.filled, got.canceled) == py_fsm(qty, evs)
        assert 0 <= got.filled <= qty                  # run_invariant
    print(f"\n  {trials} adversarial event streams (fills across full i64):")
    print("    agree with reference; 0 <= filled <= qty held every time;")
    print("    checked build never panicked — overflow designed out, not guarded in")

    print("\nAll checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
