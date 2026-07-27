#!/usr/bin/env python3
"""Safety-critical verified cores from Python: state machines, controllers,
sensor fusion. Each section exercises the theorems of one Rocq module and
differentially tests the extracted code against a Python reference.

Run:  python3 python/demo_safety.py     (or: make python)
"""

import random
import sys

import rocq


def rule(t):
    print(f"\n{'=' * 68}\n{t}\n{'=' * 68}")


def main() -> int:
    trials = 2_000

    # ------------------------------------------------------------ drive FSM
    rule("1. drive-mode FSM (PRND + fault) — shift interlocks as theorems")

    seq = [
        ("shift", "drive", 0),        # engage Drive at standstill
        ("shift", "reverse", 500),    # 5 m/s: direction interlock REJECTS
        ("shift", "neutral", 500),    # neutral always allowed
        ("shift", "reverse", 120),    # 1.2 m/s: allowed
        ("shift", "park", 80),        # 0.8 m/s: park pawl REJECTS
        ("shift", "park", 10),        # near standstill: allowed
        "fault",                      # diagnostic trips
        ("shift", "drive", 0),        # ignored: fault is absorbing
        ("clear", 30),                # clear NOT at standstill: ignored
        ("clear", 0),                 # standstill clear -> Park
    ]
    trace = []
    for i in range(len(seq)):
        trace.append(rocq.drive_fsm_run(seq[: i + 1]))
    for ev, m in zip(seq, trace):
        print(f"  {str(ev):<28} -> {m}")
    assert trace == ["drive", "drive", "neutral", "reverse", "reverse",
                     "park", "fault", "fault", "fault", "park"]

    def py_drive(events):
        P_ENGAGE, SHIFT_DIR = 30, 150
        m = "park"
        for ev in events:
            if ev == "fault":
                m = "fault"
            elif ev[0] == "clear":
                if m == "fault" and ev[1] == 0:
                    m = "park"
            else:
                _, g, v = ev
                if m == "fault":
                    continue
                ok = {"park": -P_ENGAGE <= v <= P_ENGAGE,
                      "neutral": True,
                      "reverse": -SHIFT_DIR <= v <= SHIFT_DIR,
                      "drive": -SHIFT_DIR <= v}[g]
                if ok:
                    m = g
        return m

    random.seed(21)
    gears = ["park", "reverse", "neutral", "drive"]
    for _ in range(trials):
        evs = []
        for _ in range(random.randint(0, 25)):
            x = random.random()
            if x < 0.75:
                evs.append(("shift", random.choice(gears),
                            random.randint(-(2**63), 2**63 - 1)
                            if random.random() < 0.2 else random.randint(-400, 400)))
            elif x < 0.85:
                evs.append("fault")
            else:
                evs.append(("clear", random.choice([0, 0, 17])))
        assert rocq.drive_fsm_run(evs) == py_drive(evs)
    print(f"\n  {trials} random event streams (speeds across full i64) agree"
          " with reference")

    # ---------------------------------------------------------- energy FSM
    rule("2. hybrid energy FSM — SoC bounds + EV floor for ALL inputs")

    def py_energy(soc0, reqs):
        LO, HI, DRN, HDRN, CHG, RGN = 200, 850, 8, 3, 5, 6
        clamp = lambda x: min(1000, max(0, x))
        mode, soc = "charge_sustain", clamp(soc0)
        for r in reqs:
            if r < 0:
                soc = clamp(soc + RGN)
                continue
            d = min(DRN, r)
            if mode == "ev_only":
                if soc - d < LO:
                    mode, soc = "charge_sustain", clamp(soc + CHG)
                elif r > DRN:
                    mode, soc = "hybrid_assist", soc - HDRN
                else:
                    soc = soc - d
            elif mode == "hybrid_assist":
                if soc - HDRN < LO:
                    mode, soc = "charge_sustain", clamp(soc + CHG)
                elif r <= DRN:
                    mode, soc = "ev_only", soc - HDRN
                else:
                    soc = soc - HDRN
            else:
                if soc + CHG >= HI:
                    mode, soc = "ev_only", clamp(soc + CHG)
                else:
                    soc = clamp(soc + CHG)
        return mode, soc

    random.seed(23)
    floor_hits = 0
    for _ in range(trials):
        soc0 = random.randint(-500, 1500)
        reqs = [random.randint(-(2**63), 2**63 - 1) if random.random() < 0.1
                else random.randint(-30, 30)
                for _ in range(random.randint(0, 60))]
        st = rocq.energy_fsm_run(soc0, reqs)
        assert (st.mode, st.soc) == py_energy(soc0, reqs)
        assert 0 <= st.soc <= 1000                        # run_soc_bounds
        if st.mode == "ev_only":
            assert st.soc >= 200                          # run_ev_floor
            floor_hits += 1
    print(f"  {trials} random runs (requests across full i64): SoC always in"
          f" [0,1000];")
    print(f"  EV floor checked on {floor_hits} ev_only outcomes — never below 200")

    # ----------------------------------------------------------------- PID
    rule("3. PID — saturation unconditional, i64 domain proved + enforced")

    def py_pid(kp, ki, kd, errors):
        I_MAX, U_MAX = 2**31, 10**6
        clamp = lambda lo, hi, x: min(hi, max(lo, x))
        integ, prev, outs = 0, 0, []
        for e in errors:
            integ = clamp(-I_MAX, I_MAX, integ + e)
            raw = kp * e + ki * integ + kd * (e - prev)
            outs.append(clamp(-U_MAX, U_MAX, raw))
            prev = e
        return outs, integ, prev

    random.seed(29)
    for _ in range(trials):
        kp, ki, kd = (random.randint(-(2**15), 2**15) for _ in range(3))
        errs = [random.randint(-(2**31), 2**31) for _ in range(random.randint(0, 40))]
        got = rocq.pid_run(kp, ki, kd, errs)
        want = py_pid(kp, ki, kd, errs)
        assert (got.outputs, got.integral, got.prev_error) == want
        assert all(-10**6 <= u <= 10**6 for u in got.outputs)   # saturation
        assert -(2**31) <= got.integral <= 2**31                # anti-windup
    print(f"  {trials} random gain/error runs at the FULL proved domain agree"
          " with reference;")
    print("  every output saturated, integral always clamped")
    try:
        rocq.pid_run(2**15 + 1, 0, 0, [1])
        return 1
    except rocq.DomainError as e:
        print(f"  rejected: {str(e).splitlines()[0]}")

    # ---------------------------------------------------------- thermostat
    rule("4. hysteresis thermostat — closed-loop invariant band")

    st = rocq.thermo_run(2000, [(37, 23)] * 200)
    print(f"  from 200.0 C: after 200 steps -> {st}  (band is [130, 270])")
    assert 130 <= st.temp <= 270

    def py_thermo(t0, rates):
        T_LO, T_HI, RMAX = 180, 220, 50
        eff = lambda r: min(RMAX, max(1, r))
        t, h = t0, False
        for rh, rc in rates:
            h = True if t <= T_LO else (False if t >= T_HI else h)
            t = t + eff(rh) if h else t - eff(rc)
        return t, h

    random.seed(31)
    captured = 0
    for _ in range(trials):
        t0 = random.randint(-3000, 3000)
        rates = [(random.randint(-100, 100), random.randint(-100, 100))
                 for _ in range(random.randint(0, 80))]
        got = rocq.thermo_run(t0, rates)
        assert (got.temp, got.heating) == py_thermo(t0, rates)
        # once inside the band, never out again (band_invariant)
        t, h, inside = t0, False, 130 <= t0 <= 270
        for rh, rc in rates:
            h = True if t <= 180 else (False if t >= 220 else h)
            t = t + min(50, max(1, rh)) if h else t - min(50, max(1, rc))
            if inside:
                assert 130 <= t <= 270
            inside = inside or 130 <= t <= 270
        if inside:
            captured += 1
    print(f"  {trials} random runs agree with reference; band never exited"
          f" after capture ({captured} captured)")

    # ----------------------------------------------------------------- MPC
    rule("5. finite-set MPC — optimality over the whole action tree")

    def py_rollout(r, pos, vel, sigma):
        c = 0
        for a in sigma:
            pos, vel = pos + vel, vel + 10 * a
            c += (pos - r) ** 2 + vel ** 2
        return c

    def py_exhaustive(r, pos, vel, h):
        from itertools import product
        return min(py_rollout(r, pos, vel, s) for s in product((-1, 0, 1), repeat=h))

    random.seed(37)
    small_trials = 300           # 3^5 rollouts per trial in pure Python
    for _ in range(small_trials):
        r = random.randint(-(2**20), 2**20)
        pos = random.randint(-(2**20), 2**20)
        vel = random.randint(-1000, 1000)
        d = rocq.mpc_decide(r, pos, vel, 5)
        assert d.cost == py_exhaustive(r, pos, vel, 5), (r, pos, vel)
        assert d.action in (-1, 0, 1)
    print(f"  {small_trials} random states: extracted cost == exhaustive"
          " min over all 3^5 sequences")
    d0 = rocq.mpc_decide(1000, 0, 0, 5)
    print(f"  e.g. tracking ref=1000 from rest: action={d0.action:+d},"
          f" predicted cost={d0.cost}")
    try:
        rocq.mpc_decide(2**20 + 1, 0, 0, 5)
        return 1
    except rocq.DomainError as e:
        print(f"  rejected: {str(e).splitlines()[0]}")

    # -------------------------------------------------------------- fusion
    rule("6. sensor fusion — median + plausibility, majority fault masking")

    speeds = [352, 351, 349, 990, 350]     # 4 healthy sensors + 1 faulty
    rep = rocq.fuse(speeds, tol=5)
    print(f"  readings {speeds}, tol=5")
    print(f"    fused = {rep.fused}, plausible = {rep.plausible}")
    assert rep.fused in speeds                              # median_in_inputs
    assert rep.plausible == [True, True, True, False, True]

    random.seed(41)
    masked = 0
    for _ in range(trials):
        n = random.choice([3, 5, 7, 9])
        true_v = random.randint(-10**6, 10**6)
        band = random.randint(1, 50)
        k_faulty = random.randint(0, (n - 1) // 2)          # strict minority
        readings = [true_v + random.randint(-band, band) for _ in range(n - k_faulty)]
        readings += [random.randint(-(2**60), 2**60) for _ in range(k_faulty)]
        random.shuffle(readings)
        rep = rocq.fuse(readings, tol=2 * band)
        assert rep.fused in readings                        # median_in_inputs
        # majority_band: majority within [true_v - band, true_v + band]
        assert true_v - band <= rep.fused <= true_v + band, (readings, rep)
        # scene consistency: accepted pairwise within 2*tol
        acc = [r for r, ok in zip(readings, rep.plausible) if ok]
        for a in acc:
            for b in acc:
                assert abs(a - b) <= 4 * band
        if k_faulty:
            masked += 1
    print(f"  {trials} random scenes (up to minority arbitrary-faulty"
          " sensors):")
    print(f"    fused stayed in the healthy majority's band every time"
          f" ({masked} scenes had faults);")
    print("    accepted readings always pairwise consistent")

    print("\nAll checks passed.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
