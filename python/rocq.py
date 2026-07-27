"""Python bindings for algorithms proved in Rocq and extracted to Rust.

The implementations behind these functions were not written in Rust by hand.
They were written and proved in Rocq (see ``theories/``), erased to Rust by
MetaRocq's verified typed erasure, compiled to a ``cdylib``, and are reached
here through ``ctypes``.

    >>> import rocq
    >>> rocq.sort([5, 3, 8, 1])
    [1, 3, 5, 8]
    >>> rocq.max_profit([10, 7, 5, 8, 11, 9])
    6

What is actually proved (all ``Closed under the global context``):

===================== ==================================================
``sort``              output is sorted, and a permutation of the input
``max_profit``        equals the naive max-over-all-pairs specification
``max_drawdown``      equals the naive max-over-all-pairs specification
``run_orders``        position never leaves ``[-limit, limit]``
``rle_encode/decode`` round trip; output length bounds
``pow_mod``           equals ``(b ** e) % m`` for ``0 < m <= 2**32``
``run_order_events``  ``0 <= filled <= qty`` for every event stream
===================== ==================================================

Prices and quantities are integers (ticks or cents). That is not an
interface simplification -- the Rocq proofs are about integers, so passing
floats would step outside what was proved. Floats are rejected rather than
silently rounded.
"""

from __future__ import annotations

import ctypes
import os
from typing import Iterable, NamedTuple, Sequence

__all__ = [
    "Order",
    "Analytics",
    "RocqError",
    "DomainError",
    "SAFE_PRICE_BOUND",
    "I64_MIN",
    "I64_MAX",
    "SAFE_MODULUS",
    "sort",
    "max_profit",
    "max_drawdown",
    "run_orders",
    "analyze",
    "rle_encode",
    "rle_decode",
    "pow_mod",
    "run_order_events",
    "library_path",
]

I64_MIN, I64_MAX = -(2**63), 2**63 - 1
_I64_MIN, _I64_MAX = I64_MIN, I64_MAX

#: Largest price magnitude for which no intermediate of ``max_profit`` or
#: ``max_drawdown`` can leave ``i64``. This is not a guess: it is
#: ``safe_price_bound`` in ``theories/Trading.v``, and ``max_profit_fits_i64``
#: / ``max_drawdown_fits_i64`` prove it suffices. ``mp_bounded`` /
#: ``mdd_bounded`` bound every intermediate of the scans, not just the result.
SAFE_PRICE_BOUND = 4_611_686_018_427_387_903  # 2**62 - 1

_DEFAULT_LIB = os.path.join(
    os.path.dirname(os.path.abspath(__file__)),
    "..",
    "rust",
    "rocq_ffi",
    "target",
    "release",
    "librocq_ffi.so",
)


class RocqError(RuntimeError):
    """The native layer reported a failure."""


class DomainError(ValueError):
    """Input is outside the range the Rocq proofs cover for i64.

    Every value was individually a legal ``i64``, but the algorithm would
    compute an intermediate that is not, so the extracted Rust would leave
    the domain where its theorems apply.
    """


_STATUS = {
    -1: "null pointer passed with a non-zero length",
    -2: "the extracted code panicked (contained at the FFI boundary)",
    -3: "output exceeded the provided buffer capacity",
}


def _check(code: int) -> None:
    if code != 0:
        raise RocqError(_STATUS.get(code, f"unknown status {code}"))


def _load() -> ctypes.CDLL:
    path = os.environ.get("ROCQ_FFI_LIB", _DEFAULT_LIB)
    if not os.path.exists(path):
        raise RocqError(
            f"native library not found at {path}\n"
            "Build it with:  make python   (or: cd rust/rocq_ffi && cargo build --release)\n"
            "Or point ROCQ_FFI_LIB at librocq_ffi.so."
        )
    lib = ctypes.CDLL(os.path.abspath(path))

    i64p = ctypes.POINTER(ctypes.c_int64)
    u8p = ctypes.POINTER(ctypes.c_uint8)

    lib.rocq_sort_i64.argtypes = [i64p, ctypes.c_size_t, i64p]
    lib.rocq_sort_i64.restype = ctypes.c_int32

    for name in (
        "rocq_max_profit",
        "rocq_max_drawdown",
        "rocq_max_profit_checked",
        "rocq_max_drawdown_checked",
    ):
        fn = getattr(lib, name)
        fn.argtypes = [i64p, ctypes.c_size_t, i64p]
        fn.restype = ctypes.c_int32

    for name in ("rocq_run_orders", "rocq_run_orders_checked"):
        fn = getattr(lib, name)
        fn.argtypes = [
            ctypes.c_int64, ctypes.c_int64, u8p, i64p, ctypes.c_size_t, i64p
        ]
        fn.restype = ctypes.c_int32

    u64p = ctypes.POINTER(ctypes.c_uint64)
    szp = ctypes.POINTER(ctypes.c_size_t)

    lib.rocq_rle_encode.argtypes = [i64p, ctypes.c_size_t, i64p, u64p, szp]
    lib.rocq_rle_encode.restype = ctypes.c_int32
    lib.rocq_rle_decode.argtypes = [
        i64p, u64p, ctypes.c_size_t, i64p, ctypes.c_size_t, szp
    ]
    lib.rocq_rle_decode.restype = ctypes.c_int32

    lib.rocq_pow_mod.argtypes = [
        ctypes.c_uint64, ctypes.c_uint64, ctypes.c_uint64, u64p
    ]
    lib.rocq_pow_mod.restype = ctypes.c_int32

    lib.rocq_drive_fsm_run.argtypes = [u8p, u8p, i64p, ctypes.c_size_t, u8p]
    lib.rocq_drive_fsm_run.restype = ctypes.c_int32
    lib.rocq_energy_fsm_run.argtypes = [
        ctypes.c_int64, i64p, ctypes.c_size_t, u8p, i64p
    ]
    lib.rocq_energy_fsm_run.restype = ctypes.c_int32
    lib.rocq_pid_run.argtypes = [
        ctypes.c_int64, ctypes.c_int64, ctypes.c_int64,
        i64p, ctypes.c_size_t, i64p, i64p, i64p,
    ]
    lib.rocq_pid_run.restype = ctypes.c_int32
    lib.rocq_thermo_run.argtypes = [
        ctypes.c_int64, i64p, i64p, ctypes.c_size_t, i64p, u8p
    ]
    lib.rocq_thermo_run.restype = ctypes.c_int32
    lib.rocq_mpc_decide.argtypes = [
        ctypes.c_int64, ctypes.c_int64, ctypes.c_int64, ctypes.c_uint64,
        i64p, ctypes.POINTER(ctypes.c_int8),
    ]
    lib.rocq_mpc_decide.restype = ctypes.c_int32
    lib.rocq_fusion_fuse.argtypes = [
        ctypes.c_int64, i64p, ctypes.c_size_t, i64p, u8p
    ]
    lib.rocq_fusion_fuse.restype = ctypes.c_int32

    lib.rocq_scene_check.argtypes = [
        ctypes.c_int64, ctypes.c_int64, ctypes.c_int64, ctypes.c_int64,
        ctypes.c_int64,
        u8p, i64p, i64p, i64p, i64p, i64p, i64p, i64p, u8p, i64p,
        ctypes.c_size_t,
        u8p, u8p, i64p, i64p,
    ]
    lib.rocq_scene_check.restype = ctypes.c_int32

    lib.rocq_scene_world_check.argtypes = [
        ctypes.c_int64, ctypes.c_int64, ctypes.c_int64, ctypes.c_int64,
        ctypes.c_int64, ctypes.c_int64, ctypes.c_int64, ctypes.c_int64,
        ctypes.c_int64,
        u8p, i64p, i64p, i64p, i64p, i64p, i64p, i64p, u8p, i64p,
        ctypes.c_size_t,
        u8p, u8p, i64p, i64p,
    ]
    lib.rocq_scene_world_check.restype = ctypes.c_int32

    lib.rocq_fletcher16.argtypes = [i64p, ctypes.c_size_t, i64p, i64p]
    lib.rocq_fletcher16.restype = ctypes.c_int32
    lib.rocq_rss_check.argtypes = [
        ctypes.c_int64, ctypes.c_int64, ctypes.c_int64, ctypes.c_int64,
        ctypes.c_int64, ctypes.c_int64, ctypes.c_int64,
        u8p, i64p,
    ]
    lib.rocq_rss_check.restype = ctypes.c_int32

    lib.rocq_order_fsm_run.argtypes = [
        ctypes.c_int64, u8p, i64p, ctypes.c_size_t, i64p,
        ctypes.POINTER(ctypes.c_uint8),
    ]
    lib.rocq_order_fsm_run.restype = ctypes.c_int32

    for name in ("rocq_analyze", "rocq_analyze_checked"):
        fn = getattr(lib, name)
        fn.argtypes = [
            i64p, ctypes.c_size_t, ctypes.c_int64, u8p, i64p,
            ctypes.c_size_t, i64p
        ]
        fn.restype = ctypes.c_int32

    return lib


_lib = None


def _get() -> ctypes.CDLL:
    global _lib
    if _lib is None:
        _lib = _load()
    return _lib


def library_path() -> str:
    """Absolute path of the shared library these bindings use."""
    return os.path.abspath(os.environ.get("ROCQ_FFI_LIB", _DEFAULT_LIB))


class Order(NamedTuple):
    """A single order. ``buy=False`` is a sell."""

    buy: bool
    qty: int


class Analytics(NamedTuple):
    max_profit: int
    max_drawdown: int
    final_position: int


def _as_i64_array(values: Iterable[int], what: str):
    vals = list(values)
    for i, v in enumerate(vals):
        if isinstance(v, bool) or not isinstance(v, int):
            raise TypeError(
                f"{what}[{i}] must be an int (ticks/cents), got {type(v).__name__}: {v!r}"
            )
        if not _I64_MIN <= v <= _I64_MAX:
            raise OverflowError(f"{what}[{i}] does not fit in int64: {v}")
    arr = (ctypes.c_int64 * len(vals))(*vals)
    return arr, len(vals)


def _as_i64(value: int, what: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{what} must be an int, got {type(value).__name__}: {value!r}")
    if not _I64_MIN <= value <= _I64_MAX:
        raise OverflowError(f"{what} does not fit in int64: {value}")
    return value


def _split_orders(orders: Sequence[Order | tuple[bool, int]]):
    sides, qtys = [], []
    for i, o in enumerate(orders):
        buy, qty = o
        if not isinstance(buy, (bool, int)):
            raise TypeError(f"orders[{i}].buy must be a bool, got {buy!r}")
        qtys.append(_as_i64(int(qty), f"orders[{i}].qty"))
        sides.append(1 if buy else 0)
    n = len(sides)
    return (ctypes.c_uint8 * n)(*sides), (ctypes.c_int64 * n)(*qtys), n


def sort(values: Iterable[int]) -> list[int]:
    """Sort ascending, using the Rocq-proved insertion sort.

    The result is guaranteed sorted and a permutation of the input --
    ``insertion_sort_sorted`` and ``insertion_sort_perm``.

    Protections: values are validated as true ints within i64
    (TypeError/OverflowError; floats and bools rejected, never coerced).
    No proved-domain bound is needed: the sort compares, it never computes,
    so it is total on any i64s.
    """
    arr, n = _as_i64_array(values, "values")
    out = (ctypes.c_int64 * n)()
    _check(_get().rocq_sort_i64(arr, n, out))
    return list(out)


def _enforce_price_domain(values: Sequence[int], what: str) -> None:
    """Reject prices outside the range proved safe for i64.

    Individually every value is a legal i64; the problem is that the scans
    compute differences. ``max_profit_fits_i64`` in theories/Trading.v proves
    ``|p| <= SAFE_PRICE_BOUND`` is enough for every intermediate to stay in
    range, so that is exactly what is enforced.
    """
    for i, v in enumerate(values):
        if not -SAFE_PRICE_BOUND <= v <= SAFE_PRICE_BOUND:
            raise DomainError(
                f"{what}[{i}] = {v} exceeds SAFE_PRICE_BOUND (+/-{SAFE_PRICE_BOUND}).\n"
                f"It is a valid int64, but differences of prices this large "
                f"overflow int64, and the extracted code would silently return "
                f"a wrong answer.\n"
                f"See max_profit_fits_i64 in theories/Trading.v."
            )


def max_profit(
    prices: Iterable[int], *, checked: bool = True, enforce_domain: bool = True
) -> int:
    """Best single buy-then-sell trade; 0 if no trade beats doing nothing.

    ``enforce_domain`` rejects inputs outside the range proved safe for i64.
    ``checked`` selects the build extracted with ``ExtrRustCheckedArith``, in
    which overflow panics (surfacing as ``RocqError``) instead of wrapping.
    Turning both off gives the raw extracted behaviour -- silent wraparound.
    """
    vals = list(prices)
    arr, n = _as_i64_array(vals, "prices")
    if enforce_domain:
        _enforce_price_domain(vals, "prices")
    out = ctypes.c_int64()
    fn = _get().rocq_max_profit_checked if checked else _get().rocq_max_profit
    _check(fn(arr, n, ctypes.byref(out)))
    return out.value


def max_drawdown(
    prices: Iterable[int], *, checked: bool = True, enforce_domain: bool = True
) -> int:
    """Worst peak-to-trough decline; 0 for a non-decreasing series.

    See :func:`max_profit` for ``checked`` / ``enforce_domain``.
    """
    vals = list(prices)
    arr, n = _as_i64_array(vals, "prices")
    if enforce_domain:
        _enforce_price_domain(vals, "prices")
    out = ctypes.c_int64()
    fn = _get().rocq_max_drawdown_checked if checked else _get().rocq_max_drawdown
    _check(fn(arr, n, ctypes.byref(out)))
    return out.value


def run_orders(
    limit: int,
    orders: Sequence[Order | tuple[bool, int]],
    initial: int = 0,
    *,
    checked: bool = True,
    enforce_domain: bool = True,
) -> int:
    """Run ``orders`` through the position-limit risk gate.

    Orders that would push the position outside ``[-limit, limit]`` are
    rejected. The returned position is guaranteed to be inside that interval
    (``run_orders_within_limit``), provided the starting position is --
    which for the default ``initial=0`` means ``limit >= 0``.
    """
    limit = _as_i64(limit, "limit")
    initial = _as_i64(initial, "initial")
    if limit < 0:
        raise ValueError(
            f"limit must be >= 0, got {limit}: the interval [{-limit}, {limit}] is "
            "empty, so run_orders_within_limit offers no guarantee"
        )
    if not -limit <= initial <= limit:
        raise ValueError(
            f"initial position {initial} is outside [{-limit}, {limit}]; "
            "the theorem's hypothesis does not hold, so no guarantee is offered"
        )
    sides, qtys, n = _split_orders(orders)
    if enforce_domain and n:
        # step computes `pos + qty` BEFORE range-checking it, and |pos| <= limit
        # by run_orders_within_limit. So step_fits_i64 requires limit + B <= I64_MAX
        # where B bounds |qty|.
        b = max(abs(q) for q in qtys)
        if limit + b > I64_MAX:
            raise DomainError(
                f"limit ({limit}) + largest |qty| ({b}) = {limit + b} exceeds int64.\n"
                f"The gate evaluates `pos + qty` before rejecting it, so that "
                f"sum must itself be representable.\n"
                f"See step_fits_i64 in theories/Trading.v."
            )
    out = ctypes.c_int64()
    fn = _get().rocq_run_orders_checked if checked else _get().rocq_run_orders
    _check(fn(limit, initial, sides, qtys, n, ctypes.byref(out)))
    return out.value


def analyze(
    prices: Iterable[int],
    limit: int,
    orders: Sequence[Order | tuple[bool, int]],
    *,
    checked: bool = True,
    enforce_domain: bool = True,
) -> Analytics:
    """All three analytics in a single native call.

    Protections mirror the individual entry points: ``enforce_domain``
    applies the proved price domain (``max_profit_fits_i64``), the gate's
    evaluate-before-check obligation (``step_fits_i64``) and the theorem
    hypotheses ``limit >= 0`` / initial position in range; ``checked``
    selects the ExtrRustCheckedArith build so a bypassed overflow panics
    (contained as :class:`RocqError`) instead of wrapping.
    """
    vals = list(prices)
    arr, pn = _as_i64_array(vals, "prices")
    limit = _as_i64(limit, "limit")
    if enforce_domain:
        _enforce_price_domain(vals, "prices")
        if limit < 0:
            raise ValueError(
                f"limit must be >= 0, got {limit}: the interval "
                f"[{-limit}, {limit}] is empty, so run_orders_within_limit "
                f"offers no guarantee"
            )
    sides, qtys, on = _split_orders(orders)
    if enforce_domain and on:
        b = max(abs(q) for q in qtys)
        if limit + b > I64_MAX:
            raise DomainError(
                f"limit ({limit}) + largest |qty| ({b}) exceeds int64; "
                f"see step_fits_i64 in theories/Trading.v"
            )
    out = (ctypes.c_int64 * 3)()
    fn = _get().rocq_analyze_checked if checked else _get().rocq_analyze
    _check(fn(arr, pn, limit, sides, qtys, on, out))
    return Analytics(out[0], out[1], out[2])


U64_MAX = 2**64 - 1

#: Largest modulus for which every intermediate product of ``pow_mod`` fits
#: in u64: ``safe_modulus`` in theories/ModExp.v (``square_fits`` /
#: ``mixed_fits``, given ``pow_mod_lt``).
SAFE_MODULUS = 2**32


def _as_u64(value: int, what: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int):
        raise TypeError(f"{what} must be an int, got {type(value).__name__}: {value!r}")
    if not 0 <= value <= U64_MAX:
        raise OverflowError(f"{what} does not fit in uint64: {value}")
    return value


def rle_encode(values: Iterable[int]) -> list[tuple[int, int]]:
    """Run-length encode into ``[(value, count), ...]``.

    The output buffer is sized to the input length -- sufficient by
    ``encode_length_le`` in theories/Rle.v. Every count is >= 1
    (``encode_counts_pos``). No overflow domain to enforce: the codec
    performs no arithmetic beyond count increments bounded by the input
    length.
    """
    arr, n = _as_i64_array(values, "values")
    out_vals = (ctypes.c_int64 * n)()
    out_counts = (ctypes.c_uint64 * n)()
    out_n = ctypes.c_size_t()
    _check(_get().rocq_rle_encode(arr, n, out_vals, out_counts, ctypes.byref(out_n)))
    k = out_n.value
    return list(zip(out_vals[:k], out_counts[:k]))


def rle_decode(runs: Sequence[tuple[int, int]]) -> list[int]:
    """Expand ``[(value, count), ...]`` runs. Inverse of :func:`rle_encode`
    on its image (``rle_roundtrip``); the output length equals the sum of
    counts (``decode_length``), which is how the buffer is sized here.
    """
    vals, counts = [], []
    for i, (v, c) in enumerate(runs):
        vals.append(_as_i64(v, f"runs[{i}].value"))
        counts.append(_as_u64(c, f"runs[{i}].count"))
    total = sum(counts)
    if total > 2**48:
        raise DomainError(
            f"decoded length {total} is unreasonably large; refusing to allocate"
        )
    n = len(vals)
    va = (ctypes.c_int64 * n)(*vals)
    ca = (ctypes.c_uint64 * n)(*counts)
    out = (ctypes.c_int64 * total)()
    out_len = ctypes.c_size_t()
    _check(_get().rocq_rle_decode(va, ca, n, out, total, ctypes.byref(out_len)))
    return list(out[: out_len.value])


def pow_mod(modulus: int, base: int, exponent: int) -> int:
    """``(base ** exponent) % modulus`` by verified square-and-multiply.

    ``pow_mod_correct`` (theories/ModExp.v) proves equality with the spec
    for ``modulus != 0``; ``modulus <= SAFE_MODULUS`` (2**32) is the proved
    condition (``square_fits``/``mixed_fits``) under which no intermediate
    product can leave u64. Both are enforced here; ``base`` and ``exponent``
    may be any u64.
    """
    m = _as_u64(modulus, "modulus")
    b = _as_u64(base, "base")
    e = _as_u64(exponent, "exponent")
    if m == 0:
        raise DomainError(
            "modulus 0 is outside the correctness theorem (pow_mod_correct "
            "assumes m <> 0); Rocq's x mod 0 = x convention is not a modulus"
        )
    if m > SAFE_MODULUS:
        raise DomainError(
            f"modulus {m} exceeds SAFE_MODULUS ({SAFE_MODULUS}). It is a valid "
            f"uint64, but intermediate products of values < m would overflow "
            f"u64. See square_fits/mixed_fits in theories/ModExp.v."
        )
    out = ctypes.c_uint64()
    _check(_get().rocq_pow_mod(m, b, e, ctypes.byref(out)))
    return out.value


class OrderState(NamedTuple):
    filled: int
    canceled: bool


def run_order_events(
    qty: int, events: Sequence[tuple[str, int] | str]
) -> OrderState:
    """Run fill/cancel events against a fresh order of size ``qty``.

    Events: ``("fill", n)`` or ``"cancel"``. Guaranteed by ``run_invariant``
    (theories/OrderFsm.v): ``0 <= filled <= qty`` for EVERY event stream --
    negative and overfilling fills are rejected by the machine itself, and
    ``canceled_frozen`` freezes the state after a cancel. No domain to
    enforce beyond ``qty >= 0``: the guard compares before adding
    (``fill_add_bounded``), so overflow is designed out.
    """
    q = _as_i64(qty, "qty")
    if q < 0:
        raise ValueError(f"qty must be >= 0, got {q} (init_run_invariant needs 0 <= qty)")
    fills, qtys = [], []
    for i, ev in enumerate(events):
        if ev == "cancel" or ev == ("cancel",):
            fills.append(0)
            qtys.append(0)
        else:
            tag, n = ev
            if tag != "fill":
                raise ValueError(f"events[{i}]: unknown event {ev!r}")
            fills.append(1)
            qtys.append(_as_i64(n, f"events[{i}].qty"))
    k = len(fills)
    fa = (ctypes.c_uint8 * k)(*fills)
    qa = (ctypes.c_int64 * k)(*qtys)
    out_filled = ctypes.c_int64()
    out_canceled = ctypes.c_uint8()
    _check(_get().rocq_order_fsm_run(
        q, fa, qa, k, ctypes.byref(out_filled), ctypes.byref(out_canceled)
    ))
    return OrderState(out_filled.value, bool(out_canceled.value))


# --------------------------------------------------------------------------
# Safety-critical examples: FSMs, controllers, sensor fusion
# --------------------------------------------------------------------------

#: PID proved domain (Pid.v: raw_fits_i64): |gain| <= 2^15, |error| <= 2^31.
PID_GAIN_MAX = 2**15
PID_ERR_MAX = 2**31
#: Thermostat proved domain (Hysteresis.v: step_fits_i64): |t0| <= 2^62.
THERMO_T_MAX = 2**62
#: MPC proved domain (Mpc.v): |pos|,|vel|,|ref| <= 2^20, horizon <= 8.
MPC_STATE_MAX = 2**20
MPC_HORIZON_MAX = 8

_DRIVE_MODES = ["park", "reverse", "neutral", "drive", "fault"]
_ENERGY_MODES = ["ev_only", "hybrid_assist", "charge_sustain"]
_GEARS = {"park": 0, "reverse": 1, "neutral": 2, "drive": 3}


def drive_fsm_run(events: Sequence[tuple]) -> str:
    """Run the PRND+Fault gear FSM from Park; returns the final mode name.

    Events: ``("shift", gear_name, speed_cm_s)``, ``("fault",)`` or
    ``"fault"``, ``("clear", speed_cm_s)``. Shift interlocks are theorems
    (park/reverse/drive gates, absorbing fault — DriveModeFsm.v). Speeds
    are only compared, never computed with, so ANY i64 speed is safe.
    """
    tags, gears, speeds = [], [], []
    for i, ev in enumerate(events):
        if ev == "fault" or ev == ("fault",):
            tags.append(1); gears.append(0); speeds.append(0)
        else:
            kind = ev[0]
            if kind == "shift":
                _, gname, v = ev
                if gname not in _GEARS:
                    raise ValueError(f"events[{i}]: unknown gear {gname!r}")
                tags.append(0); gears.append(_GEARS[gname])
                speeds.append(_as_i64(v, f"events[{i}].speed"))
            elif kind == "clear":
                _, v = ev
                tags.append(2); gears.append(0)
                speeds.append(_as_i64(v, f"events[{i}].speed"))
            else:
                raise ValueError(f"events[{i}]: unknown event {ev!r}")
    n = len(tags)
    ta = (ctypes.c_uint8 * n)(*tags)
    ga = (ctypes.c_uint8 * n)(*gears)
    sa = (ctypes.c_int64 * n)(*speeds)
    out = ctypes.c_uint8()
    _check(_get().rocq_drive_fsm_run(ta, ga, sa, n, ctypes.byref(out)))
    return _DRIVE_MODES[out.value]


class EnergyState(NamedTuple):
    mode: str
    soc: int


def energy_fsm_run(soc0: int, requests: Iterable[int]) -> EnergyState:
    """Run the hybrid energy FSM. SoC in per-mille; requests arbitrary i64
    (positive = propulsion, negative = braking/regen).

    Proved for EVERY request stream (HybridEnergyFsm.v): 0 <= soc <= 1000
    and the EV floor (mode ev_only implies soc >= 200). Nothing to enforce.
    """
    arr, n = _as_i64_array(requests, "requests")
    s0 = _as_i64(soc0, "soc0")
    out_m = ctypes.c_uint8()
    out_s = ctypes.c_int64()
    _check(_get().rocq_energy_fsm_run(s0, arr, n, ctypes.byref(out_m), ctypes.byref(out_s)))
    return EnergyState(_ENERGY_MODES[out_m.value], out_s.value)


class PidResult(NamedTuple):
    outputs: list[int]
    integral: int
    prev_error: int


def pid_run(kp: int, ki: int, kd: int, errors: Iterable[int]) -> PidResult:
    """Run the verified integer PID from the zero state.

    Unconditionally proved (Pid.v): every output saturated to
    [-1_000_000, 1_000_000] and the integral clamped (anti-windup). The
    proved i64 domain — |gains| <= 2^15, |errors| <= 2^31 (raw_fits_i64) —
    is enforced here, because ``raw`` is computed BEFORE the output clamp.
    """
    for name, g in (("kp", kp), ("ki", ki), ("kd", kd)):
        g = _as_i64(g, name)
        if not -PID_GAIN_MAX <= g <= PID_GAIN_MAX:
            raise DomainError(
                f"{name} = {g} exceeds PID_GAIN_MAX (+/-{PID_GAIN_MAX}); "
                f"outside raw_fits_i64 (theories/Pid.v) the intermediate "
                f"products may overflow i64"
            )
    vals = list(errors)
    arr, n = _as_i64_array(vals, "errors")
    for i, e in enumerate(vals):
        if not -PID_ERR_MAX <= e <= PID_ERR_MAX:
            raise DomainError(
                f"errors[{i}] = {e} exceeds PID_ERR_MAX (+/-{PID_ERR_MAX}); "
                f"see raw_fits_i64 in theories/Pid.v"
            )
    out_us = (ctypes.c_int64 * n)()
    out_i = ctypes.c_int64()
    out_p = ctypes.c_int64()
    _check(_get().rocq_pid_run(kp, ki, kd, arr, n, out_us,
                               ctypes.byref(out_i), ctypes.byref(out_p)))
    return PidResult(list(out_us), out_i.value, out_p.value)


class ThermoState(NamedTuple):
    temp: int
    heating: bool


def thermo_run(t0: int, rates: Sequence[tuple[int, int]]) -> ThermoState:
    """Run the hysteresis thermostat closed loop from ``t0`` (deci-deg C).

    ``rates`` are per-step (heat_rate, cool_rate) disturbances; the machine
    clamps them into [1, 50]. Proved (Hysteresis.v): the band
    [T_LO-RMAX, T_HI+RMAX] = [130, 270] is invariant, no chattering inside
    the gap, strict progress toward the band outside it. The bindings
    enforce |t0| <= 2^62 (step_fits_i64).
    """
    t0 = _as_i64(t0, "t0")
    if not -THERMO_T_MAX <= t0 <= THERMO_T_MAX:
        raise DomainError(
            f"t0 = {t0} exceeds THERMO_T_MAX (+/-{THERMO_T_MAX}); "
            f"see step_fits_i64 in theories/Hysteresis.v"
        )
    rhs = [_as_i64(a, f"rates[{i}].heat") for i, (a, _) in enumerate(rates)]
    rcs = [_as_i64(b, f"rates[{i}].cool") for i, (_, b) in enumerate(rates)]
    n = len(rhs)
    ra = (ctypes.c_int64 * n)(*rhs)
    ca = (ctypes.c_int64 * n)(*rcs)
    out_t = ctypes.c_int64()
    out_h = ctypes.c_uint8()
    _check(_get().rocq_thermo_run(t0, ra, ca, n, ctypes.byref(out_t), ctypes.byref(out_h)))
    return ThermoState(out_t.value, bool(out_h.value))


class MpcDecision(NamedTuple):
    cost: int
    action: int  # -1 decelerate, 0 coast, +1 accelerate


def mpc_decide(reference: int, pos: int, vel: int, horizon: int = 5) -> MpcDecision:
    """One receding-horizon MPC decision on the double integrator.

    Proved (Mpc.v): the reported cost is <= the rolled-out cost of EVERY
    action sequence of length ``horizon`` (mpc_le_all) and is achieved by
    one of them (mpc_realizable). The proved i64 domain —
    |pos|, |vel|, |reference| <= 2^20 and horizon <= 8 — is enforced here
    (squares would overflow outside it).
    """
    for name, v in (("reference", reference), ("pos", pos), ("vel", vel)):
        v = _as_i64(v, name)
        if not -MPC_STATE_MAX <= v <= MPC_STATE_MAX:
            raise DomainError(
                f"{name} = {v} exceeds MPC_STATE_MAX (+/-{MPC_STATE_MAX}); "
                f"see mpc_fits_i64 in theories/Mpc.v"
            )
    if not isinstance(horizon, int) or isinstance(horizon, bool) or horizon < 0:
        raise TypeError(f"horizon must be a non-negative int, got {horizon!r}")
    if horizon > MPC_HORIZON_MAX:
        raise DomainError(
            f"horizon {horizon} exceeds MPC_HORIZON_MAX ({MPC_HORIZON_MAX}); "
            f"the proved cost bound (theories/Mpc.v) covers depth <= 8"
        )
    out_c = ctypes.c_int64()
    out_a = ctypes.c_int8()
    _check(_get().rocq_mpc_decide(reference, pos, vel, horizon,
                                  ctypes.byref(out_c), ctypes.byref(out_a)))
    return MpcDecision(out_c.value, out_a.value)


class FusionReport(NamedTuple):
    fused: int
    plausible: list[bool]


def fuse(readings: Sequence[int], tol: int) -> FusionReport:
    """Median-fuse sensor readings and gate each for plausibility.

    Proved (SensorFusion.v, on top of the verified insertion sort):
    the fused value is one of the readings (median_in_inputs); a strict
    majority agreeing within a band captures the median (majority_band —
    fault masking); accepted readings are within ``tol`` of the fused value
    and pairwise within ``2*tol`` (scene consistency). The bindings enforce
    |reading|, tol <= 2^62 - 1 (gate_fits_i64).
    """
    vals = list(readings)
    if not vals:
        raise ValueError("fuse() requires at least one reading")
    arr, n = _as_i64_array(vals, "readings")
    tol = _as_i64(tol, "tol")
    if tol < 0:
        raise ValueError(f"tol must be >= 0, got {tol}")
    bound = SAFE_PRICE_BOUND  # 2^62 - 1, same constant as gate_fits_i64
    for i, v in enumerate(vals):
        if not -bound <= v <= bound:
            raise DomainError(
                f"readings[{i}] = {v} exceeds the sensor bound (+/-{bound}); "
                f"see gate_fits_i64 in theories/SensorFusion.v"
            )
    if tol > bound:
        raise DomainError(
            f"tol = {tol} exceeds the sensor bound ({bound}); "
            f"see gate_fits_i64 in theories/SensorFusion.v"
        )
    out_f = ctypes.c_int64()
    out_flags = (ctypes.c_uint8 * n)()
    _check(_get().rocq_fusion_fuse(tol, arr, n, ctypes.byref(out_f), out_flags))
    return FusionReport(out_f.value, [bool(b) for b in out_flags])


# --------------------------------------------------------------------------
# ADAS scene model with plausibility checking
# --------------------------------------------------------------------------

_SCENE_CLASSES = {"vehicle": 0, "pedestrian": 1, "bicycle": 2,
                  "sign": 3, "light": 4}
_TL_STATES = {"none": 0, "red": 1, "yellow": 2, "green": 3}

#: Rule mask bits (mirrors the catalog in theories/SceneModel.v).
SCENE_RULES = {
    1: "ENV_DIM", 2: "ENV_SPEED", 4: "ENV_FOV", 8: "ENV_CONF",
    16: "TGT_CLASS", 32: "OVERLAP",
    128: "OFFROAD_VEHICLE", 256: "OFFROAD_BIKE", 512: "PED_ON_FAST_ROAD",
    1024: "FURNITURE_IN_ROAD", 2048: "LIGHT_CONFLICT", 4096: "DUPLICATE",
    8192: "TGT_BEHIND", 16384: "TGT_OFFLANE", 32768: "TGT_EXTRA",
}

_VERDICTS = ["confirmed", "low_confidence", "implausible"]


#: Typical footprint per class (w, l in cm) used when dims are omitted.
_DEFAULT_DIMS = {"vehicle": (180, 450), "pedestrian": (60, 60),
                 "bicycle": (60, 180), "sign": (60, 60), "light": (40, 40)}


class SceneObject(NamedTuple):
    """One detected object. Units: cm, cm/s, confidence percent.

    ``cls``: vehicle | pedestrian | bicycle | sign | light.
    ``tl``: none | red | yellow | green (lights only).
    ``w``/``l`` of 0 select a typical footprint for the class.
    """
    cls: str
    x: int
    y: int
    vx: int = 0
    vy: int = 0
    w: int = 0
    l: int = 0
    conf: int = 90
    target: bool = False
    tl: str = "none"


class Road(NamedTuple):
    lanes: int = 3
    lane_w: int = 350          # cm
    curv: int = 0              # bounded units, validation-only in v1
    limit: int = 1400          # cm/s


class SceneEntry(NamedTuple):
    verdict: str
    score: int
    rules: list[str]


class SceneReport(NamedTuple):
    scene_ok: bool
    entries: list[SceneEntry]


def check_scene(road: Road, ego_v: int, objects: Sequence[SceneObject]) -> SceneReport:
    """Run the verified scene-consistency checker.

    TOTAL for any i64 inputs: unary rules are comparisons only, and all
    pairwise arithmetic is gated behind the envelope checks
    (validate-then-compute — validated_bounds / pair_arith_fits in
    theories/SceneModel.v). There is no input domain to enforce here.

    Guarantees (all axiom-free theorems):
      - one entry per object, in order (check_length);
      - envelope violations are always 'implausible' (hard_env_implausible);
      - a clean object keeps its sensor confidence — every downgrade cites
        at least one rule in ``rules`` (clean_confirmed);
      - 0 <= score <= 100 and score <= sensor confidence (score_bounds,
        score_le_conf);
      - duplicate/overlap pairs never lose BOTH members
        (dup_at_most_one, overlap_at_most_one).
    """
    n = len(objects)
    cls, xs, ys, vxs, vys, ws, ls, cfs, tgs, tls = ([] for _ in range(10))
    for i, o in enumerate(objects):
        if o.cls not in _SCENE_CLASSES:
            raise ValueError(f"objects[{i}]: unknown class {o.cls!r}")
        if o.tl not in _TL_STATES:
            raise ValueError(f"objects[{i}]: unknown light state {o.tl!r}")
        cls.append(_SCENE_CLASSES[o.cls])
        xs.append(_as_i64(o.x, f"objects[{i}].x"))
        ys.append(_as_i64(o.y, f"objects[{i}].y"))
        vxs.append(_as_i64(o.vx, f"objects[{i}].vx"))
        vys.append(_as_i64(o.vy, f"objects[{i}].vy"))
        dw, dl = _DEFAULT_DIMS[o.cls]
        ws.append(_as_i64(o.w if o.w else dw, f"objects[{i}].w"))
        ls.append(_as_i64(o.l if o.l else dl, f"objects[{i}].l"))
        cfs.append(_as_i64(o.conf, f"objects[{i}].conf"))
        tgs.append(1 if o.target else 0)
        tls.append(_TL_STATES[o.tl])
    a64 = lambda v: (ctypes.c_int64 * n)(*v)
    a8 = lambda v: (ctypes.c_uint8 * n)(*v)
    out_ok = ctypes.c_uint8()
    out_v = (ctypes.c_uint8 * n)()
    out_s = (ctypes.c_int64 * n)()
    out_m = (ctypes.c_int64 * n)()
    _check(_get().rocq_scene_check(
        _as_i64(road.lanes, "road.lanes"), _as_i64(road.lane_w, "road.lane_w"),
        _as_i64(road.curv, "road.curv"), _as_i64(road.limit, "road.limit"),
        _as_i64(ego_v, "ego_v"),
        a8(cls), a64(xs), a64(ys), a64(vxs), a64(vys), a64(ws), a64(ls),
        a64(cfs), a8(tgs), a64(tls), n,
        ctypes.byref(out_ok), out_v, out_s, out_m,
    ))
    entries = [
        SceneEntry(_VERDICTS[out_v[i]], out_s[i],
                   [name for b, name in SCENE_RULES.items() if out_m[i] & b])
        for i in range(n)
    ]
    return SceneReport(bool(out_ok.value), entries)


#: World-frame ingest domain (SceneWorld.v: SAFE_COORD, ingest_fits_i64):
#: every world coordinate, velocity and ego-pose field must satisfy
#: |v| <= 2^62 - 1 so the ingest subtractions and rotation negations fit
#: i64 (with a one-off margin below |i64::MIN|, whose negation is undefined).
SAFE_COORD = 2**62 - 1


class WorldPose(NamedTuple):
    """Ego pose in the world frame. ``heading``: quarter-turns CCW from
    world +x to ego forward (0..3). ``vx``/``vy``: ego world velocity."""
    x: int
    y: int
    heading: int = 0
    vx: int = 0
    vy: int = 0


def check_scene_world(
    road: Road,
    pose: WorldPose,
    objects: Sequence[SceneObject],
    *,
    enforce_domain: bool = True,
) -> SceneReport:
    """World-frame variant of :func:`check_scene`.

    Objects are in WORLD coordinates; the verified code ingests them
    (translate by the ego pose, rotate by the quarter-turn heading) and
    then runs the same checker, whose guarantees all lift
    (world_check_length, world_scores_bounded; the transform is lossless —
    egress_ingest_id).

    UNLIKE :func:`check_scene`, this interface HAS a caller domain: the
    ingest subtraction/negation happens on raw inputs, before any envelope
    can run. ``enforce_domain`` rejects fields outside
    ±``SAFE_COORD`` (= 2^62 - 1, proved sufficient by ``ingest_fits_i64``
    in theories/SceneWorld.v) with :class:`DomainError`. Bypassing it makes
    the checked build panic — surfaced as :class:`RocqError`, never a
    silently corrupted scene.
    """
    if not isinstance(pose.heading, int) or not 0 <= pose.heading <= 3:
        raise ValueError(
            f"pose.heading must be 0..3 quarter-turns, got {pose.heading!r} "
            f"(egress_ingest_id covers exactly these)"
        )
    def _dom(v, what):
        v = _as_i64(v, what)
        if enforce_domain and not -SAFE_COORD <= v <= SAFE_COORD:
            raise DomainError(
                f"{what} = {v} exceeds SAFE_COORD (+/-{SAFE_COORD}); outside "
                f"ingest_fits_i64 (theories/SceneWorld.v) the ingest "
                f"subtraction/negation can leave i64"
            )
        return v
    n = len(objects)
    cls, xs, ys, vxs, vys, ws, ls, cfs, tgs, tls = ([] for _ in range(10))
    for i, o in enumerate(objects):
        if o.cls not in _SCENE_CLASSES:
            raise ValueError(f"objects[{i}]: unknown class {o.cls!r}")
        if o.tl not in _TL_STATES:
            raise ValueError(f"objects[{i}]: unknown light state {o.tl!r}")
        cls.append(_SCENE_CLASSES[o.cls])
        xs.append(_dom(o.x, f"objects[{i}].x"))
        ys.append(_dom(o.y, f"objects[{i}].y"))
        vxs.append(_dom(o.vx, f"objects[{i}].vx"))
        vys.append(_dom(o.vy, f"objects[{i}].vy"))
        dw, dl = _DEFAULT_DIMS[o.cls]
        ws.append(_as_i64(o.w if o.w else dw, f"objects[{i}].w"))
        ls.append(_as_i64(o.l if o.l else dl, f"objects[{i}].l"))
        cfs.append(_as_i64(o.conf, f"objects[{i}].conf"))
        tgs.append(1 if o.target else 0)
        tls.append(_TL_STATES[o.tl])
    a64 = lambda v: (ctypes.c_int64 * n)(*v)
    a8 = lambda v: (ctypes.c_uint8 * n)(*v)
    out_ok = ctypes.c_uint8()
    out_v = (ctypes.c_uint8 * n)()
    out_s = (ctypes.c_int64 * n)()
    out_m = (ctypes.c_int64 * n)()
    _check(_get().rocq_scene_world_check(
        _as_i64(road.lanes, "road.lanes"), _as_i64(road.lane_w, "road.lane_w"),
        _as_i64(road.curv, "road.curv"), _as_i64(road.limit, "road.limit"),
        _dom(pose.x, "pose.x"), _dom(pose.y, "pose.y"),
        pose.heading, _dom(pose.vx, "pose.vx"), _dom(pose.vy, "pose.vy"),
        a8(cls), a64(xs), a64(ys), a64(vxs), a64(vys), a64(ws), a64(ls),
        a64(cfs), a8(tgs), a64(tls), n,
        ctypes.byref(out_ok), out_v, out_s, out_m,
    ))
    entries = [
        SceneEntry(_VERDICTS[out_v[i]], out_s[i],
                   [name for b, name in SCENE_RULES.items() if out_m[i] & b])
        for i in range(n)
    ]
    return SceneReport(bool(out_ok.value), entries)


# --------------------------------------------------------------------------
# Fletcher-16 checksum (data-link integrity)
# --------------------------------------------------------------------------

def fletcher16(data: Sequence[int], *, enforce_domain: bool = True) -> int:
    """Fletcher-16 checksum (packed ``256*s2 + s1``) of mod-255 symbols.

    Protections:
      (a) symbols validated as true ints in i64 (TypeError/OverflowError);
      (b) proved PROPERTY domain: every symbol must be in [0, 254] —
          the hypothesis of ``single_error_detected`` (theories/Fletcher.v).
          This domain guards a THEOREM, not an integer width: Fletcher
          works mod 255, so 0 and 255 are congruent, and substituting one
          for the other is exactly the corruption the checksum cannot see
          (the classic Fletcher blind spot). ``enforce_domain=False``
          neither crashes nor overflows — it silently forfeits the
          detection guarantee (the demo exhibits the 0x00/0xFF collision);
      (d) checked native build: a huge bypassed symbol overflows loudly
          (RocqError), never silently.

    Guaranteed on the domain: any single corrupted symbol changes the
    checksum (``single_error_detected``); the sums stay in [0, 254]
    (``run_bounds``); checksums are streamable (``fletcher_append``).
    """
    vals = list(data)
    arr, n = _as_i64_array(vals, "data")
    if enforce_domain:
        for i, d in enumerate(vals):
            if not 0 <= d <= 254:
                raise DomainError(
                    f"data[{i}] = {d} outside [0, 254], the hypothesis of "
                    f"single_error_detected (theories/Fletcher.v). Symbols "
                    f"are mod-255: 0 and 255 are congruent, so the "
                    f"detection guarantee does not cover this input."
                )
    s1 = ctypes.c_int64()
    s2 = ctypes.c_int64()
    _check(_get().rocq_fletcher16(arr, n, ctypes.byref(s1), ctypes.byref(s2)))
    return 256 * s2.value + s1.value


# --------------------------------------------------------------------------
# RSS safe following distance (division-free)
# --------------------------------------------------------------------------

#: RSS parameter domain (rss_dom / rss_fits_i64 in theories/Rss.v).
RSS_D_MAX = 1_000_000     # gap, cm (10 km)
RSS_V_MAX = 7_000         # speeds, cm/s
RSS_RHO_MAX = 100         # response time, ticks
RSS_ACC_MAX = 1_500       # accelerations, cm/s^2


class RssResult(NamedTuple):
    safe: bool
    margin: int   # RSS inequality scaled by 2*b_min*b_max; >= 0 iff safe


def rss_check(gap: int, v_rear: int, v_front: int, *,
              rho: int = 10, a_max: int = 300,
              b_min: int = 400, b_max: int = 800) -> RssResult:
    """RSS-style longitudinal safe-distance check, division-free.

    ``safe`` iff even in the worst case — rear accelerates at ``a_max``
    for the response time ``rho`` then brakes at its weakest ``b_min``,
    while the front brakes at its strongest ``b_max`` — no collision
    occurs. ``margin`` is the inequality scaled by ``2*b_min*b_max``
    (a graded severity signal).

    Protections:
      (a) all parameters validated as true ints in i64;
      (b) proved domain (DomainError): gap in [0, 10 km], speeds in
          [0, 70 m/s], rho in [1, 100], accelerations in [1, 15 m/s^2] —
          ``rss_fits_i64`` proves every product the margin computes stays
          within +-2^47 on exactly this domain;
      (d) checked native build: bypassed overflow panics, contained.

    Guaranteed (theories/Rss.v): the verdict is monotone the way physics
    demands — more gap, a slower rear vehicle, or a faster front vehicle
    can never turn safe into unsafe (``rss_monotone_distance``,
    ``rss_antitone_rear_speed``, ``rss_monotone_front_speed``); a
    stationary non-accelerating rear vehicle is safe at any gap
    (``rss_standstill_safe``).
    """
    checks = [("gap", gap, 0, RSS_D_MAX), ("v_rear", v_rear, 0, RSS_V_MAX),
              ("v_front", v_front, 0, RSS_V_MAX), ("rho", rho, 1, RSS_RHO_MAX),
              ("a_max", a_max, 0, RSS_ACC_MAX), ("b_min", b_min, 1, RSS_ACC_MAX),
              ("b_max", b_max, 1, RSS_ACC_MAX)]
    for name, v, lo, hi in checks:
        v = _as_i64(v, name)
        if not lo <= v <= hi:
            raise DomainError(
                f"{name} = {v} outside [{lo}, {hi}] (rss_dom); rss_fits_i64 "
                f"in theories/Rss.v proves i64 safety on exactly that domain"
            )
    out_s = ctypes.c_uint8()
    out_m = ctypes.c_int64()
    _check(_get().rocq_rss_check(b_min, b_max, gap, v_rear, v_front, rho,
                                 a_max, ctypes.byref(out_s), ctypes.byref(out_m)))
    return RssResult(bool(out_s.value), out_m.value)
