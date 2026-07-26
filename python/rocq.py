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
    "sort",
    "max_profit",
    "max_drawdown",
    "run_orders",
    "analyze",
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

    lib.rocq_analyze.argtypes = [
        i64p, ctypes.c_size_t, ctypes.c_int64, u8p, i64p, ctypes.c_size_t, i64p
    ]
    lib.rocq_analyze.restype = ctypes.c_int32

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
) -> Analytics:
    """All three analytics in a single native call."""
    arr, pn = _as_i64_array(prices, "prices")
    limit = _as_i64(limit, "limit")
    sides, qtys, on = _split_orders(orders)
    out = (ctypes.c_int64 * 3)()
    _check(_get().rocq_analyze(arr, pn, limit, sides, qtys, on, out))
    return Analytics(out[0], out[1], out[2])
