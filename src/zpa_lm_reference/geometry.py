"""Number-theoretic and information-geometric primitives for ZPA-LM."""

from __future__ import annotations

import math
from collections.abc import Mapping, Sequence

import numpy as np
import numpy.typing as npt

FloatArray = npt.NDArray[np.float64]


def _require_positive_integer(value: int, *, name: str) -> int:
    if isinstance(value, bool) or not isinstance(value, int) or value < 1:
        raise ValueError(f"{name} must be a positive integer; received {value!r}")
    return value


def prime_factorization(n: int) -> dict[int, int]:
    """Return the prime factorization of ``n`` as ``{prime: exponent}``.

    ``1`` has the empty factorization.  The implementation is deliberately elementary and
    transparent; the reference repository optimizes for inspectability, not large-integer
    factorization throughput.
    """

    remaining = _require_positive_integer(n, name="n")
    factors: dict[int, int] = {}

    exponent = 0
    while remaining % 2 == 0:
        remaining //= 2
        exponent += 1
    if exponent:
        factors[2] = exponent

    candidate = 3
    while candidate * candidate <= remaining:
        exponent = 0
        while remaining % candidate == 0:
            remaining //= candidate
            exponent += 1
        if exponent:
            factors[candidate] = exponent
        candidate += 2

    if remaining > 1:
        factors[remaining] = factors.get(remaining, 0) + 1
    return factors


def divisor_count(n: int) -> int:
    """Return the divisor-counting function ``d(n)`` (also written ``tau(n)``)."""

    result = 1
    for exponent in prime_factorization(n).values():
        result *= exponent + 1
    return result


def divisors(n: int) -> tuple[int, ...]:
    """Enumerate all positive divisors of ``n`` in ascending order."""

    _require_positive_integer(n, name="n")
    values = [1]
    for prime, exponent in prime_factorization(n).items():
        previous = tuple(values)
        power = 1
        for _ in range(exponent):
            power *= prime
            values.extend(value * power for value in previous)
    return tuple(sorted(values))


def divisor_kernel(n: int, m: int) -> float:
    r"""Compute the normalized divisor-overlap kernel.

    .. math::

       q(n,m) = \frac{d(\gcd(n,m))}{\sqrt{d(n)d(m)}}.
    """

    n = _require_positive_integer(n, name="n")
    m = _require_positive_integer(m, name="m")
    numerator = divisor_count(math.gcd(n, m))
    denominator = math.sqrt(divisor_count(n) * divisor_count(m))
    return numerator / denominator


def bhattacharyya_divisor_overlap(n: int, m: int) -> float:
    """Directly compute ``BC(U_n, U_m)`` from uniform divisor-set distributions.

    This intentionally uses explicit divisor sets.  It is slower than :func:`divisor_kernel`
    and exists as an independent conformance path for the keystone identity.
    """

    divisor_set_n = set(divisors(n))
    divisor_set_m = set(divisors(m))
    intersection_size = len(divisor_set_n.intersection(divisor_set_m))
    return intersection_size / math.sqrt(len(divisor_set_n) * len(divisor_set_m))


def _as_nonnegative_vector(
    values: Sequence[float] | npt.NDArray[np.generic], *, name: str
) -> FloatArray:
    array = np.asarray(values, dtype=np.float64)
    if array.ndim != 1:
        raise ValueError(f"{name} must be a one-dimensional exponent vector")
    if not np.all(np.isfinite(array)):
        raise ValueError(f"{name} must contain only finite values")
    if np.any(array < 0):
        raise ValueError(f"{name} must contain only non-negative exponents")
    return array


def exponent_kernel(
    u: Sequence[float] | npt.NDArray[np.generic],
    v: Sequence[float] | npt.NDArray[np.generic],
) -> float:
    r"""Compute the divisor kernel in prime-exponent coordinates.

    .. math::

       q(u,v) = \prod_p \frac{\min(u_p,v_p)+1}
       {\sqrt{(u_p+1)(v_p+1)}}.

    Integer exponent vectors recover the exact finite-divisor-set interpretation.  The same
    formula is also well-defined for finite non-negative real vectors.
    """

    left = _as_nonnegative_vector(u, name="u")
    right = _as_nonnegative_vector(v, name="v")
    if left.shape != right.shape:
        raise ValueError(f"u and v must have the same shape; got {left.shape} and {right.shape}")

    log_q = np.log(np.minimum(left, right) + 1.0).sum()
    log_q -= 0.5 * np.log(left + 1.0).sum()
    log_q -= 0.5 * np.log(right + 1.0).sum()
    return float(np.exp(log_q))


def pairwise_exponent_kernel(
    exponents: Sequence[Sequence[float]] | npt.NDArray[np.generic],
) -> FloatArray:
    """Return the symmetric Gram matrix for exponent profiles of shape ``[N, P]``."""

    matrix = np.asarray(exponents, dtype=np.float64)
    if matrix.ndim != 2:
        raise ValueError("exponents must have shape [N, P]")
    if not np.all(np.isfinite(matrix)) or np.any(matrix < 0):
        raise ValueError("exponents must be finite and non-negative")

    left = matrix[:, None, :]
    right = matrix[None, :, :]
    log_q = np.log(np.minimum(left, right) + 1.0).sum(axis=-1)
    log_q -= 0.5 * np.log(left + 1.0).sum(axis=-1)
    log_q -= 0.5 * np.log(right + 1.0).sum(axis=-1)
    return np.exp(log_q)


def fisher_rao_distance(overlap: float) -> float:
    r"""Return ``2 arccos(overlap)`` with roundoff-safe clamping to ``[0, 1]``."""

    if not math.isfinite(overlap):
        raise ValueError("overlap must be finite")
    if overlap < -1e-12 or overlap > 1.0 + 1e-12:
        raise ValueError(f"overlap must lie in [0, 1]; received {overlap}")
    return 2.0 * math.acos(min(1.0, max(0.0, overlap)))


def factorization_to_exponents(
    factors: Mapping[int, int], prime_basis: Sequence[int]
) -> FloatArray:
    """Project a prime-factor mapping onto an ordered prime basis."""

    return np.asarray([factors.get(prime, 0) for prime in prime_basis], dtype=np.float64)
