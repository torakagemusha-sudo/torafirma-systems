from __future__ import annotations

import math

import numpy as np
import pytest

from zpa_lm_reference.geometry import (
    bhattacharyya_divisor_overlap,
    divisor_count,
    divisor_kernel,
    divisors,
    exponent_kernel,
    factorization_to_exponents,
    fisher_rao_distance,
    pairwise_exponent_kernel,
    prime_factorization,
)


def test_known_factorizations_and_divisor_counts() -> None:
    assert prime_factorization(1) == {}
    assert prime_factorization(360) == {2: 3, 3: 2, 5: 1}
    assert divisor_count(1) == 1
    assert divisor_count(360) == 24
    assert divisors(12) == (1, 2, 3, 4, 6, 12)


def test_keystone_identity_exhaustive_small_range() -> None:
    for n in range(1, 129):
        for m in range(1, 129):
            assert divisor_kernel(n, m) == pytest.approx(
                bhattacharyya_divisor_overlap(n, m), abs=1e-15
            )


def test_prime_exponent_product_matches_gcd_form() -> None:
    for n in range(1, 257):
        for m in range(1, 65):
            primes = tuple(
                sorted(set(prime_factorization(n)).union(prime_factorization(m)))
            )
            left = factorization_to_exponents(prime_factorization(n), primes)
            right = factorization_to_exponents(prime_factorization(m), primes)
            assert exponent_kernel(left, right) == pytest.approx(
                divisor_kernel(n, m), abs=2e-15
            )


def test_kernel_invariants_and_fisher_distance() -> None:
    for n in range(1, 100):
        assert divisor_kernel(n, n) == pytest.approx(1.0)
        assert fisher_rao_distance(divisor_kernel(n, n)) == pytest.approx(0.0)
    for n, m in [(12, 18), (60, 84), (77, 143), (1, 360)]:
        q = divisor_kernel(n, m)
        assert 0.0 < q <= 1.0
        assert q == pytest.approx(divisor_kernel(m, n))
        assert 0.0 <= fisher_rao_distance(q) <= math.pi


def test_pairwise_kernel_is_symmetric_unit_diagonal_and_psd() -> None:
    exponents = np.asarray(
        [[0, 0, 0], [1, 0, 2], [2, 1, 0], [3, 2, 1], [0.5, 1.5, 0.25]],
        dtype=np.float64,
    )
    gram = pairwise_exponent_kernel(exponents)
    assert np.max(np.abs(gram - gram.T)) < 1e-14
    assert np.max(np.abs(np.diag(gram) - 1.0)) < 1e-14
    assert np.linalg.eigvalsh(gram).min() >= -1e-12


def test_input_validation() -> None:
    with pytest.raises(ValueError):
        divisor_kernel(0, 1)
    with pytest.raises(ValueError):
        exponent_kernel([1, -1], [1, 2])
    with pytest.raises(ValueError):
        exponent_kernel([1], [1, 2])
    with pytest.raises(ValueError):
        fisher_rao_distance(1.1)
