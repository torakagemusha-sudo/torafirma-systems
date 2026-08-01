from __future__ import annotations

import json

import numpy as np

from zpa_lm_reference.codebook import ExponentCodebook, integer_codebook_to_exponents


def test_integer_codebook_uses_shared_prime_basis() -> None:
    primes, exponents = integer_codebook_to_exponents([1, 12, 18, 25])
    assert primes == (2, 3, 5)
    np.testing.assert_array_equal(
        exponents,
        np.asarray([[0, 0, 0], [2, 1, 0], [1, 2, 0], [0, 0, 2]], dtype=float),
    )


def test_codebook_json_roundtrip(tmp_path) -> None:
    codebook = ExponentCodebook.from_mapping({"one": 1, "twelve": 12, "eighteen": 18})
    path = tmp_path / "codebook.json"
    path.write_text(json.dumps(codebook.as_json_dict()), encoding="utf-8")
    loaded = ExponentCodebook.from_json(path)
    assert loaded.tokens == codebook.tokens
    assert loaded.integers == codebook.integers
    assert loaded.primes == codebook.primes
    np.testing.assert_array_equal(loaded.exponents, codebook.exponents)
