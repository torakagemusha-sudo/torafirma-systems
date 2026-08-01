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


def test_codebook_json_rejects_duplicate_tokens(tmp_path) -> None:
    path = tmp_path / "duplicate.json"
    path.write_text(
        json.dumps(
            {
                "tokens": [
                    {"token": "dog", "integer": 12},
                    {"token": "dog", "integer": 18},
                ]
            }
        ),
        encoding="utf-8",
    )
    with np.testing.assert_raises_regex(ValueError, "duplicate token"):
        ExponentCodebook.from_json(path)


def test_codebook_json_rejects_implicit_integer_coercion(tmp_path) -> None:
    invalid_values = [True, 3.5, "12", 0, -1]
    for index, integer in enumerate(invalid_values):
        path = tmp_path / f"invalid-{index}.json"
        path.write_text(
            json.dumps({"tokens": [{"token": "dog", "integer": integer}]}),
            encoding="utf-8",
        )
        with np.testing.assert_raises_regex(ValueError, "positive JSON integer"):
            ExponentCodebook.from_json(path)


def test_codebook_json_requires_nonempty_string_tokens(tmp_path) -> None:
    invalid_tokens = ["", 12, None]
    for index, token in enumerate(invalid_tokens):
        path = tmp_path / f"invalid-token-{index}.json"
        path.write_text(
            json.dumps({"tokens": [{"token": token, "integer": 12}]}),
            encoding="utf-8",
        )
        with np.testing.assert_raises_regex(ValueError, "non-empty string"):
            ExponentCodebook.from_json(path)
