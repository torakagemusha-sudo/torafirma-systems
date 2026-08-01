"""Deterministic token-to-integer and token-to-exponent codebook helpers."""

from __future__ import annotations

import json
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Mapping, Sequence

import numpy as np
import numpy.typing as npt
import torch

from .geometry import factorization_to_exponents, prime_factorization


@dataclass(frozen=True, slots=True)
class ExponentCodebook:
    """A finite token dictionary represented on a shared prime basis.

    The codebook is data, not a trainable model parameter.  Semantic quality of a particular
    token-to-integer assignment is outside the keystone theorem and must be evaluated
    separately.
    """

    tokens: tuple[str, ...]
    integers: tuple[int, ...]
    primes: tuple[int, ...]
    exponents: npt.NDArray[np.float64]

    def __post_init__(self) -> None:
        if len(self.tokens) != len(self.integers):
            raise ValueError("tokens and integers must have the same length")
        if len(set(self.tokens)) != len(self.tokens):
            raise ValueError("token names must be unique")
        if any(isinstance(value, bool) or not isinstance(value, int) or value < 1 for value in self.integers):
            raise ValueError("all integer codes must be positive integers")
        if self.exponents.shape != (len(self.tokens), len(self.primes)):
            raise ValueError(
                "exponents must have shape [len(tokens), len(primes)]; "
                f"received {self.exponents.shape}"
            )
        if not np.all(np.isfinite(self.exponents)) or np.any(self.exponents < 0):
            raise ValueError("exponents must be finite and non-negative")

    @classmethod
    def from_mapping(cls, mapping: Mapping[str, int]) -> "ExponentCodebook":
        if not mapping:
            raise ValueError("mapping must not be empty")
        tokens = tuple(mapping.keys())
        integers = tuple(mapping.values())
        primes, exponents = integer_codebook_to_exponents(integers)
        return cls(tokens=tokens, integers=integers, primes=primes, exponents=exponents)

    @classmethod
    def from_json(cls, path: str | Path) -> "ExponentCodebook":
        payload: Any = json.loads(Path(path).read_text(encoding="utf-8"))
        if not isinstance(payload, dict) or not isinstance(payload.get("tokens"), list):
            raise ValueError("codebook JSON must contain a 'tokens' list")
        mapping: dict[str, int] = {}
        for entry in payload["tokens"]:
            if not isinstance(entry, dict) or "token" not in entry or "integer" not in entry:
                raise ValueError("each token entry must contain 'token' and 'integer'")
            mapping[str(entry["token"])] = int(entry["integer"])
        return cls.from_mapping(mapping)

    def to_torch(
        self,
        *,
        dtype: torch.dtype = torch.float32,
        device: torch.device | str | None = None,
    ) -> torch.Tensor:
        return torch.as_tensor(self.exponents, dtype=dtype, device=device)

    def token_to_id(self) -> dict[str, int]:
        return {token: index for index, token in enumerate(self.tokens)}

    def as_json_dict(self) -> dict[str, object]:
        return {
            "tokens": [
                {"token": token, "integer": integer}
                for token, integer in zip(self.tokens, self.integers, strict=True)
            ]
        }


def integer_codebook_to_exponents(
    integer_codes: Sequence[int],
) -> tuple[tuple[int, ...], npt.NDArray[np.float64]]:
    """Factor integer codes and return a shared prime basis and exponent matrix."""

    if not integer_codes:
        raise ValueError("integer_codes must not be empty")
    factorizations = [prime_factorization(value) for value in integer_codes]
    primes = tuple(sorted({prime for factors in factorizations for prime in factors}))
    exponents = np.stack(
        [factorization_to_exponents(factors, primes) for factors in factorizations], axis=0
    )
    return primes, exponents
