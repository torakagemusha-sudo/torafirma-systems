"""Executable conformance audit for the public reference mechanism."""

from __future__ import annotations

import argparse
import json
import platform
from dataclasses import asdict
from typing import Any

import numpy as np
import torch

from .codebook import ExponentCodebook
from .geometry import (
    bhattacharyya_divisor_overlap,
    divisor_kernel,
    exponent_kernel,
    factorization_to_exponents,
    prime_factorization,
)
from .model import TinyZPALM
from .router import DivisorKernelRouter


def toy_codebook() -> ExponentCodebook:
    return ExponentCodebook.from_mapping(
        {
            "<pad>": 1,
            "dog": 60,
            "wolf": 84,
            "cat": 330,
            "leash": 420,
            "car": 2873,
            "road": 4199,
            ".": 30,
        }
    )


def run_audit(limit: int = 96) -> dict[str, Any]:
    max_keystone_error = 0.0
    max_exponent_error = 0.0
    for n in range(1, limit + 1):
        for m in range(1, limit + 1):
            closed = divisor_kernel(n, m)
            direct = bhattacharyya_divisor_overlap(n, m)
            max_keystone_error = max(max_keystone_error, abs(closed - direct))

            primes = tuple(
                sorted(set(prime_factorization(n)).union(prime_factorization(m)))
            )
            left = factorization_to_exponents(prime_factorization(n), primes)
            right = factorization_to_exponents(prime_factorization(m), primes)
            max_exponent_error = max(max_exponent_error, abs(closed - exponent_kernel(left, right)))

    codebook = toy_codebook()
    exponent_tensor = codebook.to_torch(dtype=torch.float64)
    router = DivisorKernelRouter(exponent_tensor)
    token_ids = torch.tensor([[1, 2, 3, 1, 4, 7]], dtype=torch.long)
    raw = router.raw_kernel(token_ids)
    weights = router(token_ids)
    upper = torch.triu(weights, diagonal=1)
    eigenvalues = torch.linalg.eigvalsh(raw[0])

    torch.manual_seed(7)
    model = TinyZPALM(
        codebook.to_torch(), width=24, layers=1, max_sequence_length=16
    )
    logits, loss = model(token_ids, targets=token_ids)
    assert loss is not None
    loss.backward()
    audit = model.parameter_audit()
    gradient_parameters = [
        name
        for name, parameter in model.named_parameters()
        if parameter.requires_grad and parameter.grad is not None
    ]

    return {
        "schema": "zpa-lm-reference-audit/v1",
        "package_version": "0.1.0",
        "environment": {
            "python": platform.python_version(),
            "platform": platform.platform(),
            "numpy": np.__version__,
            "torch": torch.__version__,
        },
        "scope": {
            "integer_pair_limit_inclusive": limit,
            "integer_pair_count": limit * limit,
        },
        "keystone": {
            "max_abs_error_closed_form_vs_direct_bc": max_keystone_error,
            "max_abs_error_closed_form_vs_exponent_product": max_exponent_error,
        },
        "router": {
            "raw_symmetry_max_abs_error": float((raw - raw.transpose(-1, -2)).abs().max()),
            "raw_diagonal_max_abs_error": float(
                (raw.diagonal(dim1=-2, dim2=-1) - 1.0).abs().max()
            ),
            "raw_min_eigenvalue": float(eigenvalues.min()),
            "causal_upper_triangle_max_abs": float(upper.abs().max()),
            "causal_row_sum_max_abs_error": float(
                (weights.sum(dim=-1) - 1.0).abs().max()
            ),
            "trainable_parameter_count": sum(
                parameter.numel() for parameter in router.parameters() if parameter.requires_grad
            ),
        },
        "model": {
            **asdict(audit),
            "forward_finite": bool(torch.isfinite(logits).all().item()),
            "loss": float(loss.detach()),
            "gradient_parameter_count": len(gradient_parameters),
            "gradient_parameters": gradient_parameters,
        },
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--limit", type=int, default=96)
    parser.add_argument("--compact", action="store_true")
    args = parser.parse_args()
    if args.limit < 1:
        parser.error("--limit must be positive")
    result = run_audit(args.limit)
    print(json.dumps(result, indent=None if args.compact else 2, sort_keys=True))


if __name__ == "__main__":
    main()
