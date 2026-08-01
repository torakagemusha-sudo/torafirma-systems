"""ZPA-LM paper-conformant reference implementation.

The package implements the fixed divisor/Fisher token-routing mechanism described in
"ZPA-LM: Parameter-Free Attention via the Divisor Kernel".  "Parameter-free" refers to
construction of the token-mixing weights; the surrounding language model remains trainable.
"""

from .codebook import ExponentCodebook, integer_codebook_to_exponents
from .geometry import (
    bhattacharyya_divisor_overlap,
    divisor_count,
    divisor_kernel,
    divisors,
    exponent_kernel,
    fisher_rao_distance,
    pairwise_exponent_kernel,
    prime_factorization,
)
from .model import TinyZPALM
from .router import DivisorKernelRouter, torch_pairwise_exponent_kernel

__all__ = [
    "ExponentCodebook",
    "integer_codebook_to_exponents",
    "bhattacharyya_divisor_overlap",
    "divisor_count",
    "divisor_kernel",
    "divisors",
    "exponent_kernel",
    "fisher_rao_distance",
    "pairwise_exponent_kernel",
    "prime_factorization",
    "TinyZPALM",
    "DivisorKernelRouter",
    "torch_pairwise_exponent_kernel",
]

__version__ = "0.1.0"
