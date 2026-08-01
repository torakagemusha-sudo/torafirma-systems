"""Fixed ZPA-LM divisor/Fisher token router."""

from __future__ import annotations

import torch
from torch import nn


def _validate_exponents(exponents: torch.Tensor) -> None:
    if exponents.ndim not in (2, 3):
        raise ValueError("exponents must have shape [N, P] or [B, T, P]")
    if not torch.is_floating_point(exponents):
        raise TypeError("exponents must use a floating-point dtype")
    if not torch.isfinite(exponents).all().item():
        raise ValueError("exponents must be finite")
    if torch.any(exponents < 0).item():
        raise ValueError("exponents must be non-negative")


def torch_pairwise_exponent_kernel(exponents: torch.Tensor) -> torch.Tensor:
    """Compute pairwise divisor-kernel values in stable log space.

    Accepted shapes are ``[N, P]`` and ``[B, T, P]``.  The result shapes are ``[N, N]``
    and ``[B, T, T]`` respectively.
    """

    _validate_exponents(exponents)
    if exponents.ndim == 2:
        left = exponents[:, None, :]
        right = exponents[None, :, :]
    else:
        left = exponents[:, :, None, :]
        right = exponents[:, None, :, :]

    log_q = torch.log(torch.minimum(left, right) + 1.0).sum(dim=-1)
    log_q = log_q - 0.5 * torch.log(left + 1.0).sum(dim=-1)
    log_q = log_q - 0.5 * torch.log(right + 1.0).sum(dim=-1)
    return torch.exp(log_q)


class DivisorKernelRouter(nn.Module):
    """Construct fixed causal token-mixing weights from a non-trainable codebook.

    This module has **zero trainable parameters**.  It replaces learned query/key score
    construction only.  A surrounding model may still train embeddings, value projections,
    feed-forward blocks, normalisation parameters, and output layers.
    """

    def __init__(self, exponent_codebook: torch.Tensor) -> None:
        super().__init__()
        codebook = torch.as_tensor(exponent_codebook)
        if codebook.ndim != 2:
            raise ValueError("exponent_codebook must have shape [vocab_size, num_primes]")
        if not torch.is_floating_point(codebook):
            codebook = codebook.to(dtype=torch.float32)
        _validate_exponents(codebook)
        self.register_buffer("exponent_codebook", codebook.detach().clone(), persistent=True)

    @property
    def vocab_size(self) -> int:
        return int(self.exponent_codebook.shape[0])

    @property
    def exponent_width(self) -> int:
        return int(self.exponent_codebook.shape[1])

    def lexical_profiles(self, token_ids: torch.Tensor) -> torch.Tensor:
        if token_ids.ndim != 2:
            raise ValueError("token_ids must have shape [B, T]")
        if token_ids.dtype not in (torch.int32, torch.int64):
            raise TypeError("token_ids must use an integer dtype")
        if token_ids.numel() and (
            torch.any(token_ids < 0).item() or torch.any(token_ids >= self.vocab_size).item()
        ):
            raise IndexError("token_ids contain an index outside the codebook")
        return self.exponent_codebook[token_ids]

    def raw_kernel(self, token_ids: torch.Tensor) -> torch.Tensor:
        """Return the unmasked symmetric lexical kernel ``Q(token_i, token_j)``."""

        return torch_pairwise_exponent_kernel(self.lexical_profiles(token_ids))

    def forward(self, token_ids: torch.Tensor) -> torch.Tensor:
        """Return lower-triangular, row-normalized causal mixing weights."""

        raw = self.raw_kernel(token_ids)
        sequence_length = raw.shape[-1]
        causal_mask = torch.ones(
            (sequence_length, sequence_length), dtype=torch.bool, device=raw.device
        ).tril()
        masked = raw.masked_fill(~causal_mask, 0.0)
        row_sums = masked.sum(dim=-1, keepdim=True)
        if torch.any(row_sums <= 0).item():
            raise RuntimeError("causal kernel produced an empty row")
        return masked / row_sums
