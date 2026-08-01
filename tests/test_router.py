from __future__ import annotations

import torch

from zpa_lm_reference.codebook import ExponentCodebook
from zpa_lm_reference.router import DivisorKernelRouter, torch_pairwise_exponent_kernel


def _router() -> DivisorKernelRouter:
    codebook = ExponentCodebook.from_mapping(
        {"one": 1, "twelve": 12, "eighteen": 18, "sixty": 60, "eighty_four": 84}
    )
    return DivisorKernelRouter(codebook.to_torch(dtype=torch.float64))


def test_torch_kernel_geometry() -> None:
    profiles = torch.tensor(
        [[[0.0, 0.0], [1.0, 0.0], [2.0, 1.0], [0.5, 1.5]]], dtype=torch.float64
    )
    gram = torch_pairwise_exponent_kernel(profiles)
    assert torch.max(torch.abs(gram - gram.transpose(-1, -2))).item() < 1e-14
    assert torch.max(torch.abs(gram.diagonal(dim1=-2, dim2=-1) - 1.0)).item() < 1e-14
    assert torch.linalg.eigvalsh(gram[0]).min().item() >= -1e-12


def test_router_is_parameter_free_and_causal() -> None:
    router = _router()
    assert sum(parameter.numel() for parameter in router.parameters()) == 0
    token_ids = torch.tensor([[1, 2, 3, 1, 4]], dtype=torch.long)
    raw = router.raw_kernel(token_ids)
    weights = router(token_ids)
    assert torch.max(torch.abs(raw - raw.transpose(-1, -2))).item() < 1e-14
    assert torch.max(torch.abs(torch.triu(weights, diagonal=1))).item() == 0.0
    assert torch.max(torch.abs(weights.sum(dim=-1) - 1.0)).item() < 1e-14


def test_future_token_mutation_cannot_change_earlier_rows() -> None:
    router = _router()
    first = torch.tensor([[1, 2, 3, 1, 4]], dtype=torch.long)
    second = first.clone()
    second[0, 4] = 0
    first_weights = router(first)
    second_weights = router(second)
    torch.testing.assert_close(first_weights[:, :4, :4], second_weights[:, :4, :4], rtol=0, atol=0)


def test_repeated_tokens_have_identical_raw_lexical_rows_before_position_selection() -> None:
    router = _router()
    token_ids = torch.tensor([[1, 2, 1]], dtype=torch.long)
    raw = router.raw_kernel(token_ids)[0]
    torch.testing.assert_close(raw[0], raw[2], rtol=0, atol=0)
