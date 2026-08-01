from __future__ import annotations

import torch

from zpa_lm_reference.codebook import ExponentCodebook
from zpa_lm_reference.model import TinyZPALM


def _model() -> TinyZPALM:
    codebook = ExponentCodebook.from_mapping(
        {"<pad>": 1, "a": 6, "b": 10, "c": 15, "d": 30, ".": 42}
    )
    torch.manual_seed(5)
    return TinyZPALM(codebook.to_torch(), width=16, layers=2, max_sequence_length=16)


def test_parameter_audit_is_explicit() -> None:
    model = _model()
    audit = model.parameter_audit()
    assert audit.router_trainable == 0
    assert audit.query_key_trainable == 0
    assert audit.model_trainable > 0


def test_forward_backward_reaches_trainable_backbone() -> None:
    model = _model()
    tokens = torch.tensor([[1, 2, 3, 1, 4, 5], [2, 3, 4, 2, 1, 5]], dtype=torch.long)
    logits, loss, weights = model(tokens, targets=tokens, return_routing_weights=True)
    assert logits.shape == (2, 6, 6)
    assert weights.shape == (2, 6, 6)
    assert loss is not None and torch.isfinite(loss)
    loss.backward()
    assert model.token_embedding.weight.grad is not None
    assert model.blocks[0].value_projection.weight.grad is not None
    assert model.blocks[0].feedforward.up.weight.grad is not None
    assert model.router.exponent_codebook.grad is None


def test_cpu_eval_is_deterministic() -> None:
    model = _model().eval()
    tokens = torch.tensor([[1, 2, 3, 1, 4, 5]], dtype=torch.long)
    with torch.no_grad():
        first_logits, first_loss, first_weights = model(
            tokens, targets=tokens, return_routing_weights=True
        )
        second_logits, second_loss, second_weights = model(
            tokens, targets=tokens, return_routing_weights=True
        )
    torch.testing.assert_close(first_logits, second_logits, rtol=0, atol=0)
    torch.testing.assert_close(first_weights, second_weights, rtol=0, atol=0)
    assert first_loss is not None and second_loss is not None
    torch.testing.assert_close(first_loss, second_loss, rtol=0, atol=0)
