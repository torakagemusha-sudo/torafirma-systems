"""A deliberately small decoder-only model using the fixed ZPA-LM router."""

from __future__ import annotations

from dataclasses import dataclass

import torch
import torch.nn.functional as functional
from torch import nn

from .router import DivisorKernelRouter


class RMSNorm(nn.Module):
    def __init__(self, width: int, epsilon: float = 1e-6) -> None:
        super().__init__()
        self.weight = nn.Parameter(torch.ones(width))
        self.epsilon = epsilon

    def forward(self, hidden: torch.Tensor) -> torch.Tensor:
        scale = torch.rsqrt(hidden.pow(2).mean(dim=-1, keepdim=True) + self.epsilon)
        return hidden * scale * self.weight


class SwiGLU(nn.Module):
    def __init__(self, width: int, hidden_width: int) -> None:
        super().__init__()
        self.up = nn.Linear(width, 2 * hidden_width, bias=False)
        self.down = nn.Linear(hidden_width, width, bias=False)

    def forward(self, hidden: torch.Tensor) -> torch.Tensor:
        gate, value = self.up(hidden).chunk(2, dim=-1)
        return self.down(functional.silu(gate) * value)


class FisherMixBlock(nn.Module):
    """Pre-normalized residual block with fixed routing and a trainable value path."""

    def __init__(self, width: int, feedforward_multiplier: int = 4) -> None:
        super().__init__()
        self.mix_norm = RMSNorm(width)
        self.value_projection = nn.Linear(width, width, bias=False)
        self.ff_norm = RMSNorm(width)
        self.feedforward = SwiGLU(width, feedforward_multiplier * width)

    def forward(self, hidden: torch.Tensor, routing_weights: torch.Tensor) -> torch.Tensor:
        values = self.value_projection(self.mix_norm(hidden))
        hidden = hidden + torch.matmul(routing_weights.to(values.dtype), values)
        hidden = hidden + self.feedforward(self.ff_norm(hidden))
        return hidden


@dataclass(frozen=True, slots=True)
class ParameterAudit:
    router_trainable: int
    model_trainable: int
    query_key_trainable: int


class TinyZPALM(nn.Module):
    """Minimal decoder backbone demonstrating the paper's ``fisher_dict`` mixer.

    The divisor/Fisher routing matrix is computed once per forward pass and reused across
    all blocks.  Token embeddings, positional embeddings, value projections, normalization,
    feed-forward layers, and the tied output head remain trainable.
    """

    def __init__(
        self,
        exponent_codebook: torch.Tensor,
        *,
        width: int = 64,
        layers: int = 2,
        max_sequence_length: int = 256,
        feedforward_multiplier: int = 4,
    ) -> None:
        super().__init__()
        if width < 1 or layers < 1 or max_sequence_length < 2:
            raise ValueError("width/layers must be positive and max_sequence_length at least 2")
        self.router = DivisorKernelRouter(exponent_codebook)
        self.max_sequence_length = max_sequence_length
        self.token_embedding = nn.Embedding(self.router.vocab_size, width)
        self.position_embedding = nn.Embedding(max_sequence_length, width)
        self.blocks = nn.ModuleList(
            [FisherMixBlock(width, feedforward_multiplier) for _ in range(layers)]
        )
        self.final_norm = RMSNorm(width)

    def forward(
        self,
        input_ids: torch.Tensor,
        *,
        targets: torch.Tensor | None = None,
        return_routing_weights: bool = False,
    ) -> tuple[torch.Tensor, torch.Tensor | None] | tuple[
        torch.Tensor, torch.Tensor | None, torch.Tensor
    ]:
        if input_ids.ndim != 2:
            raise ValueError("input_ids must have shape [B, T]")
        batch_size, sequence_length = input_ids.shape
        if sequence_length > self.max_sequence_length:
            raise ValueError(
                f"sequence length {sequence_length} exceeds {self.max_sequence_length}"
            )
        positions = torch.arange(sequence_length, device=input_ids.device)
        hidden = self.token_embedding(input_ids) + self.position_embedding(positions)[None, :, :]
        routing_weights = self.router(input_ids)
        for block in self.blocks:
            hidden = block(hidden, routing_weights)
        hidden = self.final_norm(hidden)
        logits = functional.linear(hidden, self.token_embedding.weight)

        loss: torch.Tensor | None = None
        if targets is not None:
            if targets.shape != input_ids.shape:
                raise ValueError("targets must have the same shape as input_ids")
            if sequence_length < 2:
                raise ValueError("next-token loss requires sequence length at least 2")
            loss = functional.cross_entropy(
                logits[:, :-1, :].reshape(batch_size * (sequence_length - 1), -1),
                targets[:, 1:].reshape(-1),
            )

        if return_routing_weights:
            return logits, loss, routing_weights
        return logits, loss

    def parameter_audit(self) -> ParameterAudit:
        router_trainable = sum(
            parameter.numel() for parameter in self.router.parameters() if parameter.requires_grad
        )
        model_trainable = sum(
            parameter.numel() for parameter in self.parameters() if parameter.requires_grad
        )
        query_key_trainable = sum(
            parameter.numel()
            for name, parameter in self.named_parameters()
            if parameter.requires_grad and ("query" in name.lower() or "key" in name.lower())
        )
        return ParameterAudit(
            router_trainable=router_trainable,
            model_trainable=model_trainable,
            query_key_trainable=query_key_trainable,
        )
