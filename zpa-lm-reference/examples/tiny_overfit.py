#!/usr/bin/env python3
"""Small executable check that gradients flow around the fixed router."""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import torch

from zpa_lm_reference.codebook import ExponentCodebook
from zpa_lm_reference.model import TinyZPALM


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--steps", type=int, default=120)
    parser.add_argument("--learning-rate", type=float, default=0.02)
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--max-final-loss", type=float, default=None)
    args = parser.parse_args()
    if args.steps < 1:
        parser.error("--steps must be positive")

    torch.manual_seed(13)
    torch.set_num_threads(1)
    codebook = ExponentCodebook.from_json(Path(__file__).with_name("toy_codebook.json"))
    ids = codebook.token_to_id()
    sequences = torch.tensor(
        [
            [ids["dog"], ids["wolf"], ids["dog"], ids["leash"], ids["dog"], ids["."]],
            [ids["cat"], ids["dog"], ids["cat"], ids["leash"], ids["cat"], ids["."]],
            [ids["car"], ids["road"], ids["car"], ids["road"], ids["car"], ids["."]],
        ],
        dtype=torch.long,
    )
    model = TinyZPALM(
        codebook.to_torch(), width=32, layers=2, max_sequence_length=sequences.shape[1]
    )
    optimizer = torch.optim.AdamW(model.parameters(), lr=args.learning_rate, weight_decay=0.0)

    with torch.no_grad():
        _, initial_loss_tensor = model(sequences, targets=sequences)
        assert initial_loss_tensor is not None
        initial_loss = float(initial_loss_tensor)

    for _ in range(args.steps):
        optimizer.zero_grad(set_to_none=True)
        _, loss = model(sequences, targets=sequences)
        assert loss is not None
        loss.backward()
        optimizer.step()

    with torch.no_grad():
        logits, final_loss_tensor = model(sequences, targets=sequences)
        assert final_loss_tensor is not None
        final_loss = float(final_loss_tensor)
        predictions = logits[:, :-1].argmax(dim=-1)
        accuracy = float((predictions == sequences[:, 1:]).float().mean())

    result = {
        "schema": "zpa-lm-reference-tiny-overfit/v1",
        "steps": args.steps,
        "initial_loss": initial_loss,
        "final_loss": final_loss,
        "next_token_accuracy": accuracy,
        "router_trainable_parameters": model.parameter_audit().router_trainable,
    }
    if args.json:
        print(json.dumps(result, indent=2, sort_keys=True))
    else:
        for key, value in result.items():
            print(f"{key}: {value}")

    if args.max_final_loss is not None and final_loss > args.max_final_loss:
        raise SystemExit(
            f"final loss {final_loss:.6f} exceeded threshold {args.max_final_loss:.6f}"
        )


if __name__ == "__main__":
    main()
