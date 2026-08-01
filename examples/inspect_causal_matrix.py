#!/usr/bin/env python3
"""Print one paper-conformant causal divisor/Fisher routing matrix."""

from __future__ import annotations

from pathlib import Path

import torch

from zpa_lm_reference.codebook import ExponentCodebook
from zpa_lm_reference.router import DivisorKernelRouter


def main() -> None:
    codebook_path = Path(__file__).with_name("toy_codebook.json")
    codebook = ExponentCodebook.from_json(codebook_path)
    token_to_id = codebook.token_to_id()
    tokens = ["dog", "wolf", "cat", "dog", "leash", "."]
    token_ids = torch.tensor([[token_to_id[token] for token in tokens]], dtype=torch.long)
    router = DivisorKernelRouter(codebook.to_torch(dtype=torch.float64))

    raw = router.raw_kernel(token_ids)[0]
    causal = router(token_ids)[0]
    torch.set_printoptions(precision=4, linewidth=120, sci_mode=False)
    print("tokens:", tokens)
    print("\nunmasked symmetric kernel:\n", raw)
    print("\ncausal row-normalized weights:\n", causal)
    print("\nrow sums:\n", causal.sum(dim=-1))


if __name__ == "__main__":
    main()
