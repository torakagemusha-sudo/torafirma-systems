# ZPA-LM Reference

A small, paper-conformant implementation of the fixed divisor/Fisher token mixer described in:

> Thomas Helm, **“ZPA-LM: Parameter-Free Attention via the Divisor Kernel — Fisher–Rao Geometry, the Token-to-Prime Dictionary Problem, and a Diagnostic Catalogue of Permanent Failure Modes”** (ToraFirma Systems, July 2026).

This repository is intentionally narrower than the private research implementation. It exists so the central mechanism can be inspected, executed, tested, and falsified without exposing later experimental extensions.

## What “parameter-free attention” means here

It means that the **token-pair routing weights** are not produced by trainable query and key projections. For positive integer token codes `n` and `m`, the fixed overlap is

```text
q(n, m) = d(gcd(n, m)) / sqrt(d(n) d(m))
```

where `d(n)` is the divisor-counting function. If `U_n` and `U_m` are uniform probability distributions over the divisor sets of `n` and `m`, then

```text
q(n, m) = BC(U_n, U_m)
d_FR(n, m) = 2 arccos(q(n, m))
```

The first equality is algebraic. The mixer gathers these token-pair values, applies a causal mask, normalizes each row, and mixes a trainable value stream:

```text
K[b, i, j] = q(phi(token[b, i]), phi(token[b, j]))
A = row_normalize(causal_mask(K))
mixed[b, i] = sum_j A[b, i, j] W_v(x[b, j])
```

The surrounding decoder is **not** parameter-free. Embeddings, position embeddings, value projections, normalization, feed-forward blocks, and the tied output head remain trainable.

## Scope boundary

Included in v0.1.0:

- the closed-form GCD/divisor kernel;
- an independent direct Bhattacharyya calculation over explicit divisor sets;
- the equivalent prime-exponent product form;
- Fisher–Rao distance;
- deterministic token-codebook utilities;
- a zero-trainable-parameter causal router;
- a minimal decoder-only PyTorch model using one routing matrix across all layers;
- conformance tests, a machine-readable audit, and a tiny overfit demonstration.

Deliberately excluded:

- corpus-fitted, WordNet, and hybrid production dictionaries;
- deterministic exponent-state or stroboscopic context extensions;
- learned low-rank context modulation;
- private optimized kernels and experiment infrastructure;
- any claim that the fixed mixer outperforms learned attention or even the paper’s content-blind controls.

The codebook is load-bearing. The theorem identifies the geometry induced by a given token-to-integer map; it does not prove that an arbitrary map has useful linguistic semantics.

## Install and verify

```bash
python -m venv .venv
source .venv/bin/activate          # Windows: .venv\Scripts\activate
python -m pip install --upgrade pip
python -m pip install -e ".[test]"
pytest -q
python -m zpa_lm_reference.audit --limit 128
```

Run the focused demonstrations:

```bash
python examples/reproduce_keystone.py --limit 128
python examples/inspect_causal_matrix.py
python examples/tiny_overfit.py --steps 120
```

The tiny overfit is not a language-model performance claim. It only demonstrates that the fixed router can sit inside a trainable decoder and that gradients reach the value and backbone parameters while the router itself remains parameter-free.

## Evidence classes

**Proved algebraically:** the divisor overlap equals the Bhattacharyya coefficient of uniform divisor-set distributions; the prime-exponent product is the same quantity.

**Checked by this repository:** implementation equivalence, symmetry, unit diagonal, numerical positive semidefiniteness on fixtures, causal masking, row normalization, deterministic repeated CPU forwards, zero router parameters, and trainable-backbone gradient flow.

**Still open:** practical language-model value at matched non-mixer parameter count. The paper pre-registers the expected ordering as an empirical hypothesis, not a result.

See [CLAIMS_AND_LIMITS.md](CLAIMS_AND_LIMITS.md), [CONFORMANCE.md](CONFORMANCE.md), [FAILURE_REGISTRY.md](FAILURE_REGISTRY.md), and [EVIDENCE.md](EVIDENCE.md).

## Repository layout

```text
src/zpa_lm_reference/geometry.py   exact and exponent-space kernels
src/zpa_lm_reference/codebook.py   deterministic codebook conversion
src/zpa_lm_reference/router.py     fixed causal routing weights
src/zpa_lm_reference/model.py      minimal decoder demonstration
src/zpa_lm_reference/audit.py      machine-readable conformance audit
examples/                          executable demonstrations
tests/                             independent invariants and regressions
evidence/                          local validation record for this release
```

## Citation

Use [CITATION.cff](CITATION.cff). The paper is the authoritative mathematical description; this repository is the reference implementation of its static `fisher_dict` mechanism.

## Intellectual-property notice

Copyright © 2026 Thomas Helm / ToraFirma Systems. Patent pending. This initial reference release does not include an open-source licence. See [NOTICE.md](NOTICE.md) before redistribution or commercial use.
