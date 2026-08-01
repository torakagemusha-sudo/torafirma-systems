# ZPA-LM Reference

A small, paper-conformant implementation of the fixed divisor/Fisher token mixer described in:

> Thomas Helm, **“ZPA-LM: Parameter-Free Attention via the Divisor Kernel — Fisher–Rao Geometry, the Token-to-Prime Dictionary Problem, and a Diagnostic Catalogue of Permanent Failure Modes”** (ToraFirma Systems, July 2026).

This public reference is intentionally narrower than the private research implementation. It exists so the disclosed mechanism can be inspected, executed, tested, and falsified without exposing later experimental extensions.

## Contents

1. [Purpose and scope](#purpose-and-scope)
2. [Mathematical mechanism](#mathematical-mechanism)
3. [Reference architecture](#reference-architecture)
4. [Claims and limits](#claims-and-limits)
5. [Install and verify](#install-and-verify)
6. [Paper-to-code conformance](#paper-to-code-conformance)
7. [Permanent failure registry](#permanent-failure-registry)
8. [Reproducibility and evidence](#reproducibility-and-evidence)
9. [Security and trust boundary](#security-and-trust-boundary)
10. [Repository layout](#repository-layout)
11. [Changelog](#changelog)
12. [Citation](#citation)
13. [Rights notice](#rights-notice)

## Purpose and scope

### What “parameter-free attention” means here

The **token-pair routing weights** are not produced by trainable query and key projections. For positive integer token codes `n` and `m`, the fixed overlap is

```text
q(n, m) = d(gcd(n, m)) / sqrt(d(n) d(m))
```

where `d(n)` is the divisor-counting function.

The surrounding decoder is **not** parameter-free. Token and position embeddings, value projections, normalization, feed-forward blocks, and the tied output head remain trainable.

### Included in v0.1.0

- the closed-form GCD/divisor kernel;
- an independent Bhattacharyya calculation over explicit divisor sets;
- the equivalent prime-exponent product form;
- Fisher–Rao distance;
- deterministic token-codebook utilities;
- a zero-trainable-parameter causal router;
- a minimal decoder-only PyTorch model using one routing matrix across all layers;
- conformance tests, a machine-readable audit, and a tiny overfit demonstration.

### Deliberately excluded

- corpus-fitted, WordNet, and hybrid production dictionaries;
- deterministic exponent-state or stroboscopic context extensions;
- learned low-rank context modulation;
- reservoir coupling, controller logic, and later operator extensions;
- private optimized kernels and experiment infrastructure;
- any claim that the fixed mixer outperforms learned attention or the paper’s content-blind controls.

The codebook is load-bearing. The theorem identifies the geometry induced by a given token-to-integer map; it does not prove that an arbitrary map has useful linguistic semantics.

## Mathematical mechanism

For positive integers `n,m`, let `D_n` be the divisor set of `n`, and let `U_n` be the uniform probability distribution on `D_n`. Then

```text
BC(U_n, U_m)
= |D_n ∩ D_m| / sqrt(|D_n| |D_m|)
= d(gcd(n,m)) / sqrt(d(n)d(m))
= q(n,m).
```

The set identity

```text
D_n ∩ D_m = D_gcd(n,m)
```

proves the equality. Under the square-root embedding of the probability simplex, the corresponding Fisher–Rao distance is

```text
d_FR(n, m) = 2 arccos(q(n, m)).
```

In prime-exponent coordinates, if `u_p` and `v_p` are the exponents of prime `p`, the same kernel is

```text
q(u, v) = product_p (
    (min(u_p, v_p) + 1) / sqrt((u_p + 1)(v_p + 1))
)
```

Integer exponent vectors recover the exact finite-divisor-set interpretation. The implementation also evaluates the product for finite non-negative real exponent vectors as a continuous Gram-kernel extension; it does not claim that those real vectors have literal finite divisor sets.

## Reference architecture

For token dictionary `phi : token -> Z+`, the public `fisher_dict` route is

```text
K[b, i, j] = q(phi(token[b, i]), phi(token[b, j]))
A = row_normalize(causal_mask(K))
mixed[b, i] = sum_j A[b, i, j] W_v(x[b, j])
```

`K` is content-aware but context-blind. Causal masking changes which earlier values are available, but it does not change the lexical affinity assigned to the same token pair in different sentences.

The routing matrix is computed once per forward pass and reused across the reference model’s blocks. The router stores the exponent codebook as a non-trainable buffer and contains no trainable query or key projection.

## Claims and limits

### Algebraic claim

The divisor overlap equals the Bhattacharyya coefficient of the uniform divisor-set distributions. The prime-exponent product computes the same quantity.

### Implementation claim

The repository computes the kernel through three independent or equivalent paths:

1. explicit divisor-set support overlap;
2. the GCD/divisor-count closed form;
3. the prime-exponent product form.

It constructs a causal row-normalized routing matrix and applies it to a trainable value stream. Automated tests check the declared invariants.

### Explicit non-claims

This release does not establish that:

- the entire language model has zero parameters;
- the toy codebook has useful linguistic semantics;
- the fixed mixer is context-sensitive;
- the mixer dominates learned attention;
- the mixer dominates position-only or other content-blind controls;
- the tiny-overfit example predicts generalization;
- a continuous real-exponent code has a literal finite divisor-set interpretation;
- private later extensions are reproduced here.

### Architectural ceiling

With one static token-to-code dictionary, the same token pair receives the same unmasked kernel value in every context. That is an explicit ceiling of this release, not an omitted implementation detail.

### Falsification posture

A defect in the theorem should be shown by a counterexample to the set/counting identity. A defect in the implementation should be shown by a failing conformance test or independent implementation mismatch. A language-model performance claim requires matched baselines, declared budgets, multiple seeds, and complete reporting; none is inferred from the smoke demonstrations.

## Install and verify

Run these commands from this directory:

```bash
python -m venv .venv
source .venv/bin/activate          # Windows: .venv\Scripts\activate
python -m pip install -e ".[test]"
python -m pip check
python -m compileall -q src tests examples
pytest -q
python -m zpa_lm_reference.audit --limit 128
```

Focused demonstrations:

```bash
python examples/reproduce_keystone.py --limit 128
python examples/inspect_causal_matrix.py
python examples/tiny_overfit.py --steps 120
```

The tiny overfit is not a language-model performance claim. It demonstrates only that the fixed router can sit inside a trainable decoder and that gradients reach the value and backbone parameters while the router remains parameter-free.

## Paper-to-code conformance

| Paper element | Public implementation | Primary verification |
|---|---|---|
| Divisor-counting function `d(n)` | `geometry.divisor_count` | `test_known_factorizations_and_divisor_counts` |
| Keystone identity | `geometry.divisor_kernel` and `geometry.bhattacharyya_divisor_overlap` | exhaustive small-range identity test |
| Prime-exponent equation | `geometry.exponent_kernel` | GCD/product equivalence test |
| Fisher–Rao distance | `geometry.fisher_rao_distance` | identity and range tests |
| Token-to-positive-integer interface | `codebook.ExponentCodebook` | JSON, uniqueness, type, and basis tests |
| Static `fisher_dict` gather | `router.DivisorKernelRouter.raw_kernel` | symmetry and repeated-token tests |
| Causal mask and row normalization | `router.DivisorKernelRouter.forward` | upper-triangle and row-sum tests |
| Value-stream mixing | `model.FisherMixBlock` | forward/backward gradient test |
| One matrix reused across layers | `model.TinyZPALM.forward` | model tests and direct inspection |
| No learned Q/K route | router has buffers only; audit checks parameter names | parameter-audit tests |
| Context-blindness ceiling | static lexical rows | repeated-token lexical-row regression |
| Open empirical claim remains open | claim boundary | no performance promotion in code or documentation |

### Independent keystone check

The direct Bhattacharyya path explicitly enumerates divisor sets and counts their intersection. It does not call `gcd`, `divisor_count`, or the closed-form kernel. The exhaustive test is therefore a genuine second implementation path rather than a wrapper around the same calculation.

### Numerical conventions

Normalized overlaps are represented in floating point. Tests use tight absolute tolerances. Fisher–Rao input is clamped only within a small roundoff margin. Exponent products are evaluated in log space to avoid unnecessary underflow.

## Permanent failure registry

These failures are retained so the small public implementation does not erase negative evidence recorded in the technical note.

### F2 — self-isolating identity positional indexing

A causal mask combined with the tested coprimality brake and identity-style positional indexing isolated positions to themselves, blocking straightforward memorization. Status: falsified as a design choice.

### F8 — symbolic copy tasks as a discriminating benchmark

The fixed kernel represents distributional similarity of divisor-set supports, not symbolic token identity. Under exchangeable keys, copy/induction tasks can collapse to a uniform pattern and therefore do not cleanly discriminate the intended mechanism. Status: falsified as an evaluation choice.

### MSE dictionary-fit collapse

Minimizing mean-squared error between fitted kernel values and target overlaps admits a degenerate direction in which exponents collapse toward zero and all similarities approach one. The paper therefore specifies rank-oriented objectives rather than raw MSE. Status: falsified as a training objective.

### Random dictionary initialization

The tested random initialization was dominated by the structured Hermite/Calogero–Moser equilibrium initialization on the reported convergence, terminal correlation, and variance criteria. Status: falsified as the default initialization.

The public toy dictionary is a transparent fixture for mechanism inspection, not a proposal for production dictionary training or linguistic evaluation.

## Reproducibility and evidence

### Evidence classes

- **Algebraically proved:** the divisor overlap/Bhattacharyya identity and its prime-exponent product form.
- **Locally executed:** the exact repository tree has passed the tests and demonstrations recorded under `evidence/`.
- **Hosted-CI confirmed:** only a visible successful run of [the repository workflow](../.github/workflows/zpa-lm-reference.yml) establishes this state for a specific commit.
- **Still open:** practical language-model value at matched non-mixer parameter count.

### Deterministic reference path

The algebraic and routing checks are deterministic. The tiny model contains no dropout. Repeated CPU forwards with fixed weights and inputs are tested bit-for-bit in the recorded local environment.

The training smoke sets a fixed PyTorch seed and one CPU thread. Its purpose is execution evidence, not a statistical result. Floating-point details can vary across PyTorch releases or hardware while preserving the qualitative pass condition.

### Independent reproduction

A clean-room check of the keystone theorem requires only:

1. enumerate divisors of `n` and `m`;
2. form uniform distributions on those supports;
3. compute their Bhattacharyya coefficient;
4. compare it with `d(gcd(n,m))/sqrt(d(n)d(m))`.

No model code is required to test the mathematical identity.

### Evidence files

- `evidence/audit.json` — machine-readable conformance audit;
- `evidence/keystone.txt` — direct closed-form/support-overlap comparison;
- `evidence/causal-matrix.txt` — inspected routing fixture;
- `evidence/pytest.txt` — current local test output;
- `evidence/tiny-overfit.json` — bounded training smoke result;
- `evidence/local-validation.json` — evidence classification and environment;
- `evidence/security-review.json` — focused source, workflow, scope, and secret review;
- `evidence/SOURCE_MANIFEST.sha256` — repository-root-relative source hashes.

Verify the source manifest from the repository root:

```bash
sha256sum -c zpa-lm-reference/evidence/SOURCE_MANIFEST.sha256
```

## Security and trust boundary

This reference is a local mathematical/PyTorch library. It exposes no network service, authentication boundary, shell execution path, dynamic code evaluation, pickle deserialization, or remote model-loading mechanism.

The focused security review for the reorganized tree checks:

- every tracked file in the public project scope;
- obvious credential and private-key signatures;
- unsafe execution/deserialization imports and calls;
- public/private scope contamination markers in executable code;
- workflow token permissions and event triggers;
- dependency consistency, compilation, tests, and the conformance audit.

Hardening applied in this maintenance change:

- GitHub Actions are pinned to immutable full commit SHAs;
- checkout credentials are not persisted;
- workflow permissions remain read-only;
- CI is path-scoped, time-bounded, and runs `pip check` plus compilation before tests;
- local credential and key patterns are excluded through the repository `.gitignore`;
- JSON codebooks reject duplicate tokens, booleans, non-integer codes, and silent numeric coercion.

Remaining operational limits:

- trial-division factorization can consume substantial CPU for very large untrusted integers;
- pairwise routing allocates memory quadratically in sequence length;
- CI resolves package dependencies from Python package indexes without a hash-locked dependency set.

Accordingly, callers should bound untrusted integer magnitude, vocabulary size, sequence length, batch size, and exponent width. This release should not be exposed directly as an unconstrained network endpoint.

## Repository layout

```text
README.md                              this canonical project document
NOTICE                                 rights statement
CITATION.cff                           machine-readable citation metadata
pyproject.toml                         package and dependency metadata
src/zpa_lm_reference/geometry.py       exact and exponent-space kernels
src/zpa_lm_reference/codebook.py       deterministic codebook conversion
src/zpa_lm_reference/router.py         fixed causal routing weights
src/zpa_lm_reference/model.py          minimal decoder demonstration
src/zpa_lm_reference/audit.py          machine-readable conformance audit
examples/                              executable demonstrations
tests/                                 independent invariants and regressions
evidence/                              local validation and source-integrity records
../.github/workflows/                  repository-level hosted-CI workflow
```

## Changelog

### Unreleased — repository maintenance

- Moved the ZPA-LM reference from the repository root into `zpa-lm-reference/`.
- Consolidated the user-facing documentation into this single canonical README.
- Hardened codebook JSON validation against duplicate keys and implicit coercion.
- Scoped and hardened the GitHub Actions workflow.
- Added a focused public-scope and security review record.

### 0.1.0 — 2026-08-01

- Added independent divisor-set and GCD closed-form implementations of the keystone identity.
- Added the stable prime-exponent kernel and Fisher–Rao distance.
- Added deterministic integer/exponent codebook utilities.
- Added the zero-trainable-parameter causal divisor router.
- Added a minimal decoder-only PyTorch reference model with a trainable value/backbone path.
- Added conformance, causality, geometry, parameter-audit, determinism, and gradient tests.
- Added the executable audit and tiny-overfit smoke demonstration.
- Added explicit claim, failure, rights, and evidence boundaries.

## Citation

Use `CITATION.cff`. The paper is the authoritative mathematical description; this directory is the reference implementation of its static `fisher_dict` mechanism.

## Rights notice

Copyright © 2026 Thomas Helm / ToraFirma Systems. All rights reserved.

The ZPA-LM mechanism and related work are marked patent pending in the accompanying technical note. This public reference source is supplied to make the stated mechanism inspectable and testable. No open-source licence or patent licence is granted by this project. Contact ToraFirma Systems before redistribution, derivative publication, or commercial use.

This rights statement is not a scientific claim. Correctness remains subject to independent mathematical and computational verification. The canonical machine-readable rights notice is retained in `NOTICE`.
