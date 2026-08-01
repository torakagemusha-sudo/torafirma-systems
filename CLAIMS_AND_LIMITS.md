# Claims and limits

This document prevents implementation evidence from being silently promoted into a broader scientific claim.

## C1 — algebraic identity

For positive integers `n,m`, let `D_n` be the divisor set of `n`, and let `U_n` be uniform on `D_n`. Then

```text
BC(U_n, U_m)
= |D_n ∩ D_m| / sqrt(|D_n| |D_m|)
= d(gcd(n,m)) / sqrt(d(n)d(m))
= q(n,m).
```

The set identity `D_n ∩ D_m = D_gcd(n,m)` proves the result. The Fisher–Rao expression `2 arccos(q)` follows through the square-root embedding of the probability simplex.

## Implementation claim

The repository computes the same kernel through three paths:

1. explicit divisor-set distributions;
2. the GCD/divisor-count closed form;
3. the prime-exponent product form.

It constructs a causal row-normalized routing matrix and applies it to a trainable value stream. Automated tests check the declared invariants.

## Explicit non-claims

This release does not establish that:

- the entire language model has zero parameters;
- the toy codebook has useful linguistic semantics;
- the fixed mixer is context-sensitive;
- the mixer dominates learned attention;
- the mixer dominates position-only or other content-blind controls;
- the local tiny-overfit example predicts generalization;
- a continuous real-exponent code has a literal finite divisor-set interpretation;
- private later extensions are reproduced here.

## Architectural ceiling

With one static token-to-code dictionary, the pair affinity is content-aware but context-blind. The same token pair receives the same unmasked kernel value in every sentence. Causal position changes which earlier values are available, but it does not make the lexical kernel itself context-dependent.

## Falsification posture

A defect in the theorem should be demonstrated by a counterexample to the set/counting identity. A defect in the implementation should be demonstrated by a failing conformance test or an independent implementation mismatch. A language-model performance claim requires matched baselines, declared budgets, multiple seeds, and full reporting; none is inferred from this repository’s smoke demonstrations.
