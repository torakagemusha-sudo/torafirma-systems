# Permanent failure registry reproduced from the technical note

These items are included so a small reference implementation does not erase the negative evidence recorded in the paper. They are not invitations to repeat the same experiments without new evidence.

## F2 — self-isolating identity positional indexing

A causal mask combined with the paper’s tested coprimality brake and identity-style positional indexing isolated positions to themselves, blocking even straightforward memorization. Status in the paper: falsified as a design choice.

## F8 — symbolic copy tasks as a discriminating benchmark

The fixed kernel represents distributional similarity of divisor-set supports, not symbolic token identity. Under exchangeable keys, copy/induction tasks can collapse to a uniform pattern and therefore do not cleanly discriminate the intended mechanism. Status: falsified as an evaluation choice.

## MSE dictionary-fit collapse

Minimizing mean-squared error between fitted kernel values and target overlaps admits the degenerate direction in which exponents collapse toward zero and all pairwise similarities approach one. The paper therefore specifies rank-oriented objectives rather than raw MSE. Status: falsified as a training objective.

## Random dictionary initialization

The tested random initialization was dominated by the structured Hermite/Calogero–Moser equilibrium initialization on the reported convergence, terminal correlation, and variance criteria. Status: falsified as the default initialization.

## Reference-release consequence

This repository does not implement those failed paths. The toy dictionary is a transparent fixture for mechanism inspection, not a proposal for production dictionary training or linguistic evaluation.
