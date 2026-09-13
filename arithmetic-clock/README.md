# Arithmetic Clock

This package contains the Lean 4 sources for a finite arithmetic clock on the divisor lattice of 60.

Author: Thomas Helm

Affiliation: Torafirma Systems

License: Apache-2.0

## Verification status

Certification status is determined by the certificate suite included with the package. The package is formally certified only when all seven required certificates are present and report PASS. Its sources have passed deterministic static qualification; without the complete PASS suite, a fresh build and declaration audit with Lean 4.19.0 and the pinned Mathlib revision are still required.

## Pinned environment

- Lean: 4.19.0
- Mathlib: `c44e0c8ee63ca166450922a373c7409c5d26b00b`

The exact dependency revisions are recorded in `DEPENDENCIES.json`. The top-level `ArithmeticClock.lean` facade imports the three public entry modules.
