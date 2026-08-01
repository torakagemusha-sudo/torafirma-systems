# Paper-to-code conformance map

| Paper element | Public implementation | Primary verification |
|---|---|---|
| Divisor-counting function `d(n)` | `geometry.divisor_count` | `test_known_factorizations_and_divisor_counts` |
| Keystone identity | `geometry.divisor_kernel` and `geometry.bhattacharyya_divisor_overlap` | exhaustive small-range identity test |
| Prime-exponent equation | `geometry.exponent_kernel` | GCD/product equivalence test |
| Fisher–Rao distance | `geometry.fisher_rao_distance` | identity/range tests |
| Token-to-positive-integer interface | `codebook.ExponentCodebook` | JSON and basis tests |
| Static `fisher_dict` kernel gather | `router.DivisorKernelRouter.raw_kernel` | symmetry and repeated-token tests |
| Causal mask and row normalization | `router.DivisorKernelRouter.forward` | upper-triangle and row-sum tests |
| Value-stream mixing | `model.FisherMixBlock` | forward/backward gradient test |
| One routing matrix reused by layers | `model.TinyZPALM.forward` | direct code inspection and model tests |
| No learned Q/K route | router has buffers only; model audit searches query/key parameters | parameter-audit tests |
| Diagnostic failure registry | `FAILURE_REGISTRY.md` | documentary boundary |
| Context-blindness ceiling | `CLAIMS_AND_LIMITS.md` | repeated-token lexical-row regression |
| Open empirical claim remains open | README and claim boundary | no performance promotion in code/docs |

## Independence of the keystone check

The direct Bhattacharyya path explicitly enumerates divisor sets and counts their intersection. It does not call `gcd`, `divisor_count`, or the closed-form kernel. This makes the exhaustive test a genuine second implementation path rather than a tautological wrapper.

## Numerical conventions

The exact mathematical identity is represented in floating point for normalized overlaps. Tests use tight absolute tolerances. Fisher–Rao input is clamped only within a small roundoff margin. Exponent kernels are evaluated in log space to avoid avoidable product underflow.
