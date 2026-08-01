# Reproducibility

## Deterministic reference path

The algebraic and routing checks are deterministic. The tiny model contains no dropout. Repeated CPU forwards with fixed weights and inputs are tested bit-for-bit in the local environment.

The training smoke script sets a fixed PyTorch seed and one CPU thread. Its purpose is execution evidence, not a statistical performance result. Minor floating-point differences across PyTorch releases or hardware may change the final decimal values while preserving the qualitative pass condition.

## Recommended commands

```bash
python -m pip install -e ".[test]"
pytest -q
python -m zpa_lm_reference.audit --limit 128 > audit.json
python examples/tiny_overfit.py --steps 120 --json > tiny-overfit.json
```

## Independent reproduction

For a clean-room check of the keystone theorem, implement only the definitions:

1. enumerate divisors of `n` and `m`;
2. form uniform distributions on those supports;
3. compute their Bhattacharyya coefficient;
4. compare against `d(gcd(n,m))/sqrt(d(n)d(m))`.

No model code is needed to test the mathematical identity.
