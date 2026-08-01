# Evidence state

The repository distinguishes local execution from hosted continuous integration.

## Local release validation

The `evidence/` directory is generated from the exact source bundle for v0.1.0 and records:

- the Python, NumPy, and PyTorch environment;
- the full pytest result;
- the machine-readable conformance audit;
- the deterministic tiny-overfit smoke result;
- SHA-256 hashes of the release files.

These records establish **local execution only**. They do not become hosted-CI evidence until the workflow has run successfully on GitHub.

## Hosted CI gate

`.github/workflows/ci.yml` performs the following on clean Ubuntu runners:

1. install the package and test dependencies;
2. run the complete test suite;
3. run the conformance audit;
4. run a bounded tiny-overfit smoke check on one Python version.

A public release should not describe CI as green until the corresponding GitHub Actions run is visible and successful.
