# Security Policy

## Supported surfaces

This repository publishes **reference implementations, proof packs, and public evidence** for independent verification. It is not a production service.

| Surface | Status |
|---------|--------|
| ZPA-LM Reference (Python package) | Public reference — report defects |
| Arithmetic Clock (Lean pack + tools) | Public proof pack — report defects in tools/scripts |
| ORBIT public benchmark PDF | Static artefact |
| Firmastate-IDE / product services | Outside this repo (see https://torafirma.com) |

## Reporting a vulnerability

If you believe you have found a security-relevant issue (e.g. a script that could be abused when run on untrusted input, or accidental exposure of credentials in history):

1. **Do not** open a public issue with exploit details.
2. Email **security@torafirma.com** (or the contact on https://torafirma.com/contact) with:
   - Affected path / commit
   - Description and impact
   - Minimal reproduction if possible
3. Allow reasonable time for assessment before public disclosure.

## Scope notes

- Mathematical claim disputes are **not** security issues; use the research / verification issue templates.
- This repo is published in good faith. Systematic abuse of access may affect future public releases (see README).
