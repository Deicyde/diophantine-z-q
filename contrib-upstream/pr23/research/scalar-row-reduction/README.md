# Scalar row reduction: 379 variables, 425 digits

Conditional research above #17 (`eb00b7c9c5be2e8666c0403c750c6c780cf78563`). Exact row operations and a private scalar coordinate elimination preserve the parent's rational input projection. A specified input-fixed diagonal map reduces coefficient size. The detector route and all arithmetic orders stay unchanged.

Run from the repository root with Python 3.12+ and Node:

```sh
python3 -B research/scalar-row-reduction/reproduce.py --output build/row379
python3 -B scripts/check_audit_history.py --self-test
```

The full deterministic output has 379 variables including the input, 348 quadratic residuals, 26,021 quartic monomials and coefficients of at most 425 decimal digits / 1,410 bits. Every coordinate is active; content and input fourth-power coefficient are one. `EXPECTED.json` binds the complete generated decimal table. No full expansion is committed here; CI uploads it. No optimization package is needed.

Read `PROOF.md`, `APPLICATION_CONTRACT.json`, `FINDINGS.json` and `HANDOFF.md`. The source and finite checks are author submissions pending a separately authored acceptance at the exact final head. Historical contributor notes are preserved in `prior-investigation/`; their unproved candidates are not dependencies or accepted results. Version 13 remains the current manuscript/PDF and release. Inherited global arithmetic, manuscript incorporation and designated App approval remain separate.
