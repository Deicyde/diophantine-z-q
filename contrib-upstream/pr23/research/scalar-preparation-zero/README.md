# Preparation zero: 383 variables above PR #11

This conditional research layer sets `W=N` in the order-31 scalar chain
and specializes the scalar preparation to zero. Two free witnesses and
one equation disappear. The anchor remains `3^2130`.

| | Parent #11 | This layer |
| --- | ---: | ---: |
| Variables, including the input | 385 | **383** |
| Quadratic residuals | 353 | **352** |
| Quartic monomials | 26,200 | **26,019** |
| Maximum coefficient digits / bits | 682 / 2,266 | **682 / 2,266** |

The maximum coefficient is `28902 * 3^1420`. All variables occur, the
degree is four, the content is one, and the coefficient of `x0^4` is one.
The decimal table SHA-256 is
`8faea54ef4a9d8cf155205a50c956df20d36e3eec4183b50b39b2c0b87183b0d`.

[PROOF.md](PROOF.md) checks positivity, order-31 soundness, local squareclasses,
the finite-depth hypotheses, and the simultaneous real/finite choice of the
final shared point. This changes the physical scalar input, so completeness
needs its own argument. [APPLICATION_CONTRACT.json](APPLICATION_CONTRACT.json)
is an author submission pending independent review, not an acceptance record.
The global arithmetic inputs remain conditional.

Run from the repository root:

```sh
python3 -B research/scalar-preparation-zero/reproduce.py --output build/preparation-zero
```

The runner verifies the source bindings and frozen parent manifest, checks
the three changed rows and deleted conic, checks the two unused slots before
omitting them, and replays the compiler, conic transport and every final
coefficient. Negative controls cover both the changed equations and an
attempt to omit a coordinate that still has a consumer. The output must
match [EXPECTED.json](EXPECTED.json). A separate CI workflow runs this layer
without changing the parent packets or their bound workflow.
