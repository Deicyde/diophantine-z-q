---
article_id: af_d2437b2e4fcd099ecdb8c9cb
declaration: theorem
origin: cited
---

# Witness accounting of the specified polynomial

The seven recipes have the following parameter counts, witness counts and variable
counts:

| Recipe | Parameters | Witnesses | Variables |
| --- | ---: | ---: | ---: |
| power_value | 20 | 17,786,698 | 17,786,718 |
| precision | 25 | 292,889,492,836 | 292,889,492,861 |
| close | 11 | 292,890,196,199 | 292,890,196,210 |
| main | 6 | 292,890,231,486 | 292,890,231,492 |
| value_union | 6 | 292,890,231,892 | 292,890,231,898 |
| value | 6 | 292,890,231,899 | 292,890,231,905 |
| integers | 1 | 292,890,231,904 | 292,890,231,905 |

Every variable occurring in the polynomial of a template or recipe has index below its
variable count, and the private blocks of every template and recipe are pairwise disjoint
and disjoint from the variables used outside them. In particular every variable of
$[\![\mathtt{integers}]\!]$ is among $X_0,\dots,X_{292890231904}$, so
$P_*=[\![\mathtt{integers}]\!]$; its input is $X_0$ and it has exactly $292890231904$ witness
variables $X_1,\dots,X_{292890231904}$, the number allowed by the target statement.

**Proof sketch.** For the composition recipes the witness count is the sum of the fresh
ranges and the callee witness counts, read off the recipe definitions. For a
model-evaluation translation it is $3$ (generator) plus, for each explicit witness variable,
$5+140604$; for each constrained input, $140604$; for each distinct nontrivial constant,
$5+1$; for each addition, multiplication and call node, $5+6$, $5+35134$ and
$5+17786698$. Inserting the template counts and the circuit shape gives the expressions of
the witness-count arithmetic. The variable bounds and disjointness are the witness-scope
theorem applied to every template and recipe, by induction along the library and recipe
order.

## Depends on

- [The specified polynomial](../literal-polynomial.md)
- [The outer composition recipes](outer-recipes.md)

## Proof depends on

- [Parameter and witness counts of the templates](template-witness-counts.md)
- [Shape of the natural precision circuit](natural-circuit-statistics.md)
- [The witness-count arithmetic](witness-count-identity.md)
- [Witness scope of constructed templates and recipes](../language/builder-well-formed.md)
- [The precision recipe](recipe-precision.md)
- [The power-value recipe](recipe-power-value.md)

## Sources

- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Section 12.2](../../../sources/syntax-locators.md#section-122-syntax-bounds)
- [Appendix C opening](../../../sources/syntax-locators.md#appendix-c-opening)
