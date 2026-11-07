---
article_id: af_d2437b2e4fcd099ecdb8c9cb
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.specRecipes, ZInQ.Syntax.specLib, ZInQ.Syntax.specLib_wf, ZInQ.Syntax.powerValueRecipe_variableCount, ZInQ.Syntax.precisionRecipe_variableCount_le, ZInQ.Syntax.specClose_witnessCount, ZInQ.Syntax.specMain_witnessCount, ZInQ.Syntax.specValueUnion_witnessCount, ZInQ.Syntax.specValue_witnessCount, ZInQ.Syntax.specIntegers_variableCount, ZInQ.Syntax.specIntegers_variableCount_eq, ZInQ.Syntax.specIntegers_variableCount_le, ZInQ.Syntax.vars_integers_lt
---

# Witness accounting of the specified polynomial

The seven recipes have the following parameter counts, and at most the following witness
and variable counts:

| Recipe | Parameters | Witnesses | Variables |
| --- | ---: | ---: | ---: |
| power_value | 20 | 17,786,698 | 17,786,718 |
| precision | 25 | 292,889,492,836 | 292,889,492,861 |
| close | 11 | 292,890,196,199 | 292,890,196,210 |
| main | 6 | 292,890,231,486 | 292,890,231,492 |
| value_union | 6 | 292,890,231,892 | 292,890,231,898 |
| value | 6 | 292,890,231,899 | 292,890,231,905 |
| integers | 1 | 292,890,231,904 | 292,890,231,905 |

The row of power_value is exact, and so are the differences between consecutive rows from
precision on; in particular integers has exactly $739{,}069$ variables more than precision
has witnesses.

Every variable occurring in the polynomial of a template or recipe has index below its
variable count. In particular every variable of $[\![\mathtt{integers}]\!]$ is among
$X_0,\dots,X_{292890231904}$, so $P_*$, which is $[\![\mathtt{integers}]\!]$ read in these
variables, has input $X_0$ and its witness variables among $X_1,\dots,X_{292890231904}$, the
variables allowed by the target statement, which need not all occur.

The manuscript states the table as exact counts, and the private blocks of every template
and recipe as pairwise disjoint and disjoint from the variables used outside them. The exact
counts follow in the same way from the exact node statistics. The variable format of the
target needs neither; the relational statements of the compiler and assembly chapters prove
the separation of blocks they use.

**Proof sketch.** For the composition recipes the witness count is the sum of the fresh
ranges and the callee witness counts, read off the recipe definitions. For a
model-evaluation translation it is $3$ (generator) plus, for each explicit witness variable,
$5+140604$; for each constrained input, $140604$; for each distinct nontrivial constant,
$5+1$; for each addition, multiplication and call node, $5+6$, $5+35134$ and
$5+17786698$. Inserting the template counts and the bounds of the circuit shape gives the
table, through the witness-count arithmetic. The variable bounds are the witness-scope
theorem applied to every template and recipe, by induction along the library and recipe
order.

## Depends on

- [The specified polynomial](../literal-polynomial.md)
- [The outer composition recipes](outer-recipes.md)

## Proof depends on

- [Parameter and witness counts of the templates](template-witness-counts.md)
- [Shape of the natural precision circuit](../../compiler/natural/universal/circuit-node-counts.md)
- [The witness-count arithmetic](witness-count-identity.md)
- [Witness scope of constructed templates and recipes](../language/builder-well-formed.md)
- [The precision recipe](recipe-precision.md)
- [The power-value recipe](recipe-power-value.md)

## Sources

- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
- [Section 12.2](../../../sources/syntax-locators.md#section-122-syntax-bounds)
- [Appendix C opening](../../../sources/syntax-locators.md#appendix-c-opening)
