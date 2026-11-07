---
article_id: af_f910740a6871663ab4eb1c3c
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Syntax.powerValueRecipe, ZInQ.Syntax.powerValueRecipe_variableCount
---

# The power-value recipe

The recipe $\mathtt{power\_value}$ is the translation of the power template of the natural
precision polynomial ($3$ inputs, $79$ witnesses) in value mode, without natural
constraints on the inputs and without a power recipe. It has $20$ parameters (three signed
input codes at $X_0,\dots,X_{14}$ and the output code at $X_{15},\dots,X_{19}$), generator
indices $20,21,22$, and every one of the $79$ witnesses of the power template receives a
fresh point and a natural block. Its constants are $4,2,3$, which become
$\mathrm{integer\_constant}_0,\mathrm{integer\_constant}_1,\mathrm{integer\_constant}_2$.
Its root equality equates the point of the root node with the output code; the value of the
power-template polynomial is not required to vanish here.

This is a definition. With the natural circuit statistics it has $17{,}786{,}698$ witnesses
and $17{,}786{,}718$ variables.

## Depends on

- [Translation of a natural circuit into a model-evaluation recipe](model-evaluation-translation.md)
- [Semantics of the natural precision polynomial](../../compiler/natural/natural-polynomial-semantics.md)

## Sources

- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Appendix C.2](../../../sources/syntax-locators.md#appendix-c2-recipes-and-counts)
