---
article_id: af_732f9f5ed699c2a2810ef5c6
---

# The outer recipes and their translation

This chapter assembles the specified polynomial $P_*$ from the recipes of the specification and the
natural circuits of the compiler, and proves that the translation of natural-number constraints into
rational point-code constraints is exact. Its statements use both the
[specification](../syntax/README.md) and the [compiler](../compiler/README.md), which is why they form
a chapter after both; the narrative of the translation is in
[translation to rational point codes](../compiler/translation/README.md).

Throughout, $\iota(n)$ is the code of $[n]P_0$ and $\mathrm{Rel}_\tau$ is the rational relation of a
template or recipe.

## The natural-code predicate

The four square products and three additions of $\mathtt{natural}$, typed by globally typed
multiplication, give exactly the codes of the natural numbers.

- [The natural-code predicate](natural-code-semantics.md)

## The power-value and precision recipes

A natural circuit is translated into a model-evaluation recipe: every variable and node gets a point
code, natural variables get the natural template, constants get fixed-scalar templates, and additions,
multiplications and power calls get the corresponding templates.

- [The power-value recipe](recipe-power-value.md)
- [The precision recipe](recipe-precision.md)

## Translation soundness and completeness

Induction along the source DAG gives every node point the code of the node's signed integer value.
Conversely, a natural solution provides rational witnesses for every call.

- [Every node point is the code of the node's value](translation-soundness.md)
- [Natural solutions give rational witnesses](translation-completeness.md)
- [Semantics of the model-evaluation translation](model-evaluation-semantics.md)

The power-value recipe has three signed code inputs, seventy-nine private natural witnesses and an
output code for the value of the power-template polynomial. Replacing each private block of the
precision parent by its private power-value call preserves the existential assignment, and only the
final root is equated to the identity; this is input C on the rational side.

- [Semantics of the power-value recipe](power-value-semantics.md)
- [Semantics of the rational translation](rational-translation.md)

## The specified polynomial

Five composition recipes assemble the value relation and the root; $P_*$ is the polynomial of the root
recipe `integers`.

- [The outer composition recipes](outer-recipes.md)
- [The specified polynomial](literal-polynomial.md)

The witness counts follow from the template counts, the shape of the natural circuit and explicit
arithmetic; the root has one input and $292{,}890{,}231{,}904$ witnesses. In the variable format of the
target statement, the rational zero projection of $P_*$ is the set of $q$ for which the value relation
has a code.

- [Witness accounting of the specified polynomial](witness-accounting.md)
- [The rational zero projection of the specified polynomial](fin-variable-form.md)
