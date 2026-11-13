---
article_id: af_519a7625ef80e8c6f677962e
---

# Recipes and witness accounting

A natural circuit is translated into a model-evaluation recipe: every variable and node
gets a point code, natural variables get the natural template, constants get fixed-scalar
templates, and additions, multiplications and power calls get the corresponding templates.

- [Translation of a natural circuit into a model-evaluation recipe](model-evaluation-translation.md)
- [The power-value recipe](recipe-power-value.md)
- [The precision recipe](recipe-precision.md)

Five composition recipes assemble the value relation and the root.

- [The outer composition recipes](outer-recipes.md)

The witness counts follow from the template counts, the shape of the natural circuit
(proved in the compiler chapter:
[shape of the natural precision circuit](../../compiler/natural/universal/circuit-node-counts.md))
and explicit arithmetic; the root has one input and $292{,}890{,}231{,}904$ witnesses.

- [Parameter and witness counts of the templates](template-witness-counts.md)
- [The witness-count arithmetic](witness-count-identity.md)
- [Witness accounting of the specified polynomial](witness-accounting.md)

In the variable format of the target statement, the rational zero projection of $P_*$ is
the set of $q$ for which the value relation has a code.

- [The rational zero projection of the specified polynomial](fin-variable-form.md)
