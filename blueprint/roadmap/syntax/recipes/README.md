---
article_id: af_519a7625ef80e8c6f677962e
---

# Recipes and witness accounting

A natural circuit is translated into a model-evaluation recipe: every variable and node
gets a point code, natural variables get the natural template, constants get fixed-scalar
templates, and additions, multiplications and power calls get the corresponding templates.

- [Translation of a natural circuit into a model-evaluation recipe](model-evaluation-translation.md)
- [Witness scope of constructed templates and recipes](builder-well-formed.md)
- [The template library](template-library.md)

The power-value and precision recipes, the five composition recipes that assemble the value
relation and the root, and the accounting of $P_*$ use the compiler's natural circuits, so they are
in [the chapter on the outer recipes and their translation](../../recipe-translation/README.md).

The witness counts follow from the template counts, the shape of the natural circuit
(proved in the compiler chapter:
[shape of the natural precision circuit](../../compiler/natural/universal/circuit-node-counts.md))
and explicit arithmetic; the root has one input and $292{,}890{,}231{,}904$ witnesses.

- [Parameter and witness counts of the templates](template-witness-counts.md)
- [The witness-count arithmetic](witness-count-identity.md)
