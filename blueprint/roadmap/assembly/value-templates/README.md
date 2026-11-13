---
article_id: af_255a67c8042b3c09f99de017
---

# The value templates and their relations

The value relation is assembled from the membership template, three value templates
(signed encoding, coordinate window, value test), the exceptional-values template and the
precision recipe, combined by five composition recipes. This section proves what each
template expresses on arbitrary rational inputs. Every proof has the same shape: the
template polynomial is the square of a compiled formula whose calls have disjoint private
blocks, so the private-witness lemma replaces each call by its relation, and the model
statements identify the relations on codes.

Nonzero multiples of $P_0$ are affine with nonzero coordinates
([nonzero multiples of the generator](../../model/descent/nonzero-multiples.md), in the model
chapter); this makes every local parameter and inverse abscissa below well-defined.

## Natural and signed codes

The natural-code template types four untyped tuples by multiplication before adding their
squares, so it accepts exactly $\iota(\mathbb N)$ by Lagrange's theorem; this is
[the natural-code predicate](../../compiler/translation/natural-code-semantics.md) of the
compiler chapter, with M supplied by the multiplication template. The signed encoding links
a signed code $\iota(m)$ to the natural code $\iota(\operatorname{enc}m)$, in which form the integer
enters the precision relation.

- [Semantics of the signed encoding](signed-encoding-semantics.md)

## The coordinate window

For nonzero $a,l$ the coordinate-window template expresses the strict window
$|t-r(a,j)|<\epsilon_l$, with $r(a,j)=\frac12\operatorname{Tr}(z_j/z_a)$ and $\epsilon_l=|u_l|+|v_l|$.

- [Semantics of the coordinate window](close-coordinates-semantics.md)

## The exceptional values

Double-and-add chains of raw additions, started at the literal origin and the fixed signed
generator, produce the codes of the six contact values.

- [Double-and-add chains](double-and-add-chains.md)
- [Semantics of the exceptional values](exceptions-semantics.md)

## The value test

On indices, the value test is the relation $\operatorname{Test}(n,\kappa,t)$ of the six local tests.

- [The six local tests](six-local-tests.md)
- [Semantics of the value-test template](value-test-semantics.md)

## The outer recipes

The composition recipes $\mathtt{close}$, $\mathtt{main}$, $\mathtt{value\_union}$ and $\mathtt{value}$
conjoin or multiply their calls; the shared shift appears in both calls of $\mathtt{main}$.

- [Relations of the outer recipes](outer-recipe-relations.md)
