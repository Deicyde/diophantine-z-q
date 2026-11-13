---
article_id: af_9b134964ee432901f7803b4a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Translation.powerValue_rel_iff, ZInQ.Translation.powerValue_spec
---

# Semantics of the power-value recipe

Assume the multiplication statement M in its all-input form.
Let $T=T_{\mathcal P}$ be the polynomial function of the power template, of the $82$ variables
$y_0,\dots,y_{81}$ ($y_0,y_1,y_2$ its inputs). For all $a,b,c\in\mathbb Z$ and every $r\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{power\_value}}(\iota(a),\iota(b),\iota(c),r)\iff
\exists\,w\in\mathbb N^{79}:\ r=\iota\bigl(T(a,b,c,w_0,\dots,w_{78})\bigr).$$
So $\mathtt{power\_value}$ satisfies (PV): on three canonical input codes of signed integers it
relates exactly the codes of the values of the power-template polynomial at those integers
and natural witnesses. The value is not required to vanish; nothing is claimed for
non-canonical input tuples.

**Proof sketch.** $\mathtt{power\_value}$ is the translation of $\mathcal P$ in value mode, without
natural constraints on the inputs and without a power recipe, and $\mathcal P$ is well-formed with
bound $82$ and has no call nodes. Case 2 of the semantics of the model-evaluation translation
gives: the relation holds iff $r=\iota(\mathcal P(\theta))$ for some $\theta$ admissible for $\mathcal P$
with $\theta_0,\theta_1,\theta_2=a,b,c$. Admissibility says exactly
$w=(\theta_3,\dots,\theta_{81})\in\mathbb N^{79}$, and $\mathcal P(\theta)=T(a,b,c,w)$ depends on no other
value of $\theta$.

## Depends on

- [The power-value recipe](../../syntax/recipes/recipe-power-value.md)
- [Values and polynomial of a natural circuit](natural-circuit-values.md)
- [Point codes](../../model/point-codes.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)

## Proof depends on

- [Semantics of the model-evaluation translation](model-evaluation-semantics.md)
- [Scope conditions of the natural precision circuit](precision-circuit-scope.md)

## Sources

- [Section 10.4 power value](../../../sources/compiler-translation-locators.md#section-104-power-value-and-precision-parent)
- [Translation artifacts](../../../sources/compiler-translation-locators.md#translation-artifacts)
