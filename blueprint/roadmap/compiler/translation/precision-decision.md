---
article_id: af_4214350c476f1cec6240dc05
declaration: theorem
origin: bridged
---

# The precision recipe decides the precision predicate

Assume the Mordell-Weil hypothesis and the multiplication statement M in its all-input form.
For all $E_0,\dots,E_4\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{precision}}(E_0,\dots,E_4)\iff\exists\,\mathbf c\in\mathbb N^5:\
E_i=\iota(c_i)\ (0\le i\le4)\ \text{and}\ \mathrm{accepts\_naturals}(\mathbf c),$$
where $\mathrm{accepts\_naturals}$ is the precision predicate. In particular, for integers
$n,\kappa,a,l,j$, the precision recipe holds at the codes of their signed encodings exactly
when $n\notin\mathcal C$, $\kappa\ne0$, $a,l\ge1$, $j=na$, $|r(a,j)-n|<\epsilon_l$ and
$4\epsilon_l<4^{-A^{(0)}_{\rm ht}|\kappa F(n)|^{24}}$ (the degenerate rejections of the predicate
never apply, by the nondegeneracy of nonzero multiples of $P_0$).

**Proof sketch.** By the rational translation, $\mathrm{Rel}_{\mathtt{precision}}(E)$ iff
$E_i=\iota(c_i)$ with $\mathbf c\in\mathbb N^5$ and $C(\mathbf c,\mathbf z)=0$ for some natural
$\mathbf z$; by equation (C.4) the latter is $\mathrm{accepts\_naturals}(\mathbf c)$. The unfolded
form uses $\operatorname{enc}^{-1}(\operatorname{enc}(m))=m$ and the nondegeneracy lemma.

## Depends on

- [Semantics of the rational translation](rational-translation.md)
- [The precision relation](../natural/precision/precision-relation.md)
- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)
- [Mordell–Weil for the generator curve](../../main/mordell-weil.md)

## Proof depends on

- [Semantics of the natural precision polynomial](../natural/natural-polynomial-semantics.md)
- [Nonzero multiples of the generator](../../assembly/value-templates/nonzero-multiples.md)

## Sources

- [Section 10.3 specialization](../../../sources/compiler-translation-locators.md#section-103-specialization)
- [Section 10 opening](../../../sources/compiler-translation-locators.md#section-10-opening)
- [Section 11 precision contract](../../../sources/compiler-translation-locators.md#section-11-precision-contract)
