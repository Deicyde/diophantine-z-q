---
article_id: af_517787cb87d502cb82d7e15b
declaration: theorem
origin: cited
---

# The relation Close

Assume the six-contact estimate, pole completeness, the Mordell–Weil hypothesis and the
twenty-two-prime pattern. Then for all $N,K\in\mathbb Q^5$ and $t\in\mathbb Q$,
$\mathrm{Rel}_{\mathtt{close}}(N,K,t)$ holds exactly when there are $n,\kappa,a,l\in\mathbb Z$ with
$$N=\iota(n),\quad K=\iota(\kappa),\quad\operatorname{Prec}(n,\kappa,a,l,na),\quad |t-r(a,na)|<\epsilon_l .$$
This is the manuscript's $\operatorname{Close}(N,\mathcal K,t)$: choose $A,L,J$, link the five
signed codes $N,\mathcal K,A,L,J$ to the precision inputs in the order $(n,\kappa,a,l,j)$, and
impose $|t-r(a,j)|<\epsilon_l$ on the same coordinates.

**Proof sketch.** By the relations of the outer recipes, $\mathrm{Rel}_{\mathtt{close}}(N,K,t)$
holds exactly when there are $A,L,J,E_0,\dots,E_4$ with five signed-encoding relations, the
precision relation and the coordinate window. Input C, that is, the semantics of the rational
translation applied to the precision recipe together with the semantics of the natural
precision polynomial, is used in the form: for all $E_0,\dots,E_4\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{precision}}(E_0,\dots,E_4)\iff\exists\,c\in\mathbb N^5:\ E_i=\iota(c_i)\ (0\le i\le4)\ \text{and}\
\operatorname{Prec}(\operatorname{dec}c_0,\dots,\operatorname{dec}c_4).$$

($\Rightarrow$) The signed encodings give $\Sigma_i=\iota(m_i)$ and $E_i=\iota(\operatorname{enc}m_i)$ with
$(m_0,\dots,m_4)=(n,\kappa,a,l,j)$. By input C and injectivity of $\iota$, $c_i=\operatorname{enc}m_i$, so
$\operatorname{Prec}(n,\kappa,a,l,j)$, in particular $j=na$. The coordinate window gives indices
$a',l',j'$ with $A=\iota(a')$ etc. and $|t-r(a',j')|<\epsilon_{l'}$; injectivity gives
$(a',l',j')=(a,l,j)$.

($\Leftarrow$) Put $j=na$, $A=\iota(a)$, $L=\iota(l)$, $J=\iota(j)$ and $E_i=\iota(\operatorname{enc}m_i)$. The
signed encodings hold, the precision relation holds by input C since $\operatorname{dec}\circ\operatorname{enc}$
is the identity, and the coordinate window holds because $a,l\ge1$ are nonzero.

## Depends on

- [The precision quantities and the precision predicate](precision-predicate.md)
- [The outer composition recipes](../../syntax/recipes/outer-recipes.md)
- [Point codes](../../model/point-codes.md)
- [The six-contact height estimate](../../main/six-contact-estimate.md)
- [Pole completeness](../../main/pole-completeness.md)
- [Mordell–Weil for the generator curve](../../main/mordell-weil.md)
- [The twenty-two-prime pattern](../../main/prime-pattern.md)

## Proof depends on

- [Relations of the outer recipes](../value-templates/outer-recipe-relations.md)
- [Semantics of the signed encoding](../value-templates/signed-encoding-semantics.md)
- [Semantics of the coordinate window](../value-templates/close-coordinates-semantics.md)
- [Semantics of the rational translation](../../compiler/translation/rational-translation.md)
- [Semantics of the natural precision polynomial](../../compiler/natural/natural-polynomial-semantics.md)
- [Nonzero multiples of the generator](../value-templates/nonzero-multiples.md)

## Sources

- [Section 11.1 approximation](../../../sources/assembly-locators.md#section-111-approximation)
- [Section 10 precision predicate](../../../sources/assembly-locators.md#section-10-precision-predicate)
- [Saved specification outer recipes](../../../sources/assembly-locators.md#saved-specification-outer-recipes)
