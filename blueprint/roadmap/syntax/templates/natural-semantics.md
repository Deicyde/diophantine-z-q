---
article_id: af_b1ec412439534d1852861547
declaration: theorem
origin: cited
---

# Semantics of the natural-code template

Assume the multiplication statement M: for all $P,Q,R\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{multiply}}(P,Q,R)\iff\exists\,a,b\in\mathbb Z,\ (P,Q,R)=(\iota(a),\iota(b),\iota(ab)).$$
Then for every $A\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{natural}}(A)\iff\exists\,n\in\mathbb N,\ A=\iota(n).$$

**Proof sketch.** The natural template has no rational constants, so its polynomial is
$\kappa(\varphi)^2$ for the conjunction $\varphi$ of its seven calls; it vanishes exactly when
$\varphi$ holds. The seven private blocks are pairwise disjoint and none of their variables
occurs in a parameter of a call, so by the private-block statement
$\mathrm{Rel}_{\mathtt{natural}}(A)$ holds exactly when there are $\sigma_i,\Sigma_i\in\mathbb Q^5$
($i=0,\dots,3$) and $\pi_1,\pi_2\in\mathbb Q^5$ with
$$\mathrm{Rel}_{\mathtt{multiply}}(\sigma_i,\sigma_i,\Sigma_i)\ (i=0,\dots,3),\quad
\mathrm{Add}_{\rm raw}(\Sigma_0,\Sigma_1,\pi_1),\quad \mathrm{Add}_{\rm raw}(\pi_1,\Sigma_2,\pi_2),\quad
\mathrm{Add}_{\rm raw}(\pi_2,\Sigma_3,A).$$

($\Rightarrow$) By M, for each $i$ there are $a_i,b_i\in\mathbb Z$ with $\sigma_i=\iota(a_i)=\iota(b_i)$
and $\Sigma_i=\iota(a_ib_i)$. From $[a_i]P_0=[b_i]P_0$ (codes are injective) we get
$[a_ib_i]P_0=[a_i]([b_i]P_0)=[a_i]([a_i]P_0)=[a_i^2]P_0$, so $\Sigma_i=\iota(a_i^2)$; injectivity
of $n\mapsto\iota(n)$ is not needed. The raw addition contract, applied three times to
canonical inputs, gives $\pi_1=\iota(a_0^2+a_1^2)$, $\pi_2=\iota(a_0^2+a_1^2+a_2^2)$ and
$A=\iota(n)$ with $n=a_0^2+a_1^2+a_2^2+a_3^2\in\mathbb N$.

($\Leftarrow$) Let $A=\iota(n)$ with $n\in\mathbb N$. By Lagrange's four-square theorem
$n=a_0^2+a_1^2+a_2^2+a_3^2$ with $a_i\in\mathbb N$. Take $\sigma_i=\iota(a_i)$,
$\Sigma_i=\iota(a_i^2)$, $\pi_1=\iota(a_0^2+a_1^2)$ and $\pi_2=\iota(a_0^2+a_1^2+a_2^2)$. The four
multiplication relations hold by M (with $a=b=a_i$) and the three raw additions by the raw
addition contract; the private-block statement assembles the witnesses.

This is the natural predicate of Section 3.1: the four tuples $\sigma_i$ are untyped, and it is
the multiplication calls that type them before their squares are added, so the statement
uses multiplication completeness and not only the generator proposition.

## Depends on

- [The natural-code template](template-natural.md)
- [The multiplication template](template-multiply.md)
- [The codes of multiples of the generator](../../model/point-codes.md)
- [Semantics of templates and recipes](../template-semantics.md)

## Proof depends on

- [Raw addition](../../model/raw-addition.md)
- [Elementary properties of codes](../../model/field/point-code-properties.md)
- [Private witness blocks](../language/existential-lifting.md)
- [Template construction from formulas](../language/builder-soundness.md)
- [Sums of squares and products over the rationals](../sum-of-squares-semantics.md)

## Informally uses

- [Correctness of the multiplication template](../../multiplication/multiplication-template.md)

## Sources

- [Section 3.1](../../../sources/syntax-locators.md#section-31-membership-and-natural-codes)
- [Section 10 translation](../../../sources/syntax-locators.md#section-10-translation)
