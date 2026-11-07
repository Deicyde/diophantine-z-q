---
article_id: af_c9e3809c9b4af907ad88dee8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Syntax.guardTemplate_rel_codes3_iff, ZInQ.Syntax.guardTemplate_rel_iff_not_falseTriple_guardPoly
---

# Semantics of the guard template

For all $P_0,P_1,P_2\in\mathbb Q^5$,
$$\mathrm{Rel}_{\mathtt{multiply.guard}}(P_0,P_1,P_2)\iff\neg\,\exists\,(a,b,c)\in\mathbb Z^3:\
|a|,|b|,|c|\le T,\ ab\ne c,\ (P_0,P_1,P_2)=(\iota(a),\iota(b),\iota(c)).$$
That is, the zero set of $G_T$ over $\mathbb Q$ is exactly the finite set of false triples
of codes in the box, and the guard holds exactly off that set. Nothing here bounds or
evaluates $T$.

**Proof sketch.** By the inverse-witness statement the relation holds exactly when
$G_T(P_0,P_1,P_2)\ne0$, that is, when no factor vanishes. A factor
$\sum_j(D_{abc}X_j-(D_{abc}/B_j)A_j)^2$ vanishes at rational $X$ exactly when
$D_{abc}X_j=(D_{abc}/B_j)A_j$ for all $j$, i.e. $X_j=A_j/B_j$ since $D_{abc}>0$, i.e.
$(X_1,\dots,X_{15})=(\iota(a),\iota(b),\iota(c))$.

## Depends on

- [The guard template](template-guard.md)
- [The codes of multiples of the generator](../../model/point-codes.md)

## Proof depends on

- [Inverse witnesses](../nonzero-gadgets.md)
- [Sums of squares and products over the rationals](../sum-of-squares-semantics.md)

## Sources

- [Appendix C.1](../../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
- [Section 2.2](../../../sources/syntax-locators.md#section-22-catalogue-and-formal-multiple)
