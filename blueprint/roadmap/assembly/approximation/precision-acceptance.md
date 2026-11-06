---
article_id: af_be2811faba7749bf8b907409
declaration: lemma
origin: bridged
---

# Acceptance by the precision polynomial is the precision predicate

For every $c=(c_0,\dots,c_4)\in\mathbb N^5$,
$$\operatorname{accepts}(c)\iff\operatorname{Prec}(\operatorname{dec}c_0,\operatorname{dec}c_1,\operatorname{dec}c_2,\operatorname{dec}c_3,\operatorname{dec}c_4),$$
where $\operatorname{accepts}$ is the precision relation in the semantics of the natural precision
polynomial. With $(n,\kappa,a,l,j)$ the signed decoding of $c$, that relation is the conjunction of:

1. the early tests $n\notin\mathcal C$, $\kappa\ne0$, $a\ge1$, $l\ge1$, $j=na$;
2. admissibility of $l$, $a$ and $j$, that is, $[k]P_0$ is an affine point with nonzero ordinate
   for $k\in\{l,a,j\}$;
3. $|r(a,j)-n|<\epsilon_l$, with $z$, $\epsilon_l$ and $r(a,j)$ formed on these admissible indices;
4. $4\epsilon_l\cdot4^{\mathcal B(n,\kappa)}<1$, where $\mathcal B(n,\kappa)=A^{(0)}_{\rm ht}|\kappa F(n)|^{24}$,
   $A^{(0)}_{\rm ht}=2\cdot10^{13}\max(1,C_{\rm cm},Q_0^{17})$ and $Q_0=D^{DE_0}$.

$\operatorname{Prec}$ is the predicate of the precision quantities. No hypothesis is needed.

**Proof sketch.** Write $(n,\kappa,a,l,j)=(\operatorname{dec}c_0,\dots,\operatorname{dec}c_4)$. The early tests
appear in both predicates.

*Admissibility is automatic.* Under the early tests, $a,l\ge1$, and $n\ne0$ because
$0\in\mathcal C$, so $j=na\ne0$. By the nonzero-multiples lemma, $[k]P_0$ is affine with nonzero
abscissa and ordinate for $k=l,a,j$. So item 2 follows from item 1, and dropping it changes
nothing.

*The window quantities agree.* On an affine point with $y\ne0$ (hence $x\ne0$ on $E$), both
definitions give $z=-x/y$. So $z_l$, $z_a$, $z_j$, $\epsilon_l=|u_l|+|v_l|$ and
$r(a,j)=\frac12\operatorname{Tr}(z_j/z_a)$ coincide, and item 3 is the window condition of $\operatorname{Prec}$.

*The constants agree.* $A_0$ uses $R_{\rm ht}=\max(D,317,10^{12})$ and $A^{(0)}_{\rm ht}$ uses $R=D$. These
are equal because $D\ge10^{12}$, which is proved without evaluating $D$:
$D=F_0\cdot3^{256F_0^4}\ge F_0=324!\ge15!=1307674368000>10^{12}$, using
$3^{256F_0^4}\ge1$ and the monotonicity of the factorial. Hence $Q_{R_{\rm ht}}=Q_0$, $A_0=A^{(0)}_{\rm ht}$ and
$B(n,\kappa)=\mathcal B(n,\kappa)$, so item 4 is the last condition of $\operatorname{Prec}$.

## Depends on

- [The precision quantities and the precision predicate](precision-predicate.md)
- [Semantics of the natural precision polynomial](../../compiler/natural/natural-polynomial-semantics.md)

## Proof depends on

- [Nonzero multiples of the generator](../value-templates/nonzero-multiples.md)

## Sources

- [Section 10 precision predicate](../../../sources/assembly-locators.md#section-10-precision-predicate)
- [Section 4 height constants](../../../sources/assembly-locators.md#section-4-height-constants)
