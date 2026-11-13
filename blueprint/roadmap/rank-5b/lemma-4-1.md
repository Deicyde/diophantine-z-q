---
article_id: af_a5500dafd0c12cf6ec06a85e
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.sel2_ncard_eq_four_mul, ZInQ.RouteK.Rank5b.sel2HEquivKer, ZInQ.RouteK.Rank5b.sel2HEquivKer_apply, ZInQ.RouteK.Rank5b.sel2_ncard_eq_card_sols, ZInQ.RouteK.Rank5b.sel2_eq_image
---

# The 2-Selmer group and the kernel of $M_1$ (Lemma 4.1)

Let $n>0$ be squarefree with $n\equiv5\pmod8$. To a tuple $(a_0,a_1,b_0,b_1,u,v)$ over the
primes of $n$ attach the pair $a=(-1)^{a_0}2^{a_1}\prod_pp^{u_p}$,
$b=(-1)^{b_0}2^{b_1}\prod_pp^{v_p}$. Then $\mathrm{Sel}_2(C_n)$ is exactly the set of pairs of the
solutions of $\Sigma(\mathcal C_n)$, and
$$|\mathrm{Sel}_2(C_n)|=4\,|\ker M_1|,\qquad\text{that is}\qquad
\dim\mathrm{Sel}_2(C_n)=2+\operatorname{corank}M_1 .$$
Moreover the tuples whose pair lies in $\mathrm{Sel}_2(C_n)$ and which have $b_1=0$ ($b$ odd) and
$a_0=y\cdot u$ ($a\equiv1\pmod4$) form a subspace $H$, and $(u,v)\mapsto(u+v,\,u)$ is a bijection
from $H$ onto $\ker M_1$; here $u+v$ and $u$ are the indicator vectors of the primes dividing $ab$
and $a$.

**Proof sketch.** By Proposition 0 a tuple solves $\Sigma(\mathcal C_n)$ exactly when its pair
lies in $\mathrm{Sel}_2(C_n)$, every Selmer class is such a pair, and distinct tuples give distinct
pairs. The configuration of $n$ has product class $5$, and its matrix $M_1$ is that of $n$; the
statement is the class-5 statement for the configuration of $n$.

## Depends on

- [Smith's matrices $L$, $M_1$ and $M_{5b}$](smith-matrices.md)
- [Proposition 0](../selmer/proposition-0.md)

## Proof depends on

- [The Selmer system of a class-5 configuration and the kernel of $M_1$](kernel-class-five.md)

## Sources

- [Lemma 4.1](../../sources/rank-5b-locators.md#lemma-41)
