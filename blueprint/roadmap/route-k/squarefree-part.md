---
article_id: af_c338169afee3640bc4661d06
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.sqf, ZInQ.RouteK.betaOf, ZInQ.RouteK.thetaOf, ZInQ.RouteK.Admissible, ZInQ.RouteK.sqfInt, ZInQ.RouteK.sqfNat, ZInQ.RouteK.sqf_spec, ZInQ.RouteK.sqf_eq_of_eq_mul_sq, ZInQ.RouteK.poleCompleteness_iff_admissible
---

# Admissible inputs, the squarefree part, $\beta$ and $\theta$

A rational $B$ is *admissible* if its reduced denominator is a square, $0<B<1/2$, and
$v_p(B)\ge4$ for every $p\in S_0=\{2,3,5,7,13\}$. These are the hypotheses of pole completeness,
which therefore says that every admissible $B$ satisfies $\Phi(B)$.

The *signed squarefree part* of an integer $N$ is
$\mathrm{sqf}(N)=\operatorname{sign}(N)\prod_{p:\,v_p(N)\text{ odd}}p$, and that of a rational
$x=a/b$ in lowest terms ($b>0$) is $\mathrm{sqf}(x)=\mathrm{sqf}(ab)$. For $x\ne0$, $\mathrm{sqf}(x)$
is squarefree, $x=\mathrm{sqf}(x)\,t^2$ for some nonzero rational $t$, and it is the only
squarefree integer with this property; $\mathrm{sqf}(0)=0$.

A *signed divisor* of $2730=2\cdot3\cdot5\cdot7\cdot13$ is an integer $m$, of either sign, with
$m\mid2730$. For a rational $B$ and such an $m$ put
$$\beta=\mathrm{sqf}(mB),\qquad\theta=\mathrm{sqf}\bigl(m(m-B)\bigr).$$

## Depends on

- [Pole completeness](../main/pole-completeness.md)

## Sources

- [Inputs and the properties of theta](../../sources/route-k-locators.md#inputs-and-the-properties-of-theta)
