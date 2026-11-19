---
article_id: af_58c1c55a4c56a997a6d9dadf
declaration: def
origin: background
statement: formalized
lean: ZInQ.RouteK.Rank.sqfRep, ZInQ.RouteK.Rank.sqfRep_squarefree, ZInQ.RouteK.Rank.sqc_sqfRep, ZInQ.RouteK.Rank.sqfRep_ne_zero, ZInQ.RouteK.Rank.sqfRep_injective, ZInQ.RouteK.Rank.exists_squarefree_sqc_class, ZInQ.RouteK.Rank.exists_squarefree_sqc, ZInQ.RouteK.Rank.exists_squarefree_sqc_int, ZInQ.RouteK.Rank.sqEq_sqfRep, ZInQ.RouteK.Rank.repPair, ZInQ.RouteK.Rank.repPair_injective
---

# Squarefree representatives of rational square classes

Every nonzero integer, and every nonzero rational number, has the square class of a squarefree
integer (signs allowed); so every class in $\mathbb Q^\times/\mathbb Q^{\times2}$ is the class of a
squarefree integer. For a square class $c$ fix such an integer $r(c)$, its *squarefree
representative*. Then $r(c)$ is squarefree and nonzero, its square class is $c$, and
$c\mapsto r(c)$ is injective. If $c$ is the class of a rational $q\ne0$, then $r(c)\equiv q$, that is
$r(c)=qs^2$ for some nonzero $s\in\mathbb Q$.
Hence the pair map $(\alpha,\beta)\mapsto(r(\alpha),r(\beta))$ is injective on
$(\mathbb Q^\times/\mathbb Q^{\times2})^2$.

**Proof sketch.** Write $|n|=b^2a$ with $a$ squarefree and $b>0$; then
$n=\operatorname{sign}(n)\,a\cdot b^2$, and $\operatorname{sign}(n)\,a$ is squarefree. A nonzero
rational $q$ with numerator $u$ and denominator $v$ is $(uv)\cdot(1/v)^2$, so it has the class of
the nonzero integer $uv$. Injectivity holds because $r(c)$ determines its class $c$.

## Depends on

- [Two-isogenies and the Kummer map](../model/descent/kummer-map.md)
- [Square classes in a field](square-classes.md)

## Sources

- [RK9](../../sources/pole-completeness-locators.md#rk9)
