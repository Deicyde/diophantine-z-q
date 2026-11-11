---
article_id: af_b041d5b5a815ad7572cd070e
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.sel_of_selmerCertified
---

# The 2-Selmer group of a certified curve

Let $d$ be a squarefree natural number with $d\equiv5\pmod8$, and let $a$ be a squarefree integer
dividing $d$ such that $(d,a)$ carries a Selmer certificate: the system $\Sigma(\mathcal C_d)$ has
exactly $8$ solutions, and one of them has first coordinate the class of $a$. Then
$|\mathrm{Sel}_2(C_d)|=8$, and $(a,b)\in\mathrm{Sel}_2(C_d)$ for some integer $b$.

**Proof sketch.** By Proposition 0, unknowns $\sigma$ solve $\Sigma(\mathcal C_d)$ if and only if
$(a(\sigma),b(\sigma))\in\mathrm{Sel}_2(C_d)$, and every element of $\mathrm{Sel}_2(C_d)$ has this
form. So $\mathrm{Sel}_2(C_d)$ is the image of the solution set under
$\sigma\mapsto(a(\sigma),b(\sigma))$. This map is injective for odd $d$, so
$|\mathrm{Sel}_2(C_d)|=8$. Let $\sigma$ be the solution whose first coordinate is the class of $a$,
that is $a_0=[a<0]$, $a_1=0$ and $u_p=[p\mid a]$. Since $a$ is a squarefree divisor of $d$,
$a(\sigma)=(-1)^{[a<0]}\prod_{p\mid a}p=a$, so $(a,b(\sigma))\in\mathrm{Sel}_2(C_d)$. These are
steps 1 and 2 of the proof of CR₃ from its Selmer form, at a single certificate.

## Depends on

- [The configuration of an odd number and Selmer certificates](../../route-k/prime-configuration.md)
- [The 2-Selmer group of a congruent number curve](../../selmer/selmer-group.md)

## Proof depends on

- [Proposition 0](../../selmer/proposition-0.md)
- [The certified rank hypothesis from its Selmer form](../../selmer/certified-rank-of-sel.md)

## Sources

- [Positive rank on the two curves](../../../sources/rank-locators.md#positive-rank-on-the-two-curves)
- [Proposition 0](../../../sources/selmer-locators.md#proposition-0)
