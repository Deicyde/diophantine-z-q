---
article_id: af_ac5e273163c0c47b18355894
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.RouteK.Selmer.Sel2, ZInQ.RouteK.Selmer.classInt, ZInQ.RouteK.Selmer.selPair, ZInQ.RouteK.Selmer.selPair_injective, ZInQ.RouteK.Selmer.squarefree_classInt
---

# The 2-Selmer group of a congruent number curve

For a natural number $d$, the *2-Selmer group* $\mathrm{Sel}_2(C_d)$ is the set of pairs $(a,b)$ of
squarefree integers (signs allowed) such that the 2-covering $D_{a,b}$ of $C_d:y^2=x^3-d^2x$ is
soluble (in its x-form) over $\mathbb R$ and over $\mathbb Q_p$ for every prime $p$, $p=2$ included.

For odd $d$ and unknowns $\sigma=(a_0,a_1,b_0,b_1,u,v)$ of the Selmer system on the primes of $d$,
put
$$a(\sigma)=(-1)^{a_0}2^{a_1}\prod_{p\mid d}p^{u_p},\qquad b(\sigma)=(-1)^{b_0}2^{b_1}\prod_{p\mid d}p^{v_p}.$$
These integers are squarefree, and $\sigma\mapsto(a(\sigma),b(\sigma))$ is injective: the sign, $v_2$
and the $v_p$ recover the unknowns.

By the Kummer-map lemma over each completion, $(a,b)\in\mathrm{Sel}_2(C_d)$ says that the class of
$(a,b)$ in $(\mathbb Q^*/\mathbb Q^{*2})^2$ lies locally everywhere in the image of the Kummer map.
With the standard identification of $H^1(\mathbb Q,C_d[2])$ with $(\mathbb Q^*/\mathbb Q^{*2})^2$, under
which the connecting map of the complete 2-descent is the Kummer map (Silverman, Proposition
X.1.4), and with each square class written by its squarefree integer representative, this is the
textbook 2-Selmer group. That identification is used to read the definition, not formalized.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)
- [The Selmer system of a configuration](../route-k/selmer-system.md)

## Sources

- [The Selmer group](../../sources/selmer-locators.md#the-selmer-group)
- [Silverman](../../sources/selmer-locators.md#silverman)
