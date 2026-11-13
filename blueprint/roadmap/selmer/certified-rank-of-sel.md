---
article_id: af_a4dc298941ad1a7d33450efe
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.certifiedRank_of_certifiedRankSel, ZInQ.RouteK.Selmer.certifiedRank_of_sel, ZInQ.RouteK.Selmer.exists_point_of_loc, ZInQ.RouteK.Selmer.classInt_natClass, ZInQ.RouteK.Selmer.eq_one_of_squarefree_of_isSquare
---

# The certified rank hypothesis from its Selmer form

The hypothesis CR₃^Sel implies the certified rank hypothesis CR₃.

**Proof sketch.** Let $d\equiv5\pmod8$ be squarefree, $a$ a squarefree divisor of $d$ with
$|a|\equiv7\pmod8$, and suppose $\Sigma(\mathcal C_d)$ has $8$ solutions, one of them $\sigma$ with
first coordinate the class of $a$.

1. By Proposition 0 and the injectivity of $\sigma\mapsto(a(\sigma),b(\sigma))$, $\mathrm{Sel}_2(C_d)$
   is the image of the solutions, so it has $8$ elements.
2. Since $a$ is a squarefree divisor of $d$, its class gives $a(\sigma)=a$; so
   $(a,b(\sigma))\in\mathrm{Sel}_2(C_d)$ with $|a|\equiv7\pmod8$.
3. CR₃^Sel gives the x-form of $D_{a,b(\sigma)}$ over $\mathbb Q$. The first alternative would make
   the squarefree $a$ a square, so $a=1$, against $|a|\equiv7$. So there is $x$ with $x=ar_1^2$,
   $x-d=b r_2^2$, $x+d=abr_3^2$.
4. $x\ne0$: otherwise $-d/b$ and $d/(ab)$ are nonzero squares, which forces $a=-1$.
5. $y=abr_1r_2r_3$ satisfies $y^2=x^3-d^2x$, and $x/a=r_1^2$ is a square.

This is the conclusion of CR₃.

## Depends on

- [The certified rank hypothesis in Selmer form](certified-rank-sel.md)
- [The certified rank hypothesis](../main/certified-rank.md)

## Proof depends on

- [Proposition 0](proposition-0.md)
- [The 2-Selmer group of a congruent number curve](selmer-group.md)

## Sources

- [The hypothesis in the literature's form](../../sources/selmer-locators.md#the-hypothesis-in-the-literatures-form)
