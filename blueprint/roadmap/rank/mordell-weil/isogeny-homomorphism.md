---
article_id: af_7933aa91c2e06acea8d9522f
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank.mwPhi_add, ZInQ.RouteK.Rank.mwPhiHom, ZInQ.RouteK.Rank.mwPhiHom_apply, ZInQ.RouteK.Rank.mwPhi_neg, ZInQ.RouteK.Rank.mwAdd_tZero_some, ZInQ.RouteK.Rank.mwTZero_add_tZero, ZInQ.RouteK.Rank.mwNeg_tZero, ZInQ.RouteK.Rank.mwPhi_tZero, ZInQ.RouteK.Rank.mwPhi_add_tZero
---

# The two-isogeny is a homomorphism

Let $K$ be a field of characteristic different from $2$ and $b\in K^\times$. The two-isogeny
$\varphi_b:E_b(K)\to E_{-4b}(K)$ is a group homomorphism:
$$\varphi_b(P+Q)=\varphi_b(P)+\varphi_b(Q)\qquad(P,Q\in E_b(K)).$$

Along the way, with $T=(0,0)$:

- $\varphi_b(-P)=-\varphi_b(P)$ for every $P$;
- $T+T=O$, hence $-T=T$, and $\varphi_b(T)=O$;
- for an affine point $(x,y)$ with $x\ne0$, $(b/x,\,-by/x^2)$ lies on $E_b$ and
  $(x,y)+T=(b/x,\,-by/x^2)$; and $\varphi_b(P+T)=\varphi_b(P)$ for every $P$.

**Proof sketch.** (Silverman–Tate, Section III.4.) The first three items are direct
computations; for example, $\varphi_b(b/x,-by/x^2)$ has coordinates $y^2/x^2$ and
$y(b-x^2)/x^2$.

*Additivity.* If $P$ or $Q$ is $O$ or $T$, use $\varphi_b(P+T)=\varphi_b(P)$ and
$\varphi_b(T)=O$. If $P+Q=O$, use $\varphi_b(-P)=-\varphi_b(P)$. If $P+Q=T$, then $Q=-P+T$ and
$\varphi_b(Q)=-\varphi_b(P)$. Otherwise $P=(x_1,y_1)$ and $Q=(x_2,y_2)$ with $x_1,x_2\ne0$. If
$x_1=x_2$, then $Q=P$ (the doubling case) or $Q=-P$ (excluded). If $x_1x_2=b$, then $P+T$ has abscissa
$b/x_1=x_2$, so $Q=\pm(P+T)$. If $Q=P+T$, then
$\varphi_b(P+Q)=\varphi_b(2P+T)=\varphi_b(2P)=2\varphi_b(P)=\varphi_b(P)+\varphi_b(Q)$; the doubling
hypotheses hold because $P+Q\notin\{O,T\}$. If $Q=-(P+T)$, then $P+Q=T$, which is excluded. In
the remaining case $P+Q\ne T$ has nonzero abscissa, and the chord case applies.

## Depends on

- [Two-isogenies and the Kummer map](../../model/descent/kummer-map.md)

## Proof depends on

- [The two-isogeny on chord sums and doubles](isogeny-chord-sums.md)

## Sources

- [Silverman-Tate](../../../sources/rank-locators.md#silverman-tate)
- [Silverman: descent and heights](../../../sources/rank-locators.md#silverman-descent-and-heights)
