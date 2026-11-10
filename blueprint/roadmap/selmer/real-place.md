---
article_id: af_9515e2649a11e19dea7ae106
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.loc_real_iff, ZInQ.RouteK.Selmer.loc_real_iff_int
---

# Local solubility at the real place

Let $d>0$ and $a,b\ne0$ be real numbers. Then the covering $D_{a,b}$ of $C_d$ is soluble over
$\mathbb R$ (in its x-form) if and only if $a$ and $b$ have the same sign. In particular this holds
for integers $d>0$ and $a,b\ne0$.

**Proof sketch.** If $a,b>0$ take $x=d$; if $a,b<0$ take $x=0$. If $a>0>b$, a witness would have
$x\ge0$, $x-d\le0$ and $x+d\le0$, impossible; if $a<0<b$, it would have $x\le0$ and $x-d\ge0$,
impossible as $d>0$. The first alternative forces $a,b>0$.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)

## Sources

- [The real place](../../sources/selmer-locators.md#the-real-place)
