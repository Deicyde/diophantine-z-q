---
article_id: af_5a63633a89df04f85427aa08
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.cov_iff_loc
---

# The x-form of a covering

Let $K$ be a field and $d,a,b\in K$ with $a,b\ne0$. Then the 2-covering $D_{a,b}$ of $C_d$ is
soluble over $K$ if and only if its x-form holds: $a$ and $b$ are squares, or some $x\in K$ makes
$x/a$, $(x-d)/b$ and $(x+d)/(ab)$ squares.

**Proof sketch.** Let $(z_1,z_2,z_3,w)$ be a point. If $w=0$, then $az_1^2=bz_2^2$ and
$z_1^2=bz_3^2$; here $z_1\ne0$, since otherwise every coordinate vanishes, so $z_3\ne0$,
$b=(z_1/z_3)^2$ and $a=(z_2/z_3)^2$. If $w\ne0$, put $x=a(z_1/w)^2$; then $(x-d)/b=(z_2/w)^2$ and
$(x+d)/(ab)=(z_3/w)^2$. Conversely, if $a=s^2$ and $b=t^2$ then $(1/s,1/t,1/(st),0)$ is a point,
and if $x/a=r_1^2$, $(x-d)/b=r_2^2$, $(x+d)/(ab)=r_3^2$ then $(r_1,r_2,r_3,1)$ is a point, because
$ar_1^2-br_2^2=x-(x-d)$ and $ar_1^2-abr_3^2=x-(x+d)$.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)

## Sources

- [Coverings](../../sources/selmer-locators.md#coverings)
