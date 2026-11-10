---
article_id: af_5a85853b22f77ca5668151d7
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.loc_iff_kummer, ZInQ.RouteK.Selmer.kummer
---

# Coverings and the Kummer map

Let $K$ be a field with $2\ne0$ and $d\ne0$ in $K$. The *Kummer map* of the complete 2-descent
on $C_d:y^2=x^3-d^2x$ sends the point at infinity to $(1,1)$, the 2-torsion points $(0,0)$,
$(d,0)$, $(-d,0)$ to $(-1,-d)$, $(d,2)$, $(-d,-2d)$, and every other point $(x,y)$ to
$(x,x-d)$; its values are read modulo squares. Then for $a,b\ne0$ the x-form of $D_{a,b}$ holds
if and only if there is a point $P\in C_d(K)$ whose Kummer image $(\alpha,\beta)$ has
$a\equiv\alpha$ and $b\equiv\beta$.

**Proof sketch.** (⇐) By the invariance under squares it suffices to treat the image of $P$
itself: the point at infinity and the torsion points give the torsion classes; for
$P=(x,y)$ with $x\notin\{0,\pm d\}$ the witness is $x$, since $x/x=1$, $(x-d)/(x-d)=1$ and
$(x+d)/(x(x-d))=(y/(x(x-d)))^2$. (⇒) If $a,b$ are squares take the point at infinity.
Otherwise, with $x=ar_1^2$, $x-d=br_2^2$, $x+d=abr_3^2$, the point $(x,abr_1r_2r_3)$ lies on
$C_d$; by the torsion analysis, either $x\in\{0,\pm d\}$ and $(a,b)$ is the image of the
corresponding 2-torsion point, or $(a,b)\equiv(x,x-d)$.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)

## Proof depends on

- [Square classes and torsion witnesses of a covering](covering-classes.md)

## Sources

- [The Kummer map](../../sources/selmer-locators.md#the-kummer-map)
