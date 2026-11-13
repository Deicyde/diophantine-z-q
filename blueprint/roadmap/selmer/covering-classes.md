---
article_id: af_c3fad4cb3e12a347a2c1f694
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.loc_torsion, ZInQ.RouteK.Selmer.loc_mul_sq_iff, ZInQ.RouteK.Selmer.loc_congr_sq, ZInQ.RouteK.Selmer.loc_of_sqEq_torsion
---

# Square classes and torsion witnesses of a covering

Let $K$ be a field with $2\ne0$ and $d,a,b\in K$, $d,a,b\ne0$.

1. *(Inv)* The x-form of $D_{a,b}$ depends only on the classes of $a$ and $b$ modulo nonzero
   squares: if $a\equiv a'$ and $b\equiv b'$, it holds for $(a,b)$ if and only if it holds for
   $(a',b')$.
2. *(Tor)* If $x/a$, $(x-d)/b$ and $(x+d)/(ab)$ are squares, then either $x=0$, $a\equiv-1$,
   $b\equiv-d$; or $x=d$, $a\equiv d$, $b\equiv2$; or $x=-d$, $a\equiv-d$, $b\equiv-2d$; or
   $x$, $x-d$, $x+d$ are all nonzero, $x\equiv a$, $x-d\equiv b$, $x+d\equiv ab$ and
   $x(x-d)(x+d)$ is a square.
3. For $i,j\in\{0,1\}$, if $a\equiv d^i(-1)^j$ and $b\equiv2^i(-d)^j$ (one of the four torsion
   classes $(1,1)$, $(-1,-d)$, $(d,2)$, $(-d,-2d)$), the x-form of $D_{a,b}$ holds.

**Proof sketch.** (1) Divide the three squares by $s^2$, $t^2$ and $(st)^2$; the witness $x$
is the same. (2) If $x=0$ then $-d/b$ and $d/(ab)$ are nonzero squares, so $b\equiv-d$ and
$a\equiv-1$; the cases $x=\pm d$ are alike; otherwise the three quotients are nonzero squares
and their product is $x(x-d)(x+d)/(ab)^2$. (3) By (1) take the class representatives; the
witnesses are the first alternative for $(1,1)$ and $x=0$, $d$, $-d$ for the others.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)

## Sources

- [Coverings](../../sources/selmer-locators.md#coverings)
