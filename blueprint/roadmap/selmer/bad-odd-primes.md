---
article_id: af_dfc6b5a5ee0db064fb811a5b
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Selmer.loc_padic_dvd_iff, ZInQ.RouteK.Selmer.padic_norm_natCast_of_squarefree, ZInQ.RouteK.Selmer.padic_norm_ne_zpow_odd
---

# Local solubility at odd primes dividing d

Let $p$ be an odd prime, $d$ a squarefree natural number divisible by $p$, and $a,b$ nonzero
integers. Then $D_{a,b}$ is soluble over $\mathbb Q_p$ (in its x-form) if and only if there are
$i,j\in\{0,1\}$ such that $ad^i(-1)^j$ and $b\,2^i(-d)^j$ are squares in $\mathbb Q_p$; that is,
$(a,b)$ is one of the four torsion classes $(1,1)$, $(d,2)$, $(-1,-d)$, $(-d,-2d)$.

**Proof sketch.** (⇐) The torsion classes are soluble. (⇒) After the torsion analysis, compare $|x|$
with $|d|=p^{-1}$. If $|x|>|d|$, (P) gives $x\pm d\equiv x$ and $(a,b)\equiv(1,1)$; if $|x|<|d|$,
$x-d\equiv-d$, $x+d\equiv d$ and $(a,b)\equiv(-1,-d)$. If $|x|=|d|$, write $x=dt$ with $t$ a unit: $t-1$
and $t+1$ are not both non-units (their difference is $2$) and not both units (then
$|x(x-d)(x+d)|=p^{-3}$ is not the norm of a square); $p\mid t-1$ gives $(d,2)$ and $p\mid t+1$
gives $(-d,-2d)$.

## Depends on

- [The 2-coverings of a congruent number curve](coverings.md)

## Proof depends on

- [Squares in the p-adic numbers](padic-squares.md)
- [Square classes and torsion witnesses of a covering](covering-classes.md)

## Sources

- [Odd primes dividing d](../../sources/selmer-locators.md#odd-primes-dividing-d)
