---
article_id: af_65f8beac284f0f8c7cd045d4
declaration: instance
origin: cited
statement: formalized
lean: ZInQ.Zs.isPrincipalIdealRing, ZInQ.Zs.uniqueFactorizationMonoid
---

# $\mathbb Z[\sqrt2]$ is a principal ideal domain

The ring $\mathbb Z[s]$ is a principal ideal domain (the ring of integers of $K_0$ has class
number one). Consequently it is a unique factorization domain with fraction field $K_0$:
every $x\in K_0^\times$ is $x=u\prod_\pi\pi^{v_\pi(x)}$ with $u\in\mathbb Z[s]^\times$, $\pi$
running over a set of representatives of the prime elements up to units, and integers
$v_\pi(x)$, almost all zero, uniquely determined by $x$. The valuations satisfy
$v_\pi(xy)=v_\pi(x)+v_\pi(y)$ and $v_\pi(x+y)\ge\min(v_\pi(x),v_\pi(y))$, with equality when the
two valuations differ.

**Proof sketch.** The manuscript's route: $K_0$ has discriminant $8$ and the Minkowski bound
is $\frac{2!}{2^2}\sqrt8=\sqrt2<2$, so every ideal class contains an integral ideal of norm
$1$, i.e. the unit ideal. An elementary route better suited to formalization: $\mathbb Z[s]$
is Euclidean for $|\operatorname N|$. Given $a,b\in\mathbb Z[s]$, $b\ne0$, write
$a/b=u+vs$ and let $q=\lfloor u\rceil+\lfloor v\rceil s$ with nearest integers; then
$|\operatorname N(a/b-q)|\le\max(\tfrac14,\tfrac24)<1$, so $a=qb+\rho$ with
$|\operatorname N(\rho)|<|\operatorname N(b)|$. Unique factorization and the valuation rules
follow from the principal ideal property in the usual way.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](quadratic-field.md)

## Proof depends on

- [Pair arithmetic represents the quadratic field](../../syntax/field-pair-arithmetic.md)

## Sources

- [Class number and units](../../../sources/model-locators.md#class-number-and-units)
