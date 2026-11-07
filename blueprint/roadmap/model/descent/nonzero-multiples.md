---
article_id: af_27935f7d660df017638fbd70
declaration: lemma
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.genP0_not_isOfFinAddOrder, ZInQ.iota_injective, ZInQ.zsmul_genP0_affine, ZInQ.zsmul_genP0_affine_z_w, ZInQ.iota_zero_coord_iff
---

# Nonzero multiples of the generator

The point $P_0$ has infinite order. Consequently, for every nonzero $m\in\mathbb Z$ the point
$[m]P_0$ is affine, its abscissa and ordinate are nonzero, and $z([m]P_0)=-x/y$ and
$w([m]P_0)=1/x$ are nonzero elements of $K_0$. The map $m\mapsto\iota(m)$ is injective, and the
first coordinate of $\iota(m)$ is $0$ exactly when $m\ne0$.

No hypothesis is needed: this uses only the torsion subgroup of $E(K_0)$, not the
Mordell–Weil theorem.

**Proof sketch.** The torsion subgroup of $E(K_0)$ is $E(K_0)[2]$, whose affine points have
ordinate $0$. The ordinate of $P_0$ is $(-123720+87483s)/32\ne0$, so $P_0$ is not torsion,
and $[m]P_0=[m']P_0$ forces $m=m'$. For $m\ne0$, $[m]P_0$ is not torsion either, so it is
neither $O$ nor a point with $y=0$; and $x=0$ forces $y^2=0$ on $E$. Hence $x,y\ne0$, so
$z=-x/y\ne0$ and $w=1/x\ne0$. Injectivity of $\iota$ follows from injectivity of codes, and
the first code coordinate is $0$ exactly for affine points.

## Depends on

- [Point codes](../point-codes.md)

## Proof depends on

- [The torsion of $E(K_0)$ is the full two-torsion](torsion.md)
- [The point $P_0$](../field/generator-point.md)
- [Elementary properties of codes](../field/point-code-properties.md)

## Sources

- [Section 3 codes](../../../sources/assembly-locators.md#section-3-codes)
- [Section 11.2 six local tests](../../../sources/assembly-locators.md#section-112-six-local-tests)
