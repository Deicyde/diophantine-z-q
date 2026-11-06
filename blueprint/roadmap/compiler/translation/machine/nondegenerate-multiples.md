---
article_id: af_13158e82bc20414894926e9b
declaration: lemma
origin: bridged
---

# Nonzero multiples of the generator are nondegenerate

For every integer $m\ne0$ the point $[m]P_0$ is nondegenerate: it is affine,
$[m]P_0=(x,y)$, with $x\ne0$ and $y\ne0$. Hence $z([m]P_0)=-x/y$ is defined and nonzero. In
particular, condition 1 of the precision predicate implies its condition 2, and
$\epsilon_l>0$.

**Proof sketch.** The torsion of $E(K_0)$ is $E(K_0)[2]=\{O,(0,0),(d,0),(-d,0)\}$, and $P_0$ is
not in it because its ordinate $(-123720+87483s)/32$ is nonzero; so $P_0$ has infinite order
and $[m]P_0\ne O$. If $y=0$, or if $x=0$ (which forces $y^2=x^3-d^2x=0$), then $[m]P_0$ is a
two-torsion point, so $[2m]P_0=O$ with $2m\ne0$, a contradiction. For condition 1: $a,l\ge1$
and $j=na$ with $n\ne0$ (as $0\in\mathcal C$) give $l,a,j\ne0$. Finally $z([l]P_0)\ne0$ gives
$(u_l,v_l)\ne(0,0)$. No Mordell-Weil input is used.

## Depends on

- [The precision predicate](precision-predicate.md)
- [The point $P_0$](../../../model/field/generator-point.md)

## Proof depends on

- [The torsion of $E(K_0)$ is the full two-torsion](../../../model/descent/torsion.md)

## Sources

- [Section 10 opening](../../../../sources/compiler-translation-locators.md#section-10-opening)
