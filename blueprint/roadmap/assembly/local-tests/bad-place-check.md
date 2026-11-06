---
article_id: af_2aee439afbca4d4c51eb7b86
declaration: lemma
origin: bridged
---

# The generator at the two bad primes

1. $v_s\bigl(x(P_0)\bigr)=-6$; hence $P_0\in E_3(s)$.
2. $[7]P_0$ is affine and $v_d\bigl(x([7]P_0)\bigr)=-2$; hence $[7]P_0\in E_1(d)$.

Both are closed finite computations: (1) concerns $x(P_0)=(1641-1160s)/8$, and (2) the
abscissa of $[7]P_0$, an explicit element of $K_0$ whose two rational components have
numerators and denominators of about $165$ decimal digits, computed by a few chord-and-tangent
steps in $K_0$.

**Proof sketch.** (1) $v_s(8)=6$, and $v_s(1641-1160s)=\min(2v_2(1641),\,2v_2(1160)+1)=\min(0,7)=0$.
(2) Compute $[7]P_0$ exactly in $K_0$ (for instance $[2]P_0$, $[3]P_0=[2]P_0+P_0$, $[6]P_0$,
$[7]P_0$); write its abscissa as $(\alpha+\beta s)/\gamma$ with $\alpha,\beta,\gamma\in\mathbb Z$, $\gamma>0$, and read off
the valuation at $d$ from $v_7(\gamma)$ (as $v_d(7)=1$) and the number of times $d$ divides
$\alpha+\beta s$ in $\mathbb Z[s]$, testing divisibility by $d$ through the residue map
$a_0+a_1s\mapsto a_0+3a_1\bmod7$. Geometrically, $P_0$ reduces at $d$ to the nonsingular point
$(2,6)$ of the cuspidal cubic $y^2=x^3$ over $\mathbb F_7$, whose nonsingular points form a group
of order $7$; the computation certifies the consequence directly.

## Depends on

- [Formal neighbourhoods of the identity](formal-group.md)
- [The point $P_0$](../../model/field/generator-point.md)
- [The primes $(s)$ and $(d)$ of $\mathbb Z[\sqrt2]$](../../model/field/special-primes.md)

## Sources

- [Section 12 size](../../../sources/assembly-locators.md#section-12-size)
- [Lemma 11.2](../../../sources/assembly-locators.md#lemma-112)
