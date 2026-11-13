---
article_id: af_b99001b3797d8c162877e025
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.red_add, ZInQ.eq_zero_of_red_eq_zero
---

# Reduction is injective on prime-to-$p$ torsion

Let $p$ be an odd prime and $r\in\mathbb Z$ with $r^2\equiv2\pmod p$. Then
$\rho:\mathbb Z[s]\to\mathbb F_p$, $a+bs\mapsto a+br\bmod p$, is a surjective ring homomorphism
with kernel the prime $\mathfrak p=(p,s-r)$; it extends to the local ring
$\mathbb Z[s]_{\mathfrak p}\subset K_0$. Let $A\in\mathbb Z[s]$ with $\rho(A)\ne0$, let
$W:y^2=x^3+Ax$ over $K_0$ and $\widetilde W:y^2=x^3+\rho(A)x$ over $\mathbb F_p$ (an elliptic curve,
since $p$ is odd and $\rho(A)\ne0$). Define $\operatorname{red}:W(K_0)\to\widetilde W(\mathbb F_p)$
by $\operatorname{red}(O)=O$, $\operatorname{red}(x,y)=(\rho(x),\rho(y))$ if $x\in\mathbb Z[s]_{\mathfrak p}$,
and $\operatorname{red}(x,y)=O$ otherwise. Then:

1. $\operatorname{red}$ is a group homomorphism;
2. if $T\in W(K_0)$ has finite order prime to $p$ and $\operatorname{red}(T)=O$, then $T=O$.
   Hence $\operatorname{red}$ is injective on every finite subgroup of $W(K_0)$ of order prime
   to $p$, and the order of such a subgroup divides $\#\widetilde W(\mathbb F_p)$.

(If $x\in\mathbb Z[s]_{\mathfrak p}$ then $y\in\mathbb Z[s]_{\mathfrak p}$ too, because
$y^2=x^3+Ax$ is integral there.)

**Proof sketch.** This is reduction modulo a prime of good reduction (Silverman, Proposition
VII.2.1 and Proposition VII.3.1(b)), applied after embedding $K_0$ in its completion at
$\mathfrak p$, which is $\mathbb Q_p$ because $\mathfrak p$ has residue degree one. Part 1 holds
because the group law is given by polynomial formulas in projective coordinates that reduce
to those of $\widetilde W$. For part 2, the kernel of reduction is the group of points with
$v_{\mathfrak p}(x)<0$; on it $z=-x/y$ defines an isomorphism with the formal group
$\widehat W(\mathfrak p)$, which has no nontrivial torsion of order prime to $p$ because
multiplication by an integer prime to $p$ is invertible on it.

## Depends on

- [The field $K_0=\mathbb Q(\sqrt2)$](../field/quadratic-field.md)

## Sources

- [Torsion bound](../../../sources/model-locators.md#torsion-bound)
- [Silverman](../../../sources/model-locators.md#silverman)
