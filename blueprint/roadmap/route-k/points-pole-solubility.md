---
article_id: af_224e746ae9bc67ee0a7c8e67
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.RouteK.poleSoluble_of_points, ZInQ.RouteK.exists_multiplier_bits
---

# Points on two congruent number curves give pole solubility

Let $B$ be a nonzero rational, $m\ne B$ a signed divisor of $2730$, $\beta=\mathrm{sqf}(mB)$,
$\theta=\mathrm{sqf}(m(m-B))$, and $N$ a nonzero rational. Suppose that
$C_N:y^2=x^3-N^2x$ has a rational point $(x_1,y_1)$ with $x_1\ne0$ and $x_1/\beta$ a square,
and that $C_{N\theta}:y^2=x^3-(N\theta)^2x$ has a rational point $(x_2,y_2)$ with $x_2\ne0$ and
$x_2/\beta$ a square. Then $\Phi(B)$ holds: the pole polynomial has a rational zero with
input $B$.

**Proof sketch.** Every signed divisor of $2730$ is the multiplier
$(1-2b_0)(1+b_1)(1+2b_2)(1+4b_3)(1+6b_4)(1+12b_5)$ for some bits $b_i\in\{0,1\}$: the sign gives
$b_0$, and $|m|=\gcd(|m|,2)\gcd(|m|,3)\gcd(|m|,5)\gcd(|m|,7)\gcd(|m|,13)$ gives the others. Then
$A=mB=\beta t^2$ and $H=A(A-B^2)=B^2m(m-B)=\theta h^2$ with $t,h\ne0$. Write
$x_1=\beta s^2$, $x_2=\beta s'^2$. Scaling the first point by $\lambda=t/s$ gives the point
$(A,\lambda^3y_1)$ on $C_e$ with $e=N\lambda^2$, so $r_1=\lambda^3y_1$ satisfies
$r_1^2=A(A-e)(A+e)$. Then $eH=N\theta(\lambda h)^2$, and scaling the second point by $\lambda h$
gives $(Az^2,(\lambda h)^3y_2)$ on $C_{eH}$ with $z=s'h/s$; so $r_2=(\lambda h)^3y_2/z$ satisfies
$(zr_2)^2=Az^2(Az^2-eH)(Az^2+eH)$, that is $r_2^2=T_2$. Finally $w=(eHz)^{-1}$, which exists
because $e,H,z\ne0$. Every summand of the pole polynomial vanishes.

## Depends on

- [Admissible inputs, the squarefree part, $\beta$ and $\theta$](squarefree-part.md)
- [Pole completeness](../main/pole-completeness.md)

## Sources

- [Points and the pole polynomial](../../sources/route-k-locators.md#points-and-the-pole-polynomial)
