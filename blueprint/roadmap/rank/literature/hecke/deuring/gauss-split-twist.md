---
article_id: af_8cdce5281bc30c5c15ab28b2
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.card_cd_affine_eq, ZInQ.Contrib.HeckeFE.sum_quadraticChar_twist, ZInQ.Contrib.HeckeFE.gaussSplit_of_one, ZInQ.Contrib.HeckeFE.gaussSplit_one_of_pointCount
---

# The split primes for $C_d$ from the curve $y^2=x^3-x$

For a prime $p$, $\left(\frac{\cdot}{p}\right)$ is the quadratic character of $\mathbb F_p$ (with
value $0$ at $0$). *Gauss's theorem at the split primes* for $d$ is as in
[Deuring's identity from the Euler product](deuring-of-euler-product.md), and
[Gauss's point count](../gauss/gauss-point-count.md) is the statement about $y^2=x^3-x$ named there.

1. If $p\ne2$ is prime and $d$ a natural number, then
   $\#\{(x,y)\in\mathbb F_p^2:y^2=x^3-d^2x\}=p+\sum_{x\in\mathbb F_p}\left(\frac{x^3-d^2x}p\right)$.
2. If $p$ is prime and $p\nmid d$, then
   $\sum_x\left(\frac{x^3-d^2x}p\right)=\left(\frac dp\right)\sum_x\left(\frac{x^3-x}p\right)$.
3. If $d\equiv1\pmod4$ is squarefree and Gauss's theorem at the split primes holds for $d=1$, then
   it holds for $d$.
4. Gauss's point count implies Gauss's theorem at the split primes for $d=1$.

**Proof sketch.** (1) A value $x$ contributes $1+\left(\frac{x^3-d^2x}p\right)$ solutions $y$.

(2) Substitute $x=dt$: $(dt)^3-d^2(dt)=d^2\cdot d(t^3-t)$, and $\left(\frac{d^2}p\right)=1$.

(3) Let $p\equiv1\pmod4$ be prime with $p\nmid d$; then $p\nmid2d$ and $p\nmid2$. By
[Deuring's identity for $C_d$](deuring-identity.md),
[the coefficients at primes](../../l-function-cd/prime-coefficients.md) and (1),
$c_d(p)=-\sum_x\left(\frac{x^3-d^2x}p\right)$ and $c_1(p)=-\sum_x\left(\frac{x^3-x}p\right)$, so
$c_d(p)=\left(\frac dp\right)c_1(p)$ by (2). Since $p\equiv1\pmod4$ and $d$ is odd, quadratic
reciprocity gives $\left(\frac dp\right)=\left(\frac pd\right)$. On the other side
$\lambda_d(p)=\left(\frac pd\right)\lambda_1(p)$
([Hecke coefficients](../gaussian/hecke-coefficients.md) (2)), and $c_1(p)=\lambda_1(p)$ by the
hypothesis.

(4) For a prime $p\equiv1\pmod4$, $c_1(p)$ is $p$ minus the number of solutions of $y^2=x^3-x$
(the coefficients at primes), and $\lambda_1(p)=\frac14\sum_{\alpha\in A_p}u(\alpha)\alpha$ since
$\left(\frac{\cdot}1\right)=1$; Gauss's point count says these are equal.

## Depends on

- [Deuring's identity from the Euler product and the split primes](deuring-of-euler-product.md)
- [Gauss's point count on $y^2=x^3-x$](../gauss/gauss-point-count.md)

## Proof depends on

- [Deuring's identity for $C_d$](deuring-identity.md)
- [The coefficients of $L(C_d,s)$ at primes as point counts](../../l-function-cd/prime-coefficients.md)
- [The coefficients of the Hecke L-series $L(\psi_d,s)$](../gaussian/hecke-coefficients.md)

## Sources

- [The point count of Gauss](../../../../../sources/hecke-locators.md#the-point-count-of-gauss)
- [Deuring and the Hecke character](../../../../../sources/hecke-locators.md#deuring-and-the-hecke-character)
