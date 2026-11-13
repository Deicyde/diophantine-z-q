---
article_id: af_9b28fae8f795e65f3a05f542
declaration: def
origin: background
statement: formalized
lean: ZInQ.Contrib.HeckeFE.gaussFEPair, ZInQ.Contrib.HeckeFE.isStrong_gaussFEPair, ZInQ.Contrib.HeckeFE.gaussLambda, ZInQ.Contrib.HeckeFE.gaussLambdaDual, ZInQ.Contrib.HeckeFE.mellinConvergent_gaussTheta, ZInQ.Contrib.HeckeFE.differentiable_gaussLambda, ZInQ.Contrib.HeckeFE.differentiable_gaussLambdaDual, ZInQ.Contrib.HeckeFE.gaussLambda_two_sub
---

# The completed lattice functions and their functional equation

For $a,b\in\mathbb R/\mathbb Z$ let $\theta_{a,b}$ and $\theta^*_{a,b}$ be the
[theta kernels](theta-kernels.md). The *completed lattice function* and its dual are the Mellin
transforms
$$\Lambda_{a,b}(s)=\int_0^\infty\theta_{a,b}(x)\,x^{s-1}\,dx,\qquad
\Lambda^*_{a,b}(s)=\int_0^\infty\theta^*_{a,b}(x)\,x^{s-1}\,dx\qquad(s\in\mathbb C),$$
each integral read as $0$ where the integrand is not integrable.

1. The pair $(\theta_{a,b},\theta^*_{a,b})$ is a functional-equation pair of weight $2$ and sign $1$
   with constant terms $0$: both functions are locally integrable on $(0,\infty)$,
   $\theta_{a,b}(1/x)=x^2\theta^*_{a,b}(x)$ for $x>0$, and both are $O(x^r)$ as $x\to\infty$ for
   every real $r$.
2. For every $s\in\mathbb C$ the integral defining $\Lambda_{a,b}(s)$ converges absolutely.
3. $\Lambda_{a,b}$ and $\Lambda^*_{a,b}$ are entire.
4. For every $s\in\mathbb C$, $\Lambda_{a,b}(2-s)=\Lambda^*_{a,b}(s)$.

**Proof sketch.** (1) The transformation law and the growth bounds are
[theta kernels](theta-kernels.md) (2) and (5); continuity on $(0,\infty)$, theta kernels (6), gives
local integrability.

(2)–(4) This is the general theorem on such pairs (Hecke's argument): for a pair $(f,g)$ with
$f(1/x)=\varepsilon x^kg(x)$, both decaying faster than every power of $x$ at infinity and with
constant terms $0$, the Mellin integrals of $f$ and $g$ converge for every $s$, define entire
functions, and satisfy $\Lambda_f(k-s)=\varepsilon\Lambda_g(s)$. One splits the integral at $x=1$
and moves the part over $(0,1)$ to $(1,\infty)$ with the transformation law. Here $k=2$ and
$\varepsilon=1$.

## Depends on

- [The weight-two theta kernels of a shifted lattice](theta-kernels.md)

## Sources

- [Theta series and the method of Hecke](../../../../../sources/hecke-locators.md#theta-series-and-the-method-of-hecke)
