---
article_id: af_64589cdf0e4c6094b22e002e
declaration: def
origin: background
statement: formalized
lean: ZInQ.Contrib.HeckeFE.gaussTheta, ZInQ.Contrib.HeckeFE.gaussThetaDual, ZInQ.Contrib.HeckeFE.oddKernel_one_div, ZInQ.Contrib.HeckeFE.evenKernel_one_div, ZInQ.Contrib.HeckeFE.gaussTheta_one_div, ZInQ.Contrib.HeckeFE.isBigO_atTop_of_sub_const, ZInQ.Contrib.HeckeFE.evenKernel_isBigO_one, ZInQ.Contrib.HeckeFE.cosKernel_isBigO_one, ZInQ.Contrib.HeckeFE.prod_isBigO_rpow, ZInQ.Contrib.HeckeFE.gaussTheta_isBigO, ZInQ.Contrib.HeckeFE.gaussThetaDual_isBigO, ZInQ.Contrib.HeckeFE.continuousOn_gaussTheta, ZInQ.Contrib.HeckeFE.continuousOn_gaussThetaDual
---

# The weight-two theta kernels of a shifted lattice

For $a\in\mathbb R/\mathbb Z$ and real $x>0$ the four one-variable kernels are
$$E_a(x)=\sum_{n\in\mathbb Z}e^{-\pi(n+a)^2x},\qquad O_a(x)=\sum_{n\in\mathbb Z}(n+a)\,e^{-\pi(n+a)^2x},$$
$$C_a(x)=\sum_{n\in\mathbb Z}\cos(2\pi an)\,e^{-\pi n^2x},\qquad S_a(x)=\sum_{n\in\mathbb Z}n\sin(2\pi an)\,e^{-\pi n^2x};$$
each depends only on $a$ modulo $1$. They are real functions defined for every real $x$; only
$x>0$ is used, where they are these sums. For $a,b\in\mathbb R/\mathbb Z$ the *theta kernel* of the
shifted lattice $(a,b)+\mathbb Z^2$ and its *dual kernel* are the complex functions
$$\theta_{a,b}(x)=O_a(x)E_b(x)+i\,E_a(x)O_b(x),\qquad
\theta^*_{a,b}(x)=S_a(x)C_b(x)+i\,C_a(x)S_b(x).$$

1. For $x>0$: $O_a(1/x)=x^{3/2}S_a(x)$ and $E_a(1/x)=x^{1/2}C_a(x)$.
2. (Transformation law.) For $x>0$: $\theta_{a,b}(1/x)=x^2\,\theta^*_{a,b}(x)$.
3. If $f:\mathbb R\to\mathbb R$ and real numbers $c$ and $p>0$ satisfy
   $f(x)-c=O(e^{-px})$ as $x\to\infty$, then $f(x)=O(1)$ as $x\to\infty$. In particular $E_a$ and
   $C_a$ are $O(1)$ as $x\to\infty$.
4. If $u,v:\mathbb R\to\mathbb R$, $u(x)=O(e^{-px})$ for some $p>0$ and $v(x)=O(1)$ as
   $x\to\infty$, then $u(x)v(x)=O(x^r)$ as $x\to\infty$ for every real $r$.
5. For every real $r$, $\theta_{a,b}(x)=O(x^r)$ and $\theta^*_{a,b}(x)=O(x^r)$ as $x\to\infty$.
6. $\theta_{a,b}$ and $\theta^*_{a,b}$ are continuous on $(0,\infty)$.

**Proof sketch.** (1) These are the one-variable transformation laws
$O_a(x)=x^{-3/2}S_a(1/x)$ and $E_a(x)=x^{-1/2}C_a(1/x)$ (Poisson summation), read at $1/x$.

(2) Substitute (1) in the definition of $\theta_{a,b}(1/x)$ and use $x^2=x^{3/2}x^{1/2}$.

(3) Write $f=(f-c)+c$; $e^{-px}\le1$ for $x\ge0$, so both summands are $O(1)$. The kernels $E_a$
and $C_a$ differ from a constant by $O(e^{-px})$ for some $p>0$ (standard), so (3) applies.

(4) $u(x)v(x)=O(e^{-px})$, and $e^{-px}=o(x^r)$ for every $r$.

(5) $O_a$ and $S_a$ are $O(e^{-px})$ for some $p>0$ (standard), and $E_b$, $C_b$ are $O(1)$ by (3).
Apply (4) to each of the two products in $\theta_{a,b}$ and in $\theta^*_{a,b}$, and add.

(6) The four kernels are continuous on $(0,\infty)$.

## Depends on

None.

## Sources

- [Theta series and the method of Hecke](../../../../../sources/hecke-locators.md#theta-series-and-the-method-of-hecke)
