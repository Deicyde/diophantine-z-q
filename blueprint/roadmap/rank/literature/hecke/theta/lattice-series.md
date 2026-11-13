---
article_id: af_892003ce9681cbfe5df38f8a
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.gz, ZInQ.Contrib.HeckeFE.gq, ZInQ.Contrib.HeckeFE.gq_eq_norm_sq, ZInQ.Contrib.HeckeFE.gq_nonneg, ZInQ.Contrib.HeckeFE.norm_cexp_two_pi_I, ZInQ.Contrib.HeckeFE.ech, ZInQ.Contrib.HeckeFE.norm_ech, ZInQ.Contrib.HeckeFE.hasSum_gaussTheta, ZInQ.Contrib.HeckeFE.hasSum_gaussThetaDual, ZInQ.Contrib.HeckeFE.gaussPeriodPair, ZInQ.Contrib.HeckeFE.summable_norm_gz_rpow, ZInQ.Contrib.HeckeFE.hasSum_gaussLambda, ZInQ.Contrib.HeckeFE.summable_gz_div, ZInQ.Contrib.HeckeFE.hasSum_gaussLambdaDual, ZInQ.Contrib.HeckeFE.gaussL, ZInQ.Contrib.HeckeFE.gaussL_continuation
---

# The lattice Dirichlet series and its entire continuation

For real $a,b$ and $(m,n)\in\mathbb Z^2$ put
$$z_{a,b}(m,n)=(m+a)+i(n+b),\qquad N_{a,b}(m,n)=(m+a)^2+(n+b)^2,\qquad
e_{a,b}(m,n)=e^{2\pi i(am+bn)}.$$
For $N\ge0$ real and $s\in\mathbb C$, $N^s$ is the complex power ($e^{s\log N}$ for $N>0$, and
$0^s=0$ for $s\ne0$). The *lattice Dirichlet series* is
$$L_{a,b}(s)=\sum_{(m,n)\in\mathbb Z^2}\frac{z_{a,b}(m,n)}{N_{a,b}(m,n)^s},$$
read as $0$ where the family is not summable. The lattice $\mathbb Z+\mathbb Zi\subset\mathbb C$ has
the basis $1,i$. Let $\theta_{a,b},\theta^*_{a,b}$ be the [theta kernels](theta-kernels.md) and
$\Lambda_{a,b},\Lambda^*_{a,b}$ the [completed lattice functions](theta-mellin.md), with $a,b$ taken
modulo $1$.

1. $N_{a,b}(m,n)=|z_{a,b}(m,n)|^2\ge0$, and $|e^{2\pi ix}|=1$ for real $x$; so $|e_{a,b}(m,n)|=1$.
2. For $t>0$, $\displaystyle\theta_{a,b}(t)=\sum_{(m,n)}z_{a,b}(m,n)\,e^{-\pi N_{a,b}(m,n)t}$ and
   $\displaystyle\theta^*_{a,b}(t)=\sum_{(m,n)}-i\,(m+in)\,e_{a,b}(m,n)\,e^{-\pi(m^2+n^2)t}$, both
   families summable.
3. For real $r<-2$, $\sum_{(m,n)}|z_{a,b}(m,n)|^r<\infty$ (a term with $z_{a,b}(m,n)=0$ is $0$).
4. For $\operatorname{Re}s>3/2$: the family $z_{a,b}/N_{a,b}^s$ is absolutely summable, and
   $$\Lambda_{a,b}(s)=\sum_{(m,n)}\pi^{-s}\Gamma(s)\frac{z_{a,b}(m,n)}{N_{a,b}(m,n)^s},\qquad
   \Lambda^*_{a,b}(s)=\sum_{(m,n)}\pi^{-s}\Gamma(s)\frac{-i\,(m+in)\,e_{a,b}(m,n)}{(m^2+n^2)^s}.$$
5. (Hecke.) There is an entire function $F$ with $F(s)=L_{a,b}(s)$ for every $s$ with
   $\operatorname{Re}s>3/2$.

**Proof sketch.** (1) Direct computation.

(2) $O_a(t)$ and $E_b(t)$ are absolutely convergent sums over $\mathbb Z$, so their product is the
sum over $\mathbb Z^2$ of the products of terms, and
$e^{-\pi N_{a,b}(m,n)t}=e^{-\pi(m+a)^2t}e^{-\pi(n+b)^2t}$; likewise for $E_a(t)O_b(t)$, and the two
combine to $z_{a,b}(m,n)$. For the dual kernel use the expansions
$S_a(t)=\sum_n-i\,n\,e^{2\pi ian}e^{-\pi n^2t}$ and $C_a(t)=\sum_ne^{2\pi ian}e^{-\pi n^2t}$ (the
odd parts cancel under $n\mapsto-n$) and multiply in the same way.

(3) The standard summability of $\sum_{\omega}|\omega-w|^r$ over a lattice $\omega$ of rank $2$ in
$\mathbb C$, for $r<-2$, applied to $\mathbb Z+\mathbb Zi$ and $w=-(a+bi)$.

(4) A function given for $t>0$ by $\sum_kc_ke^{-\pi\lambda_kt}$ with $\lambda_k\ge0$ (and
$c_k=0$ when $\lambda_k=0$) has Mellin transform $\sum_k\pi^{-s}\Gamma(s)c_k\lambda_k^{-s}$ whenever
$\sum_k|c_k|\lambda_k^{-\operatorname{Re}s}<\infty$ and $\operatorname{Re}s>0$. Apply it to (2): with
$\sigma=\operatorname{Re}s$, $|z_{a,b}|N_{a,b}^{-\sigma}=|z_{a,b}|^{1-2\sigma}$ and
$1-2\sigma<-2$, so (3) gives the hypothesis; for the dual, $|(m+in)e_{a,b}(m,n)|=|m+in|$ by (1).
Absolute summability of $z_{a,b}/N_{a,b}^s$ follows from the first identity after dividing by
$\pi^{-s}\Gamma(s)\ne0$.

(5) Take $F(s)=\pi^s\Gamma(s)^{-1}\Lambda_{a,b}(s)$. It is entire, since $\pi^s$ and $1/\Gamma$ are
entire and $\Lambda_{a,b}$ is entire ([completed lattice functions](theta-mellin.md) (3)). For
$\operatorname{Re}s>3/2$, $\Gamma(s)\ne0$ and (4) gives $F(s)=L_{a,b}(s)$.

## Depends on

- [The weight-two theta kernels of a shifted lattice](theta-kernels.md)
- [The completed lattice functions and their functional equation](theta-mellin.md)

## Sources

- [Theta series and the method of Hecke](../../../../../sources/hecke-locators.md#theta-series-and-the-method-of-hecke)
