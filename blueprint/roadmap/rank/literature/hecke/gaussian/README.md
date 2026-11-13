---
article_id: af_c84604eecd8b8160c706e957
---

# The Hecke character $\psi_d$ and its coefficients

This subsection is about the Gaussian integers, with one exception: the vanishing of $\lambda_d(p)$
at the primes $p\mid2d$ is read off from Deuring's identity at those primes. For a natural number
$d$, the Hecke character $\psi_d$ is $\psi_d(\alpha)=\left(\frac{N(\alpha)}d\right)u(\alpha)\,\alpha$ on $\mathbb Z[i]$,
where $u(\alpha)$ is a unit read off $\alpha$ modulo $4$ (the primary unit, $0$ when $1+i$ divides
$\alpha$). It is completely multiplicative and takes the value $1$ on the four units, so the
coefficients $\lambda_d(n)=\frac14\sum_{N(\alpha)=n}\psi_d(\alpha)$ are a sum over the ideals of
norm $n$. For squarefree $d\equiv1\pmod4$ its coefficients are those of $C_d$
([Deuring's identity](../deuring/deuring-from-gauss-count.md)).

These coefficients are multiplicative, by counting the factorizations $\gamma=\alpha\beta$ with
$N(\alpha)=m$, $N(\beta)=n$ for coprime $m,n$. At a prime $p\equiv1\pmod4$ that does not divide
$d$, the factorization $p=\pi\bar\pi$ into two non-associate Gaussian primes gives the Hecke relation
$\lambda_d(p^{k+2})=\lambda_d(p)\lambda_d(p^{k+1})-p\lambda_d(p^k)$; at a prime $p\equiv3\pmod4$
not dividing $d$, the elements of norm $p^{k+2}$ are $p$ times those of norm $p^k$, which gives
$\lambda_d(p^{k+2})=-p\lambda_d(p^k)$; and at $2$ and at the primes dividing $d$ the coefficients of
the prime powers vanish. Together, for odd squarefree $d$, the coefficients are those of an Euler
product with local factors $(1-\lambda_d(p)T+pT^2)^{-1}$ at $p\nmid2d$ and $1$ at $p\mid2d$.

Throughout, a pair $(a,b)\in\mathbb Z^2$ is also the Gaussian integer $a+bi$, with norm
$N(a,b)=a^2+b^2$; $A_n$ is the set of Gaussian integers of norm $n$; and $\left(\frac an\right)$ is
the Jacobi symbol as in [the Hecke character](hecke-character.md).

- [Gaussian integers as pairs, norms and units](norm-fibres.md)
- [Factoring a Gaussian integer along coprime norms](norm-fibres-coprime.md)
- [Gaussian integers whose norm is a prime power](norm-fibres-primes.md)
- [The Gaussian primes above a split prime](norm-fibres-split.md)
- [The primary unit of a Gaussian integer modulo 4](primary-unit.md)
- [The Hecke character $\psi_d$](hecke-character.md)
- [The coefficients of the Hecke L-series $L(\psi_d,s)$](hecke-coefficients.md)
- [The Hecke coefficients at the primes that do not split](hecke-coefficients-non-split.md)
- [The Hecke coefficients are multiplicative](hecke-multiplicative.md)
- [The Hecke relation at prime powers](hecke-split-recursion.md)
- [Inverses of quadratic power series](quadratic-power-series.md)
- [The Euler product of $L(\psi_d,s)$](hecke-euler-product.md)
