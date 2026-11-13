---
article_id: af_7de38e35edd5ff952c62e3dc
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.Contrib.HeckeFE.OddGauss, ZInQ.Contrib.HeckeFE.oddGauss_prime, ZInQ.Contrib.HeckeFE.oddGauss_one, ZInQ.Contrib.HeckeFE.crt_injective2, ZInQ.Contrib.HeckeFE.sum_crt2, ZInQ.Contrib.HeckeFE.oddGauss_mul, ZInQ.Contrib.HeckeFE.oddGauss_of_prime
---

# The odd part of the Fourier transform

Let $G_d$ be the odd part of [the factorization](fourier-factorization.md). The *odd Gauss sum
identity* holds for a natural number $d$ if
$$G_d(\nu)=d\left(\frac{\nu_1^2+\nu_2^2}d\right)\qquad\text{for every }\nu\in\mathbb Z^2.$$

1. The identity holds for every odd prime $p$, and for $d=1$.
2. Let $m,n$ be coprime. The map $(a,b)\mapsto(na+mb)\bmod mn$ is injective on
   $\{0,\dots,m-1\}\times\{0,\dots,n-1\}$. If moreover $m,n>0$ and $g:\mathbb Z\to\mathbb C$
   satisfies $g(x)=g(x\bmod mn)$ for every $x$, then
   $\sum_{j=0}^{mn-1}g(j)=\sum_{a=0}^{m-1}\sum_{b=0}^{n-1}g(na+mb)$.
3. If $m,n>0$ are coprime and the identity holds for $m$ and for $n$, it holds for $mn$.
4. If the identity holds for every odd prime, it holds for every odd squarefree $d$.

**Proof sketch.** (1) For $d=p$, identify $\{0,\dots,p-1\}^2$ with $\mathbb F_p^2$; the Jacobi
symbols become the quadratic character $\chi$ of $\mathbb F_p$, and the identity is the
two-dimensional quadratic Gauss sum
([quadratic Gauss sums](quadratic-gauss-sums.md) (6), with (1) there). For $d=1$ both sides are
$1$.

(2) The Chinese remainder theorem, and a bijection by counting.

(3) Apply (2) in both coordinates: $b=n b'+m b''$. Then $e^{2\pi i\,b\cdot\nu/(mn)}=
e^{2\pi i\,b'\cdot\nu/m}e^{2\pi i\,b''\cdot\nu/n}$; $N(b)\equiv n^2N(b')\pmod m$ with
$\left(\frac{n^2}m\right)=1$, and likewise modulo $n$; and the Jacobi symbol is multiplicative in
its denominator. So $G_{mn}(\nu)=G_m(\nu)G_n(\nu)$, and the right sides multiply in the same way.

(4) Induction over the factorization of $d$: a squarefree prime power is a prime, odd because $d$
is; $d=1$ is (1); a product of coprime factors is (3); $d=0$ is not odd.

## Depends on

- [The Fourier transform of $\omega_d$ splits into a 2-part and an odd part](fourier-factorization.md)

## Proof depends on

- [Quadratic Gauss sums over $\mathbb F_p$ in one and two variables](quadratic-gauss-sums.md)

## Sources

- [Gauss and Jacobi sums](../../../../../sources/hecke-locators.md#gauss-and-jacobi-sums)
