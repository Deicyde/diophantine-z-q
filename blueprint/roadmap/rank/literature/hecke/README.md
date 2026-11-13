---
article_id: af_fdd24cabfc14bc52201eec3f
---

# Hecke's continuation and the functional equation, proved

This section proves two of the literature statements of the chapter: [Hecke's
continuation](../hecke-continuation.md) of $L(C_d,s)$ for every natural number $d\ne0$, and
[the functional equation](../functional-equation.md) $\Lambda_{32d^2}(2-s)=-\Lambda_{32d^2}(s)$ on
the strip $0<\operatorname{Re}s<2$ for squarefree $d\equiv5\pmod8$. Both are proved with no
hypothesis. The main classical input is Gauss's count of the points of $y^2=x^3-x$ over
$\mathbb F_p$, which is proved here too, by a quartic Jacobi sum; the extension to every $d$ also
uses minimal equations at $2$ and changes of variables, which are proved as well.

The route is Hecke's. Classically $C_d$ has complex multiplication by $\mathbb Z[i]$ (this is not
proved or used here); what is proved is that, for squarefree $d\equiv1\pmod4$, its coefficients are
those of the character
$\psi_d(\alpha)=\left(\frac{N(\alpha)}d\right)u(\alpha)\,\alpha$ of $\mathbb Q(i)$, where $u(\alpha)$
is the primary unit of $\alpha$; this is Deuring's identity, $c_d(n)=\lambda_d(n)$ with
$\lambda_d(n)=\frac14\sum_{N(\alpha)=n}\psi_d(\alpha)$. It is proved by comparing Euler products: the
Hecke coefficients are multiplicative and satisfy the Hecke relation at prime powers, by unique
factorization in $\mathbb Z[i]$, and at the primes the two sides agree by direct counts at $2$, at
$p\mid d$ and at $p\equiv3\pmod4$, and by Gauss's count at $p\equiv1\pmod4$ after a quadratic twist.
Deuring's identity makes $L(C_d,s)$ a periodic twist $\sum_\alpha c(\alpha\bmod4d)\,\alpha\,N(\alpha)^{-s}$
of the lattice series of $\mathbb Z[i]$. Each such series is a finite combination of Mellin
transforms of theta kernels of shifted lattices, which are entire, so $L(C_d,s)$ has an entire
continuation. The transformation law of the theta kernels, together with a finite Fourier identity
for $c$ proved with quadratic Gauss sums, gives the functional equation, with the factor
$(32d^2)^{s/2}$ and sign $\left(\frac2d\right)=-1$.

Deuring's identity is proved for squarefree $d\equiv1\pmod4$, which covers the functional equation.
For Hecke's continuation at every $d\ne0$, the computation of $L(C_d,s)$ is extended to even
squarefree $d$, the coefficients of $C_d$ are written as a quadratic twist of those of $C_1$, and a
square factor of $d$ is removed by a change of variables, under which the L-series does not change.

The section also records the consequence for the class-number hypothesis: with the functional
equation and the case $d\equiv5\pmod8$ of Hecke's continuation proved, CR₃^TYZ_Cl,Rk follows from
two hypotheses that remain unproved, Tian–Yuan–Zhang's Theorem 3.5(2) in reading A and the
Gross–Zagier statement. Reading A is one reading of their theorem that no refereed text found
states ([reading A](../tyz-reading-a.md)).

Throughout, $C_d$ is the curve $y^2=x^3-d^2x$; $c_d(n)$ are the coefficients of
[the standard Euler product](../l-function-cd/l-series.md); a pair $(a,b)\in\mathbb Z^2$ is also the
Gaussian integer $a+bi$, with norm $N(a,b)=a^2+b^2$; and $\left(\frac an\right)$ is the Jacobi symbol
as in [the Hecke character $\psi_d$](gaussian/hecke-character.md).

## Theta series and Hecke's continuation for $\mathbb Z[i]$

- [Theta series of $\mathbb Z[i]$ and Hecke's continuation](theta/README.md)

## The Hecke character and its Euler product

- [The Hecke character $\psi_d$ and its coefficients](gaussian/README.md)

## Gauss's point count

- [Gauss's point count on $y^2=x^3-x$](gauss/README.md)

## Deuring's identity

- [Deuring's identity for $C_d$](deuring/README.md)

## The Fourier identity

- [The Fourier identity for the Hecke character](fourier/README.md)

## The case $d\equiv5\pmod8$

- [The continuation of $L(C_d,s)$ from Deuring's identity](continuation-of-deuring.md)
- [The functional equation from Deuring's identity and the Fourier identity](functional-equation-of-deuring.md)
- [Hecke's continuation for $d\equiv5\pmod8$ and the functional equation from Gauss's point count](both-from-gauss-count.md)

## Every natural number $d\ne0$

- [The L-series of $C_d$ for every $d\ne0$](every-d/README.md)

## The two statements

- [Hecke's continuation holds](hecke-continuation-holds.md)
- [The functional equation holds](functional-equation-holds.md)

## The class-number hypothesis without them

- [Row 5b from reading A and Hecke's continuation for $d\equiv5\pmod8$](row-5b-restricted.md)
- [CR₃^TYZ_Cl,Rk from reading A, Gross–Zagier and Gauss's point count](certified-rank-of-gauss-count.md)
