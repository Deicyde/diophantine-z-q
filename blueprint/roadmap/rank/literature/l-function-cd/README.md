---
article_id: af_34f41ef8124f802ebe64ab54
---

# The L-series of the congruent number curves, computed

Most literature statements of this section are about the L-series $L(C_d,s)$, defined by the recipe
of [entire continuations](../l-series-continuation.md): an Euler product over the finite places of
$\mathbb Q$ of local polynomials, each read off a minimal equation of $C_d$ over the completion,
where the minimal equation is one chosen once and for all. This subsection computes that recipe for
odd squarefree $d$, which includes every squarefree $d\equiv5\pmod8$. Nothing here is assumed; every
statement is proved.

Two general facts come first. Over a discrete valuation ring, an integral equation whose
discriminant is not divisible by the twelfth power of the maximal ideal is minimal, and two minimal
equations with nonzero discriminant differ by a change of variables with $u$ a unit, which reduces
to a change of variables over the residue field. So the local polynomial at a place of good
reduction, or of additive reduction with nonzero discriminant, can be computed from any minimal
equation, not only from the chosen one.

For $C_d:y^2=x^3-d^2x$ the discriminant is $(2d)^6$ and $c_4=48d^2$. For odd squarefree $d$ no
prime has its twelfth power dividing $(2d)^6$, so the equation is minimal at every prime; the
reduction is good at the primes $p\nmid2d$ and additive at the primes $p\mid2d$. The local
polynomial is therefore $1-a_pT+pT^2$ with $a_p=p+1-\#C_d(\mathbb F_p)$ (the point at infinity
included) at $p\nmid2d$, and $1$ at $p\mid2d$. Since only one place lies over each prime, the
Dirichlet coefficient of $L(C_d,s)$ at $p^k$ is the coefficient of $T^k$ in the inverse of that
polynomial. At every prime $p$ the coefficient is $p$ minus the number of affine solutions of
$y^2=x^3-d^2x$ over $\mathbb F_p$; at a prime $p\mid2d$ both are $0$, the affine solutions
being the $p$ points $(t^2,t^3)$ of the cusp $y^2=x^3$ when $p\mid d$, and $(0,0)$, $(1,0)$
when $p=2$. The coefficients are
multiplicative, so $L(C_d,s)$ is the Dirichlet series whose coefficients are those of the formal
Euler product $\prod_{p\nmid2d}(1-a_pp^{-s}+p^{1-2s})^{-1}$.

The computation proves none of the literature statements of this section (the functional
equation, Gross–Zagier, [row 5b](../tyz-row-5b.md), [reading A](../tyz-reading-a.md) and
[Hecke's continuation](../hecke-continuation.md)): it shows only that $L(C_d,s)$, for the
squarefree $d\equiv5\pmod8$ that the functional equation, row 5b and reading A concern, is the
standard L-series. It says nothing about $L(C_d,s)$ for even or non-squarefree $d$, which Hecke's
continuation also covers, nor about $L(E,s)$ for the other elliptic curves in Gross–Zagier.

The coefficients $c_d(n)$ of the formal Euler product are studied for every $d$, even or not
squarefree: they are multiplicative, vanish at the multiples of the primes dividing $2d$ (so at
every even $n$), and satisfy $c_d(p^{k+2})=c_d(p)c_d(p^{k+1})-p\,c_d(p^k)$ at the primes
$p\nmid2d$. Counting the solutions of $y^2=x^3-d^2x$ with the quadratic character $\chi$ of
$\mathbb F_p$ writes $c_d(p)$, for $p\nmid2d$, as minus the Jacobsthal sum $\sum_x\chi\bigl(x(x^2-d^2)\bigr)$.
Its second moment gives Hasse's bound $c_d(p)^2\le4p$; for $p\equiv3\pmod4$ the sum vanishes,
so $c_d(p^{2k})=(-p)^k$ and $c_d(p^{2k+1})=0$. With the recursion, Hasse's bound gives
$|c_d(n)|\le\sigma_0(n)\sqrt n$, so $\sum_nc_d(n)n^{-s}$ converges absolutely on
$\operatorname{Re}s>3/2$; for odd squarefree $d$ this series is $L(C_d,s)$, which is
therefore complex differentiable there. This subsection proves neither the continuation of
$L(C_d,s)$ nor its functional equation; both are proved, the continuation for every $d\ne0$,
in [Hecke's continuation holds](../hecke/hecke-continuation-holds.md) and
[the functional equation holds](../hecke/functional-equation-holds.md). The conductor is not
proved here.

Throughout, $d$ is a natural number, $p$ a prime, and $v$ a finite place of $\mathbb Q$ with prime
$p_v$, completion $\mathbb Q_v$, valuation ring $\mathcal O_v$, maximal ideal $\mathfrak m_v$ and
residue field $\kappa_v$. The number of elements of an infinite set is taken to be $0$; only finite
residue fields occur.

## Minimal equations over a discrete valuation ring

- [Minimal Weierstrass equations over a discrete valuation ring](minimal-models.md)
- [Point counts under changes of variables and field isomorphisms](point-counts.md)
- [The local polynomial from any minimal equation](local-polynomial.md)

## The curve and the completions of $\mathbb Q$

- [The model $y^2=x^3-d^2x$ over a ring](cd-model.md)
- [The places of $\mathbb Q$ and their completions](completion.md)
- [The curve $C_d$ over a completion of $\mathbb Q$](cd-local.md)

## The local factors of $C_d$

- [Minimality and reduction type of $C_d$ at each prime](cd-reduction.md)
- [The Euler polynomial of $C_d$ at $p$](cd-euler-polynomial.md)
- [The local polynomial of $C_d$ at each prime](cd-local-polynomial.md)

## The Dirichlet coefficients

- [The coefficients of $L(C_d,s)$ at prime powers](prime-power-coefficients.md)
- [The coefficients of $L(C_d,s)$ at primes as point counts](prime-coefficients.md)
- [Every coefficient of $L(C_d,s)$](coefficients.md)
- [$L(C_d,s)$ is the Dirichlet series of the standard Euler product](l-series.md)

## The coefficients for every $d$

- [The coefficients $c_d(n)$ for every $d$](coefficients-every-d.md)
- [The recursion for the coefficients at a good prime](good-prime-recursion.md)

## Character sums, Hasse's bound and absolute convergence

- [Point counts by the quadratic character](quadratic-character-counts.md)
- [Jacobsthal sums over a finite field and their bound](jacobsthal-sums.md)
- [Hasse's bound for $C_d$](hasse-bound.md)
- [The coefficients of $L(C_d,s)$ at the primes $p\equiv3\pmod4$](primes-3-mod-4.md)
- [Bounds for the coefficients $c_d(n)$](coefficient-bounds.md)
- [$L(C_d,s)$ converges absolutely on $\operatorname{Re}s>3/2$](absolute-convergence.md)
