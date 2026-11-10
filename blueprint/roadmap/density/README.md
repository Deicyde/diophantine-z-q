---
article_id: af_1b62a6e9391c95287ebef455
---

# Proposition D: the density of good slope primes

Route AP replaces the twenty-two-prime pattern by long arithmetic progressions of good slope
primes. Szemerédi's theorem in the primes provides them once the good slope primes are known to have
positive relative upper density in the primes; this chapter proves that density statement,
Proposition D of the route AP note in its weak form, following the project's research note on it.
No complex multiplication enters: the description of the good slope primes uses elementary
character sums only, the main term uses Dirichlet's theorem in residue classes, and the one deep-ish
step, a uniform bound for the primes removed at a medium prime $\ell$, uses a two-dimensional
Selberg sieve.

Notation: $G$ is the set of good slope primes, $\chi$ the quadratic character of $\mathbb F_p$,
$\varphi_p(a)=\sum_{x\in\mathbb F_p}\chi(x^3+ax)$, $\pi(N)$ the number of primes at most $N$, and for a set
$S$ of natural numbers $\theta_S(N)=\sum_{n\le N,\,n\in S}\log n$ and $\Phi_S(x)=\sum_{n\in S}(\log n)/n^x$.

- [The density statement for good slope primes](good-prime-density.md)

## Character sums and the description of good primes

The point counts of the two reductions of $E$ at a split prime are expressed through $\varphi_p$, and
Jacobsthal's identity writes $p=c_p^2+e_p^2$ with $c_p=\varphi_p(1)/2$. For the primes in the class
$p\equiv1\pmod8$, $(p/7)=-1$, being a good slope prime becomes $\gcd(c_p,p+1)=1$.

- [Character sums for the curves $y^2=x^3+ax$](character-sums.md)
- [Jacobsthal's identity](jacobsthal.md)
- [Four divides the point count of $y^2=x^3-D^2x$](four-divides-point-count.md)
- [The description of the good slope primes](description.md)

## The residue set and the main term

The congruence conditions modulo $8$, $7$ and the small primes $\ell\equiv1\pmod4$ define a set $C_L$ of
primes of Dirichlet density $\delta_L\ge3/(8(L-1))$; removing the primes $T_L$ bad at some $\ell>L$ leaves
good slope primes only.

- [The residue set $A_L$ and the primes $C_L$](residue-set.md)
- [The main term: the Dirichlet series of $C_L$](main-term.md)
- [A subset of good slope primes](good-subset.md)

## The primes bad at a large $\ell$

- [The primes bad at a large $\ell$](lattice-count.md)

## The sieve bound for a medium $\ell$

A prime bad at $\ell$ is a value of $(\ell U)^2+(b+\ell V)^2$ on a box, coprime to the small primes
$q\equiv1\pmod4$. The Selberg sieve, vendored from the PrimeNumberTheoremAnd project, bounds these
values; the local densities, the box count and a lower bound for the Selberg sum by elementary
divisor sums supply its inputs.

- [The Selberg sieve bound](selberg-sieve.md)
- [Local densities of $(\ell U)^2+(b+\ell V)^2$](local-densities.md)
- [Counting a box with a divisibility condition](box-count.md)
- [A lower bound for the Selberg sum](selberg-sum.md)
- [The sieve for the primes bad at $\ell$](sieve-instance.md)
- [The count of primes $c^2+e^2$ with $\ell\mid c$ and $\ell\mid p+1$](gauss-bad-count.md)
- [The uniform bound for the primes bad at a medium $\ell$](uniform-bad-bound.md)
- [The uniform bound holds](proposition-4-2.md)

## Assembly

The prime tail and Abel summation bound the Dirichlet series of $T_L$, the main term bounds that of
$C_L$ from below, and a positive lower Dirichlet density gives a positive relative upper density.

- [The prime tail $\sum_{\ell>L}\ell^{-2}$](prime-tail.md)
- [Abel summation for $\Phi_S$](abel-summation.md)
- [Dirichlet density gives relative upper density](dirichlet-density.md)
- [Theorem D: the density statement from the uniform bound](theorem-d.md)
- [Proposition D: the good slope primes have positive relative density](proposition-d.md)
- [Progressions of good slope primes from Szemerédi's theorem in the primes alone](good-prime-ap-from-dense-form.md)
