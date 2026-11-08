---
article_id: af_128074e33aea9ba6ca55666c
---

# Primes in arithmetic progressions

The size bounds need every unit class modulo $W=4\prod_{p\le324}p$ to contain twenty-two
primes above $324$ below an explicit cutoff. The manuscript takes this from the explicit
progression estimate of Bennett, Martin, O'Bryant and Rechnitzer. This chapter proves it
instead from an effective form of Dirichlet's theorem with crude but explicit constants:
for $q\ge2^{16}$, every unit class modulo $q$ has twenty-two primes in $(q^2,2^{q^8})$. The
proof is the classical one, made quantitative; every constant is explicit, and the value of
an $L$-function at $s=1$ is reached as a limit from the right.

Notation: $\chi$ is a Dirichlet character modulo $q$, $\chi_0$ the principal one,
$M=\log q+3$ and $S_\chi(x)=\sum_{n\le x}\chi(n)\Lambda(n)/n$.

## $L$-values near $s=1$

Summation by parts bounds $L(\sigma,\chi)$, its derivative and its partial sums for real
$\sigma\ge1$, and the classical product inequality gives
$|L(1,\chi)|\ge1/(256M^7)$ when $\chi^2\ne\chi_0$.

- [Character sums and $L$-values near $s=1$](lseries/README.md)

## Real characters

When $\chi^2=\chi_0$, the value $L(1,\chi)$ is tied to a quadratic field: $\chi$ is a
Legendre symbol $(d/\cdot)$ away from $2q$, the Dedekind zeta function of
$\mathbb Q(\sqrt d)$ factors as $\zeta(s)L(s,\chi)$ up to finitely many local factors, and
the class number formula with crude bounds on the discriminant, the roots of unity and the
regulator gives $|L(1,\chi)|\ge1/(40q^{3/2})$. The splitting law and the field need only that
$d$ is not a square.

- [Quadratic fields](quadratic-fields/README.md)
- [Ideal counts in quadratic fields](ideal-counts/README.md)
- [Real characters](real-characters/README.md)

## The count

Mertens' first theorem (with constant $3$), the identity relating $L(1,\chi)S_\chi(x)$ to
$\sum_{n\le x}\chi(n)\log n/n$, and orthogonality give at least twenty-two primes of each
unit class in $(q^8,q^8e^{5qB}]$, where $B=(M^2+6q)/c$ and $c$ is a lower bound for
$|L(1,\chi)|$ at all nonprincipal $\chi$; here $\log(e^{5qB})$ is of order $q^{11/2}$.

- [Counting primes in a residue class](counting/README.md)

## The theorem and its instance

- [An effective Dirichlet theorem](effective-dirichlet.md)

At $q=W$ this is the catalogue bound with cutoff $2^{W^8}$, the fourth hypothesis of the main
theorem.

- [The catalogue bound holds](catalogue-instance.md)
