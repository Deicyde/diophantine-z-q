---
article_id: af_0d7c19d565038298ef17cf69
---

# Rédei's formula for the 4-rank of class groups

For a set $B$ of primes of an odd number $d$, the genus sum $T_{5b}(d)$ of the
[row-5b chapter](../rank-5b/README.md) uses Rédei's $g_d(B)$, a determinant in the residue bits of
the primes. Tian, Yuan and Zhang state their criterion for analytic rank one with the genus class
numbers $g(d_B)=|\mathrm{Cl}(\mathbb Q(\sqrt{-d_B}))^2|$ instead, where $d_B=\prod_{p\in B}p$. This
chapter proves Rédei's formula, $g(d_B)\equiv g_d(B)\pmod2$ for every block of a genus sum. So the
certified rank hypothesis stated with Tian, Yuan and Zhang's own class numbers is equivalent to the
one stated with Rédei's $g$.

The proof is genus theory in the ring of integers of $K=\mathbb Q(\sqrt{-n})$, $n$ odd and
squarefree, with Dirichlet's theorem on primes in progressions in place of the Hasse–Minkowski
theorem:

- the classes of the ramified primes fill $\mathrm{Cl}[2]$;
- the genus characters $\chi_q([\mathfrak a])=[N\mathfrak a/q]$, one for each prime $q\mid n$,
  together take at least $2^{t-1}$ values;
- counting then gives the principal genus theorem $\mathrm{Cl}^2=\bigcap_q\ker\chi_q$, and Rédei's
  theorem: $g(n)$ is odd if and only if the kernel of the Rédei matrix is spanned by the exponent
  vector of $(\sqrt{-n})$;
- linear algebra over $\mathbb F_2$ turns that kernel condition into $g_d(B)=1$.

Throughout, $n\ge1$ is an integer and $K=\mathbb Q(\omega)$ with $\omega^2=-n$. We write
$\mathcal O$ for its ring of integers, $\sigma$ for its nontrivial automorphism and $\mathrm{Cl}$ for
the class group of $\mathcal O$. $N$ is the absolute norm of elements and ideals, and
$[a/p]\in\mathbb F_2$ is the [residue bit](../route-k/residue-bits.md). The set $T_n$ of ramified
primes, $t=|T_n|$, and the prime ideals $\mathfrak p_p$ are defined in
[the ramified primes](field/ramified-primes.md).

On notation: the letter $n$ is reserved for the field $\mathbb Q(\sqrt{-n})$, while $d$ is the odd
number whose primes carry the bits $a_{pq}$, $y_p$, $z_p$, and $g_d(B)$ is Rédei's $g$ of a set $B$
of its primes. The row-5b chapter writes $n$ and $C_n$ for that number; here, as in the Selmer
chapter, the congruent number curve is $C_d$.

## The genus class number and Rédei's formula

- [The genus class number](genus-class-number.md)
- [The statement of Rédei's formula](redei-formula-statement.md)
- [Rédei's formula](redei-formula.md)

## The Rédei matrix

- [The Rédei matrix](redei-matrix.md)

## The field and its primes

The field $\mathbb Q(\sqrt{-n})$, its conjugation and norms, and the splitting of rational primes,
decided by norms of ideals and residue fields without an explicit integral basis.

- [The field $\mathbb Q(\sqrt{-n})$ and its primes](field/README.md)

## Ambiguous classes and genus characters

- [Ambiguous classes and genus characters](genus/README.md)

## The 4-rank

- [The 4-rank](four-rank/README.md)

## From the Rédei matrix to Rédei's bits

- [From the Rédei matrix to Rédei's bits](bits/README.md)

## Consequences for the certified rank hypothesis

By Rédei's formula, the genus sum of class numbers equals the genus sum of Rédei bits, so the
class-number form CR₃^TYZ_Cl of the certified rank hypothesis is equivalent to CR₃^TYZ.

- [The genus sum of class numbers](class-number-genus-sum.md)
- [The certified rank hypothesis with class numbers](certified-rank-tyz-cl.md)
- [The genus sum of class numbers is the genus sum of Rédei bits](genus-sums-agree.md)
- [CR₃ with class numbers is CR₃^TYZ](class-number-hypothesis.md)

The same comparison of genus sums shows that the positive-rank form of CR₃^TYZ_Cl implies the
positive-rank form of CR₃^TYZ; that implication is stated in the positive-rank chapter
([CR₃^TYZ_Cl,Rk implies CR₃^TYZ,Rk](../rank/certified-rank-tyz-rk-of-cl-rk.md)).
