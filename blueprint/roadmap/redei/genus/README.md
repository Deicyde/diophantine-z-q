---
article_id: af_be201c52caf2a875ae3c6986
---

# Ambiguous classes and genus characters

This section is the genus theory of $K=\mathbb Q(\sqrt{-n})$, in the notation of the chapter:
$\mathcal O$, $\sigma$, $N$, $\mathrm{Cl}$, the set $T_n$ with $t=|T_n|$, the prime ideals
$\mathfrak p_p$ and the residue bits $[a/q]$. The main results assume $n$ odd and squarefree; each
article states its own hypotheses, and some auxiliary facts hold for every $n\ge1$.

- For $n$ odd and squarefree, the ambiguous class map $\psi:\mathbb F_2^{T_n}\to\mathrm{Cl}$
  sends $e$ to $\prod_p[\mathfrak p_p]^{e_p}$. By Hilbert 90 for ideals its image is $\mathrm{Cl}[2]$, and its
  kernel contains the exponent vector $e_n$ of $(\sqrt{-n})$, so $|\mathrm{Cl}[2]|\le2^{t-1}$ for
  $n>1$.
- For each prime $q\mid n$, the genus character $\chi_q$ sends the class of a nonzero ideal $I$
  with $q\nmid N(I)$ to $[N(I)/q]$. It is well defined because norms of elements are squares
  modulo $q$, and on the ambiguous classes it is given by the Rédei matrix.
- Through the slot lemma, Dirichlet's theorem shows that the genus characters take every family
  of values $(\varepsilon_q)_{q\mid n}$, subject only to $\sum_q\varepsilon_q=0$ when
  $n\equiv3\pmod4$.

## Ambiguous classes

- [Hilbert 90 for ideals](hilbert-90.md)
- [The ambiguous class map $\psi$](ambiguous-class-map.md)
- [The classes of the ramified primes](ramified-classes.md)
- [Classes of invariant ideals are ambiguous](invariant-ideals.md)
- [The ambiguous classes fill $\mathrm{Cl}[2]$](two-torsion.md)
- [A bound for the 2-torsion of the class group](two-torsion-bound.md)

## Genus characters

Each genus character is computed on a representative of norm prime to $q$; that its value does
not depend on the representative comes from the fact that norms of elements are squares modulo
the primes of $n$.

- [Every class has a representative of norm prime to $q$](coprime-representatives.md)
- [Norms are squares modulo the primes of $n$](norms-are-squares.md)
- [The norm residue bit depends only on the class](norm-bit-class-invariant.md)
- [The genus characters](genus-characters.md)
- [The genus characters on the ambiguous classes](characters-on-ambiguous-classes.md)

## The values of the genus characters

A prime $\ell\nmid 2n$ with $-n$ a square modulo $\ell$ is the norm of an ideal, and the slot lemma
supplies such primes with prescribed residue bits.

- [Split primes](split-primes.md)
- [The genus characters take all allowed values](surjectivity.md)
