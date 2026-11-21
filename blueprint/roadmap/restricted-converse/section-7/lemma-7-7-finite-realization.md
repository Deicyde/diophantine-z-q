---
article_id: af_8aaf1a22d4b77e78aed64094
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Symbols.finite_realization
---

# Lemma 7.7: finite realization

Let $m>0$ be even, let $P$ be a finite set of primes prime to $m$ (the old vertices), and let $X$ be a
finite avoidance set. For $n$ new vertices prescribe reduced residue classes $c_1,\dots,c_n$ modulo
$m$, bits $b_i(p)\in\mathbb F_2$ for $p\in P$, and bits $b_{ij}\in\mathbb F_2$ for $j<i$. Then there are
distinct primes $q_1,\dots,q_n$, outside $P\cup X$, with $q_i\equiv c_i\pmod m$,
$$\Bigl(\frac{q_i}{p}\Bigr)=(-1)^{b_i(p)}\quad(p\in P),\qquad
\Bigl(\frac{q_i}{q_j}\Bigr)=(-1)^{b_{ij}}\quad(j<i).$$

A type is represented by a reduced residue class modulo $m$, as in the manuscript's proof. The reverse
bits are not part of the statement; they follow by quadratic reciprocity. The clause about replacing a
product template by a fresh prime is not part of this theorem.

**Proof sketch.** Choose the new primes one at a time. A prescribed bit at an earlier prime is a
nonzero residue class modulo that prime. The Chinese remainder theorem combines these classes with the
class modulo $m$, and Dirichlet's theorem gives infinitely many primes in the resulting reduced class,
so one avoids all earlier primes and $X$.

## Depends on

- [Section 7: typed graphs](README.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
