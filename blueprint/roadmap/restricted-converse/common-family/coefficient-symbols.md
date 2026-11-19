---
declaration: def
origin: cited
---

# Compatible typed graphs and coefficient symbols

Fix the finite support $S$ of a coefficient source, containing $2$, and the finite quadratic characters
used to read its coefficients. The *type* of a prime $p\notin S$ records its values under these characters
and its unit squareclasses at $S$, including its class modulo $8$; types form a finite elementary two-group
$\mathcal L$, written additively, with all relations among the coordinates retained. In the present case
($E[2]$ rational) there is one independent residue bit per pair of primes.

A *compatible typed graph* is a finite ordered vertex set $V$ with an individually realizable type
$\ell_v\in\mathcal L$ for each vertex and quadratic residue bits: for prime representatives,
$z_{vw}=0$ or $1$ according as $(p_v/p_w)=1$ or $-1$. For each unordered pair one direction is free and the
other is fixed by reciprocity,
$$z_{vw}+z_{wv}=\epsilon_v\epsilon_w,\qquad \epsilon_v=(p_v-1)/2\bmod 2.$$
A filter prescribes the total type $\sum_v\ell_v$. *Contracting* two vertices replaces their types by the
sum and every incidence to an external vertex by the sum of the two incidences; it is represented by a fresh
prime with those data, and no internal bit is kept. A vertex is *primary* if its generator is a square unit
at the fixed support and its type is neutral in every retained coordinate, and *neutral relative to a
graph* if moreover all its incidences to the other vertices are zero. Two symbols may read surjective
projections of one common type group that commute with these rules.

A *symbol*, for one fixed coefficient source and one fixed normalized depth $\delta$, is the function
$A$ with values in $\mathbb F_2$ given on an allowed positive squarefree index $D$ by
$$A(D)=\begin{cases}1,&v_2(a(D))=\delta+\omega(D),\\0,&v_2(a(D))>\delta+\omega(D),\end{cases}$$
and zero off the source's filter. For the even source of Appendix E, phase removal makes the coefficient
rational. For an odd theta source, the comparison (3.8) removes the phase modulo the retained power
$2^{M_\theta}$, and the integer representative at that precision is used; a coefficient that is zero modulo
$2^{M_\theta}$ is invisible. At one finite odd stage the definition is used only through a finite
squarefree-weight cutoff at which the lower bound holds. The intrinsic odd symbol is the limit of such
finite tables, a function on finite compatible typed graphs, built in Appendix G.

The lower bound making the two alternatives exhaustive is part of each source's construction: for the
even source it follows from (3.2) and the coefficient-square formula of the even form.

## Depends on

- [An actual even form with rational normalized phase](../coefficient-sources/even-form.md)
- [The actual odd theta form and its recurrence](../coefficient-sources/odd-theta-form.md)
- [The unaveraged weighted theta comparison (O.7)](../coefficient-sources/theta-comparison.md)

## Sources

- [The 11/5 manuscript](../../../sources/manuscript.md): `ex:sec7-typed-graph` (L2015–2067) and
  `ex:sec7-symbol` (L2068–2101)

## Manuscript check

Read in full by AI review together with their uses. These are definitions. The review of the appendices
found the order of choices consistent with them: an odd symbol is used only through a finite weight cutoff
and operator budget, chosen before the theta stage and the primes (L10814–10861).
