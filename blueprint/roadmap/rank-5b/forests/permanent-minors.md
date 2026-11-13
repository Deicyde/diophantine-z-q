---
article_id: af_b1907774a86df0fdfb786493
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.det_submatrix_eq_pmin, ZInQ.RouteK.Rank5b.Sec3.pmin, ZInQ.RouteK.Rank5b.Sec3.bijFun, ZInQ.RouteK.Rank5b.Sec3.mem_bijFun, ZInQ.RouteK.Rank5b.Sec3.bijFun_surj, ZInQ.RouteK.Rank5b.Sec3.zmod2_units_smul, ZInQ.RouteK.Rank5b.Sec3.det_eq_pmin_univ, ZInQ.RouteK.Rank5b.Sec3.pmin_congr, ZInQ.RouteK.Rank5b.Sec3.pmin_eq_zero_of_card_ne, ZInQ.RouteK.Rank5b.Sec3.pmin_transpose, ZInQ.RouteK.Rank5b.Sec3.invOn, ZInQ.RouteK.Rank5b.Sec3.invOn_spec, ZInQ.RouteK.Rank5b.Sec3.invOn_apply, ZInQ.RouteK.Rank5b.Sec3.invOn_not_mem, ZInQ.RouteK.Rank5b.Sec3.invOn_mem, ZInQ.RouteK.Rank5b.Sec3.invOn_invOn
---

# Minors over $\mathbb F_2$ as permanents

Let $V$ be a finite set and $M$ a $V\times V$ matrix over $\mathbb F_2$. For $R,C\subseteq V$
put
$$\operatorname{per}M[R,C]=\sum_{\sigma}\prod_{i\in R}M_{i\sigma(i)},$$
the sum over the bijections $\sigma:R\to C$. This is the minor of $M$ with rows $R$ and columns
$C$ used below; it needs no signs and no ordering of $R$ and $C$. Then:

1. (principal minors) for $S\subseteq V$, $\det M[S,S]=\operatorname{per}M[S,S]$; in particular
   $\det M=\operatorname{per}M[V,V]$;
2. if $|R|\ne|C|$, then $\operatorname{per}M[R,C]=0$;
3. $\operatorname{per}M[R,C]$ depends only on the rows of $M$ indexed by $R$;
4. (transpose) $\operatorname{per}M^{\mathsf T}[A,C]=\operatorname{per}M[C,A]$ for
   $A,C\subseteq V$.

**Proof sketch.** (1) In the Leibniz expansion of $\det M[S,S]$ every sign $\pm1$ is $1$ in
$\mathbb F_2$, and the permutations of $S$ are exactly the bijections $S\to S$; the case $S=V$ is
$\det M$. (2) There are no bijections. (3) The products only involve rows in $R$. (4) Inverting a
bijection $A\to C$ gives a bijection $C\to A$, and this matches the two sums term by term: with
$c=\sigma(a)$, $\prod_{a\in A}M^{\mathsf T}_{a\sigma(a)}=\prod_{c\in C}M_{c\sigma^{-1}(c)}$.

## Depends on

None.

## Sources

- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
- [Lemma 2.2](../../../sources/rank-5b-locators.md#lemma-22)
