---
article_id: af_b3410f5f52da6a8ac84cdc02
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.pmin_expand_row, ZInQ.RouteK.Rank5b.Sec3.pmin_updateRow_sum, ZInQ.RouteK.Rank5b.Sec3.pmin_updateRow_add, ZInQ.RouteK.Rank5b.Sec3.pmin_eq_zero_of_row_eq
---

# Row operations on minors over $\mathbb F_2$

Let $V$ be a finite set, $M$ a $V\times V$ matrix over $\mathbb F_2$, $R,C\subseteq V$, and let
$\operatorname{per}M[R,C]$ be the minor of $M$ with rows $R$ and columns $C$, the sum over the
bijections $R\to C$. Then:

1. (row expansion) for $i\in R$,
   $\operatorname{per}M[R,C]=\sum_{v\in C}M_{iv}\operatorname{per}M[R\setminus\{i\},C\setminus\{v\}]$;
2. (linearity in a row) for $i\in R$ and finitely many row vectors $r_u$, the minor of the matrix
   $M$ with row $i$ replaced by $\sum_u r_u$ is the sum over $u$ of the minors of $M$ with row $i$
   replaced by $r_u$; in particular this holds for a sum $r+s$ of two rows;
3. (equal rows) if $i\ne k$ lie in $R$ and rows $i$ and $k$ of $M$ are equal, then
   $\operatorname{per}M[R,C]=0$.

**Proof sketch.** (1) Group the bijections by $v=\sigma(i)$: removing $i$ leaves a bijection
$R\setminus\{i\}\to C\setminus\{v\}$, and each such bijection extends uniquely by $i\mapsto v$; a
bijection is onto $C$, so every $v\in C$ occurs. (2) By (1), whose terms are linear in row $i$,
while the smaller minors in (1) do not involve row $i$, since a minor depends only on the rows it
uses. (3) Composing with the transposition of $i$ and $k$ is an involution of the bijections
$R\to C$; it has no fixed point, since $\sigma(i)\ne\sigma(k)$, and it keeps each product, since
rows $i$ and $k$ agree. So the terms cancel in pairs.

## Depends on

- [Minors over $\mathbb F_2$ as permanents](permanent-minors.md)

## Sources

- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
- [Lemma 2.2](../../../sources/rank-5b-locators.md#lemma-22)
