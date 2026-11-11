---
article_id: af_8448b21c4b00ef65c1744e6c
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.pmin_lapl_eq_sum_maps, ZInQ.RouteK.Rank5b.Sec3.compat, ZInQ.RouteK.Rank5b.Sec3.mem_compat
---

# Expanding the diagonal of a Laplacian

Let $a$ be bits on a finite set $V$, let $U\subseteq V$ with Laplacian $L_U$, and let
$R,C\subseteq V$ with $C\subseteq U$. For a map $f:V\to V$ let $\mathrm{compat}_{R,C}(f)$ be the
set of bijections $\sigma:R\to C$ with $\sigma(i)\in\{i,f(i)\}$ for every $i\in R$. Then
$$\operatorname{per}L_U[R,C]=\sum_f\mathrm{wt}_R(f)\cdot\#\mathrm{compat}_{R,C}(f),$$
the sum over the maps $f$ that move $R$ in $U$, with the counts read in $\mathbb F_2$.

**Proof sketch.** Fix a bijection $\sigma:R\to C$ and expand $\prod_{i\in R}(L_U)_{i\sigma(i)}$.
If $\sigma(i)\ne i$, the factor is the single bit $a_{i\sigma(i)}$, and $\sigma(i)\in C\subseteq U$;
it is the choice $f(i)=\sigma(i)$. If $\sigma(i)=i$, the factor is $\sum_{j\in U,\,j\ne i}a_{ij}$,
and each term is a choice $f(i)=j$. Extending by the identity outside $R$, the product becomes
$\sum\mathrm{wt}_R(f)$ over the maps $f$ that move $R$ in $U$ and satisfy
$\sigma(i)\in\{i,f(i)\}$ for all $i\in R$. Summing over $\sigma$ and exchanging the two sums gives
the claim.

## Depends on

- [The Laplacian of a family of bits](laplacian.md)
- [Minors over $\mathbb F_2$ as permanents](permanent-minors.md)
- [Forests on a finite set](forests.md)

## Sources

- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
