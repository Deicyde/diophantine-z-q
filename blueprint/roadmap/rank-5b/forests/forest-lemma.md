---
article_id: af_66c3af3265939d21034b061b
declaration: theorem
origin: background
statement: formalized
proof: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.pmin_lapl_eq_forests
---

# The forest lemma (Lemma 2.1)

Let $a$ be bits on a finite set $V$, let $U\subseteq V$ with Laplacian $L_U$, and let
$F,W\subseteq U$ with $|F|=|W|$. Then
$$\operatorname{per}L_U[U\setminus F,\,U\setminus W]=\sum_f\mathrm{wt}(f),$$
the sum over the forests $f$ on $U$ rooted at $F$ of which $W$ is a transversal, that is, in which
every tree contains exactly one element of $W$. This is the case over $\mathbb F_2$ of the
all-minors matrix-tree theorem.

**Proof sketch.** Since $U\setminus W\subseteq U$, the diagonal expansion writes the minor as
$\sum_f\mathrm{wt}(f)\cdot\#\mathrm{compat}(f)$ over the maps $f$ that move $U\setminus F$ in $U$,
where $\mathrm{compat}(f)$ is the set of bijections $\sigma:U\setminus F\to U\setminus W$ with
$\sigma(i)\in\{i,f(i)\}$. The maps that are not acyclic have an even number of compatible
bijections and drop out. The acyclic ones are the forests on $U$ rooted at $F$, and for a forest
the number of compatible bijections is $1$ if $W$ is a transversal and $0$ otherwise.

## Depends on

- [Minors over $\mathbb F_2$ as permanents](permanent-minors.md)
- [Forests on a finite set](forests.md)
- [The Laplacian of a family of bits](laplacian.md)

## Proof depends on

- [Expanding the diagonal of a Laplacian](diagonal-expansion.md)
- [Maps with a cycle contribute an even number](cycles-cancel.md)
- [A forest has at most one compatible bijection](forest-bijection.md)

## Sources

- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
- [Matrix-tree theorem](../../../sources/rank-5b-locators.md#matrix-tree-theorem)
