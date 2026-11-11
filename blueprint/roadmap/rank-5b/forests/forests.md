---
article_id: af_8eeafc4ecc00ef041521429d
declaration: def
origin: background
statement: formalized
lean: ZInQ.RouteK.Rank5b.Sec3.forests, ZInQ.RouteK.Rank5b.Sec3.mapsOn, ZInQ.RouteK.Rank5b.Sec3.wt, ZInQ.RouteK.Rank5b.Sec3.root, ZInQ.RouteK.Rank5b.Sec3.IsAcyc, ZInQ.RouteK.Rank5b.Sec3.IsTransv, ZInQ.RouteK.Rank5b.Sec3.rootsOf, ZInQ.RouteK.Rank5b.Sec3.allF, ZInQ.RouteK.Rank5b.Sec3.mem_mapsOn, ZInQ.RouteK.Rank5b.Sec3.mem_forests, ZInQ.RouteK.Rank5b.Sec3.mem_allF, ZInQ.RouteK.Rank5b.Sec3.rootsOf_of_forests, ZInQ.RouteK.Rank5b.Sec3.mem_forests_rootsOf, ZInQ.RouteK.Rank5b.Sec3.sum_allF, ZInQ.RouteK.Rank5b.Sec3.iterate_mem, ZInQ.RouteK.Rank5b.Sec3.mem_of_ne, ZInQ.RouteK.Rank5b.Sec3.ne_of_mem, ZInQ.RouteK.Rank5b.Sec3.iterate_fixed', ZInQ.RouteK.Rank5b.Sec3.iterate_comm, ZInQ.RouteK.Rank5b.Sec3.fixed_of_periodic, ZInQ.RouteK.Rank5b.Sec3.exists_periodic_of_not_acyc, ZInQ.RouteK.Rank5b.Sec3.root_apply, ZInQ.RouteK.Rank5b.Sec3.root_iterate, ZInQ.RouteK.Rank5b.Sec3.root_mem, ZInQ.RouteK.Rank5b.Sec3.root_mem_F, ZInQ.RouteK.Rank5b.Sec3.root_of_fixed, ZInQ.RouteK.Rank5b.Sec3.root_eq_of_not_mem, ZInQ.RouteK.Rank5b.Sec3.root_mem_of_forests
---

# Forests on a finite set

Let $V$ be a finite set with $N$ elements and $f:V\to V$ a map.

- The *root* of $i\in V$ is $r_f(i)=f^N(i)$, and $f$ is *acyclic* if every root is a fixed point
  of $f$.
- For $U,R\subseteq V$, $f$ *moves $R$ in $U$* if it is the identity outside $R$ and, for
  $i\in R$, $f(i)\in U$ and $f(i)\ne i$.
- For $U,F\subseteq V$, a *forest on $U$ rooted at $F$* is an acyclic map that moves
  $U\setminus F$ in $U$. Its *tree* at $\rho\in F$ is $T_\rho=\{v\in U:r_f(v)=\rho\}$, and a set
  $W$ is a *transversal* of it if, for every $\rho\in F$, exactly one element of $W$ has root
  $\rho$.
- Given bits $a_{ij}\in\mathbb F_2$ ($i,j\in V$), the *weight* of $f$ on $R\subseteq V$ is
  $\mathrm{wt}_R(f)=\prod_{i\in R}a_{if(i)}$; for a forest on $U$ rooted at $F$ we write
  $\mathrm{wt}(f)=\mathrm{wt}_{U\setminus F}(f)$.
- The *roots of $g$ in $U$* are its fixed points in $U$, and a *forest on $U$* is a forest on $U$
  rooted at some $F\subseteq U$.

These notions satisfy the following.

1. In an acyclic map every periodic point is fixed, and a map that is not acyclic has a periodic
   point that is not fixed. So $f$ is acyclic exactly when it has no cycle of length at least $2$.
2. A fixed point is its own root. If $f$ is acyclic, $f(x)$ and every $f^k(x)$ have the same root
   as $x$.
3. Let $f$ move $U\setminus F$ in $U$. Then a point $x$ with $f(x)\ne x$ lies in $U\setminus F$, a
   point outside $U\setminus F$ is its own root, and the iterates and the root of a point of $U$
   stay in $U$. If moreover $f$ is acyclic, the root of every point of $U$ lies in $F$.
4. A map is a forest on $U$ if and only if it is the identity outside $U$, maps $U$ into $U$ and is
   acyclic. A forest on $U$ rooted at $F\subseteq U$ has exactly $F$ as its roots in $U$; so every
   forest on $U$ is rooted at exactly one $F\subseteq U$, namely its set of roots in $U$.
5. Hence, for every $\mathbb F_2$-valued function $H$ of a set and a map,
   $$\sum_{F\subseteq U}\ \sum_{f}H(F,f)=\sum_{g}H\bigl(R_U(g),g\bigr),$$
   where $f$ runs over the forests on $U$ rooted at $F$, $g$ over the forests on $U$, and $R_U(g)$
   is the set of roots of $g$ in $U$.

## Depends on

None.

## Sources

- [Lemma 2.1](../../../sources/rank-5b-locators.md#lemma-21)
