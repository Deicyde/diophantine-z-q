---
article_id: af_aaf25b05d838e79e291f6fb8
declaration: def
origin: bridged
statement: formalized
lean: ZInQ.Translation.WellFormedCore, ZInQ.Translation.WellFormed
---

# Well-formed natural circuits

A natural circuit $\mathcal N$ with $k$ inputs, explicit variables $(i_0,\kappa_0),(i_1,\kappa_1),\dots$,
nodes $n_0,\dots,n_{K-1}$, root $\rho$ and (if it has call nodes) power template $\mathcal P$ with
$V_{\mathcal P}$ variables is *well-formed with bound $V$* when:

1. the explicit variable indices are pairwise distinct, the first $k$ entries are the inputs
   with indices $0,\dots,k-1$, and no later entry is an input;
2. every argument of an $\mathrm{add}$, $\mathrm{mul}$ or $\mathrm{call}$ node $n_j$ is a node
   index below $j$, and $\rho<K$;
3. every $\mathrm{var}\ i$ node refers to an explicit variable $i$;
4. every $\mathrm{const}\ c$ node with $c\notin\{0,1,-1\}$ has $c\ge2$;
5. the blocks $[w,w+V_{\mathcal P}-3)$ of distinct call nodes are pairwise disjoint and disjoint
   from the set of explicit variable indices;
6. every explicit variable index and every block variable is below $V$;
7. if $\mathcal N$ has a call node, $\mathcal P$ has $3$ inputs, no call nodes, and is itself
   well-formed with bound $V_{\mathcal P}$, its explicit variables being $0,\dots,V_{\mathcal P}-1$.

Condition 3 says that the parent never reads a private coordinate of a call directly;
condition 4 is what the fixed-scalar templates need, since a nontrivial constant $c$ is
produced as $[c]P_0$. Under conditions 2, 3, 5 and 7, $\mathrm{val}_\theta(j)$ depends only on
the values of $\theta$ at the explicit variables and at the blocks of the call nodes among
the ancestors of $j$, and $[\![\mathcal N]\!]$ involves only variables below $V$.

This is a definition (a decidable predicate on a finite circuit).

## Depends on

- [Translation of a natural circuit into a model-evaluation recipe](../../syntax/recipes/model-evaluation-translation.md)
- [Values and polynomial of a natural circuit](natural-circuit-values.md)

## Sources

- [Section 10.4](../../../sources/compiler-translation-locators.md#section-104-power-value-and-precision-parent)
- [Translation artifacts](../../../sources/compiler-translation-locators.md#translation-artifacts)
