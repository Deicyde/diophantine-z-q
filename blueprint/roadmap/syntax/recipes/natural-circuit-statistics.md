---
article_id: af_6a2e2d89347f6b92cbd08fca
declaration: theorem
origin: cited
---

# Shape of the natural precision circuit

Let $\mathcal N$ be the five-input natural precision circuit and $\mathcal P$ its power
template. Then:

1. $\mathcal P$ has $3$ inputs and $79$ witnesses, no calls, $196$ addition nodes and $190$
   multiplication nodes, and its constants other than $0,1,-1$ are, in order of first
   occurrence, $4,2,3$;
2. $\mathcal N$ has $5$ inputs and $54056$ explicit variables, listed in increasing index
   order with the inputs first (so $54051$ explicit witnesses), $1305811$ variables in all;
   its node list has $125327$ addition nodes, $98382$ multiplication nodes and $15845$ call
   nodes, each calling $\mathcal P$ on three earlier nodes with a private block of $79$
   variables, these blocks being pairwise disjoint and disjoint from the explicit variables;
3. the constants of $\mathcal N$ other than $0,1,-1$ are, in order of first occurrence,
   $c_3,2,4,1399$, where $c_3$ is the program literal of the compiler chapter; in particular these four values
   are distinct, and $c_3\notin\{2,3,4\}$, so the distinct nontrivial constants of $\mathcal P$ and
   then $\mathcal N$, in order of first occurrence, are $4,2,3,c_3,1399$ (it suffices that
   $c_3>1399$).

Each item is a closed decidable statement about the explicit circuit: count the nodes of
each kind, list the constants in node order, and compare them. For orientation, $c_3$ has
$3{,}181{,}317$ decimal digits; that count is not part of the statement, and no part of the
statement requires expanding $c_3$ beyond comparing it with small integers.

## Depends on

- [Semantics of the natural precision polynomial](../../compiler/natural/natural-polynomial-semantics.md)

## Sources

- [Section 10.4](../../../sources/syntax-locators.md#section-10-translation)
- [Saved specification](../../../sources/syntax-locators.md#saved-specification)
