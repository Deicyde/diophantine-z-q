---
article_id: af_abec611ca4524381111e7b1a
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: ZInQ.Syntax.Pair.val, ZInQ.Syntax.holds_feq, ZInQ.Syntax.holds_curve
---

# Pair arithmetic represents the quadratic field

For a rational pair $u=(u_0,u_1)$ write $[u]=u_0+u_1s\in K_0$. For rational pairs
$u,u'$ and an integer $k$:

1. $[u+u']=[u]+[u']$, $[-u]=-[u]$, $[ku]=k[u]$, $[u\cdot u']=[u][u']$, $[\bar u]=\sigma[u]$
   where $\sigma$ is the conjugation $s\mapsto-s$, and $N(u)=[u]\,\sigma[u]\in\mathbb Q$;
2. $u\doteq u'$ holds exactly when $[u]=[u']$;
3. $\mathrm{NZ}_K(u)$ is satisfiable by its fresh variable exactly when $[u]\ne0$;
4. $\mathrm{Div}(n,d)$ holds for some value of its fresh variables with value $q$ exactly
   when $[d]\ne0$ and $[q]=[n]/[d]$;
5. for a rational point code $p$ and pairs $\zeta$, $v$: $Z(p,\zeta)$ holds for some value
   of its fresh variable exactly when either $p=O$ and $[\zeta]=0$, or $p_0=0$,
   $[y(p)]\ne0$ and $[\zeta]=-[x(p)]/[y(p)]$; and $I\!X(p,v)$ holds exactly when either $p=O$ and
   $[v]=0$, or $p_0=0$ and $[x(p)][v]=1$.

**Proof sketch.** Part 1 is $s^2=2$ and the definition of $\sigma$. Part 2 is the linear
independence of $1,s$ over $\mathbb Q$. Part 3 is the inverse-witness statement for pairs.
Part 4 combines 2 and 3 with $[d][q]=[n]$. Part 5 unfolds the two disjunctions with the
compilation theorem; the branches are exclusive because $p_0=1$ in the first and $p_0=0$
in the second.

## Depends on

- [Quadratic-field pairs and point-code formulas](language/field-pair-gadgets.md)

## Proof depends on

- [Inverse witnesses](nonzero-gadgets.md)
- [Sums of squares and products over the rationals](sum-of-squares-semantics.md)

## Sources

- [Appendix C.1](../../sources/syntax-locators.md#appendix-c1-scalar-nodes)
- [Section 3](../../sources/syntax-locators.md#section-3-point-codes)
