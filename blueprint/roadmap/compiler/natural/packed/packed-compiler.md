---
article_id: af_738de6afc9fccd49f79ecbf9
declaration: def
origin: cited
statement: formalized
lean: ZInQ.Compiler.Packed.construction, ZInQ.Compiler.Packed.compiled
---

# The packed-history construction

Let $p=(p_0,\dots,p_{m-1})$ be a primitive program valid for $r$ registers and let
$1\le k\le r$. The *packed-history construction* of $p$ is the natural construction in
hierarchical mode with $k$ inputs $a_0,\dots,a_{k-1}$ ($=X_0,\dots,X_{k-1}$) which takes the
fresh variables
$$q,\ c,\ K,\ B,\ T,\ F,\ D,\qquad R_0,\dots,R_{r-1},\qquad N_0,\dots,N_{r-1},\qquad
S_0,\dots,S_{m-1}$$
in this order and returns the conjunction of the following formulas, in this order:

1. $\mathrm{lt}(0,c)$, $\mathrm{power}(K,2,c)$, $B\doteq4K$, $\mathrm{lt}(m,B)$,
   $\mathrm{power}(T,B,q)$, then $\mathrm{lt}(a_i,K)$ for $i<k$;
2. $BF+1\doteq F+BT$, $D+F\doteq KF$, $S_0+\dots+S_{m-1}\doteq F$, $S_{m-1}\doteq T$;
3. $\mathrm{mask}(S_i,F)$ for $i<m$;
4. for each $j<r$: $\mathrm{mask}(R_j,D)$, $\mathrm{lt}(R_j,T)$,
   $\mathrm{bitAnd}(K\cdot N_j,\ R_j+D,\ K\cdot F)$;
5. for each sub instruction $p_i=\mathrm{dec}(j,x,y)$, in increasing $i$: fresh $V_i,W_i$, then
   $\mathrm{bitAnd}(V_i,S_i,N_j)$ and $S_i\doteq V_i+W_i$;
6. for each $j<r$: $R_j+B\cdot C_j\doteq\iota_j+B\cdot R_j+B\cdot A_j$, where $\iota_j=a_j$ for
   $j<k$ and $0$ otherwise, $A_j=\sum_{i:\,p_i=\mathrm{inc}(j,\cdot)}S_i$ and
   $C_j=\sum_{i:\,p_i=\mathrm{dec}(j,\cdot,\cdot)}V_i$;
7. for each $i<m$: $S_i\doteq[i=0]+B\cdot I_i$, where $I_i$ is the sum, in program order, of
   $S_{i'}$ for $p_{i'}=\mathrm{inc}(\cdot,i)$, of $V_{i'}$ for $p_{i'}=\mathrm{dec}(\cdot,i,\cdot)$
   and of $W_{i'}$ for $p_{i'}=\mathrm{dec}(\cdot,\cdot,i)$ (for a sub instruction its nonzero
   target is listed before its zero target).

Empty sums are the constant $0$. The *compiled circuit* $\mathcal C_{p,k}$ is the natural
circuit of this construction. Here $R_j$ is the packed history of register $j$, $S_i$ that
of state $i$, $N_j$ the packed nonzero indicator, $V_i,W_i$ the nonzero and zero branch
histories, and $F=F_q=1+B+\dots+B^q$, $D=(K-1)F_q$ by item 2.

This is a definition. No equation is repeated $q$ times: $q$ is one variable and the
number of conjuncts depends only on $p$.

## Depends on

- [Register machines](../programs/register-machine.md)
- [Natural constructions and their macros](../formulas/natural-constructions.md)
- [Natural semantics of a natural circuit](../formulas/natural-circuit-semantics.md)

## Sources

- [Section 10.1 packed histories](../../../../sources/compiler-natural-locators.md#section-101-packed-histories)
- [Section 10.1 nonzero and branch masks](../../../../sources/compiler-natural-locators.md#section-101-nonzero-and-branch-masks)
- [Section 10.1 transition equations](../../../../sources/compiler-natural-locators.md#section-101-transition-equations)
- [Compiler specification](../../../../sources/compiler-natural-locators.md#compiler-specification)
- [Compiler source](../../../../sources/compiler-natural-locators.md#compiler-source)
