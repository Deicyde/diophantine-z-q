---
article_id: af_2dae60f90267c0e9abf015fd
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Compiler.Natural.compile_zv_eq_zero_iff, ZInQ.Compiler.Natural.exists_agree_congr, ZInQ.Compiler.Natural.callPower_spec
---

# Compilation and private witnesses over the naturals

1. For every formula $\varphi$ and every $x:\mathbb N\to\mathbb N$,
   $\kappa(\varphi)(x)=0\iff\varphi$ holds naturally at $x$.
2. Let a natural construction run from counter $c_0$ to counter $c_1$ and produce
   $\varphi$, with all argument polynomials in variables below $c_0$. For $x:\mathbb N\to\mathbb N$
   and $y:[c_0,c_1)\to\mathbb N$ write $x[y]$ for the assignment equal to $y$ on $[c_0,c_1)$
   and to $x$ elsewhere. Then the statement
   $$\exists y:[c_0,c_1)\to\mathbb N,\ \ \varphi\text{ holds naturally at }x[y]$$
   depends only on $x$ below $c_0$. If $\varphi=\bigwedge_i\varphi_i$ where $\varphi_i$ is
   produced on the subinterval $[c_{i-1},c_i)$, it is equivalent to the conjunction of the
   corresponding statements for the $\varphi_i$; if $\varphi=\bigvee_i\varphi_i$, to their
   disjunction, the variables of inactive disjuncts being set to $0$.
3. The same holds when some atoms are power-template calls
   $\langle\mathcal P[P,Q,R;w]\rangle$ with blocks inside $[c_0,c_1)$, pairwise disjoint and
   not occurring in any other atom or argument: the call atom may then be replaced by the
   statement that some values of its block make $\mathcal P$ vanish, quantified inside its
   conjunct.

**Proof sketch.** (1) For integers, a sum of squares vanishes iff every term does and a
product vanishes iff some factor does; induct on $\varphi$ (this is the specification
chapter's statement over $\mathbb Q$ restricted to integer points). (2) Induct on the
construction: atoms and fresh variables are immediate; for a conjunction the intervals of
the conjuncts are disjoint, so witnesses for the conjuncts glue to one $y$ and a common $y$
restricts to each; for a disjunction a witness for the true disjunct is extended by $0$ on
the other intervals, which do not occur in the true disjunct. Nonemptiness of $\mathbb N$ is
what allows existential quantifiers to be pulled across the connectives. (3) is (2) with the
block of each call treated as the interval of a one-atom construction.

## Depends on

- [Natural constructions and their macros](natural-constructions.md)

## Proof depends on

- [Sums of squares and products over the rationals](../../../syntax/sum-of-squares-semantics.md)

## Informally uses

- [Private witness blocks](../../../syntax/language/existential-lifting.md)

## Sources

- [Compiler specification](../../../../sources/compiler-natural-locators.md#compiler-specification)
- [Halting correctness proof](../../../../sources/compiler-natural-locators.md#halting-correctness-proof)
