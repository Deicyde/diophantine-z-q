---
article_id: af_963856b1e33d072e7a3f2ced
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.GlueSweep.Ana.nonvanishing_even_of_prints, ZInQ.Manuscript.RC.GlueSweep.Ana.nonvanishing_odd_of_prints
---

# Proposition 7.3: nonvanishing in a signed unit filter

Assume modularity in newform form (`ModularNewform`, which follows from [the cited
results](../printed-results.md) and four fields of [the remaining hypotheses](../remaining-hypotheses.md),
`RCLeaves.modularNewform`); in the even case, the theorem of Hoffstein and Luo (the field
`RCLeaves.hlPrint`); in the odd case, clauses (i) and (ii) of the theorem of Bump, Friedberg and
Hoffstein (`BFHTheorem`, a printed result that is not an input of the reduction of Theorem 5.3). The
twisted functional equation and the absolute convergence of $L(E,s)$ on $\operatorname{Re}s>3/2$, also
hypotheses of the Lean theorems, are proved.

Let $E/\mathbb Q$ be an elliptic curve. A signed unit filter $\Phi$ is a finite set $S$ of primes, a sign,
and a unit squareclass at each $p\in S$; $u\in\Phi$ means that $u\ne0$ has the sign and lies in the
prescribed class of $\mathbb Q_p^\times$, a $p$-adic unit, at each $p\in S$. Suppose $2\in S$ and $S$
contains every prime of bad reduction, and let $B$ be a finite set of primes.

1. If $w(E^{(u)})=+1$ for every squarefree $u\in\Phi$, there is a squarefree $u\in\Phi$ prime to $B$ with
   $\omega(u)\le5$ and $L(E^{(u)},1)\ne0$.
2. If $w(E^{(u)})=-1$ for every squarefree $u\in\Phi$, there is an odd squarefree $u\in\Phi$ prime to $B$
   with $\operatorname{ord}_{s=1}L(E^{(u)},s)=1$.

The manuscript fixes $E=E_\ell$, puts $3$ in $S$, and speaks of the root number of the filter; the Lean
statement takes any $E$, and its hypothesis on the root number is about every squarefree parameter of
the filter. The manuscript's root-number check shows that one parameter suffices.

**Proof sketch.** Choose by Dirichlet's theorem a signed prime $q_0$ in the prescribed classes, outside
$S\cup B$. Apply Hoffstein–Luo (even case) or the simple-zero clause of Bump–Friedberg–Hoffstein (odd
case) to $E^{(q_0)}$, with a positive discriminant $d$ split at $S\cup B\cup\{|q_0|\}$ and at the
conductor primes. Then $q_0d$ lies in the filter, and Hoffstein–Luo gives at most four primes in $d$,
so at most five in all.

## Depends on

- [The cited results](../printed-results.md)
- [The remaining hypotheses](../remaining-hypotheses.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
