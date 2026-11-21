---
article_id: af_2c0491819a8ce4711eff5e68
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Contrib.CloudB3RC53.CoefficientDictionary.coefficientRules_symb, ZInQ.Contrib.CloudB3RC53.CoefficientDictionary.rulesUpTo_symb, ZInQ.Manuscript.RC.Symbols.limSymbol_rules, ZInQ.Manuscript.RC.Symbols.CoefficientRules
---

# Lemma 7.6: the coefficient rules

A function $A$ from typed graphs to $\mathbb F_2$ *satisfies the coefficient rules* if, for every
compatible typed graph $\Gamma$:

1. (graph dependence) $A(\Gamma)=A(\Delta)$ for every typed graph $\Delta$ isomorphic to $\Gamma$;
2. (contraction) for distinct vertices $v,w$, $A(\Gamma)+A(\Gamma')=A(\Gamma/(v,w))$, where $\Gamma'$ is
   $\Gamma$ with the bit of the pair $v,w$ changed (and its reverse bit with it);
3. (primary isolation) if a vertex has type $0$ and zero incidences with every other vertex, then
   $A(\Gamma)=0$.

Assume type data for primes (types read from reduced residue classes modulo an even $m$, with sign
coordinate $(p-1)/2\bmod2$), a reading $R$ of finite sets of good primes, and the readings of
Appendix F on prime sets: the reading of a new prime depends only on its type and its residue bits with
the others (`FixedUFactorization`), (O.12) at coefficient one with the product-label rule
(`O12Reading`), a fresh vertex of trivial type and bits reads zero (`PrimaryReading`), and $a_p$ is even
at every good prime (`ApEven`). These are named inputs, not proved.

- If the readings hold at every budget, the symbol $\operatorname{symb}(T,R)$ (the reading of any prime
  realization of a typed graph) satisfies the coefficient rules.
- If they hold within the budget $W+1$, the rules hold on typed graphs with at most $W+1$ vertices.
- If, for every cutoff $W$, the stage symbols satisfy the rules up to $W$ on a set of stages in an
  ultrafilter, then their limit symbol satisfies the rules.

The first case is the even symbol, the second one odd stage and the third the stabilized odd symbol.
Whole-prime omission is built in: one function on all typed graphs reads every configuration, including
those with a prime omitted. The budget of the manuscript is a bound on the number of vertices.

**Proof sketch.** The manuscript refers to Appendix F. Graph dependence: two isomorphic graphs have
prime realizations with the same reading, since the reading of a new prime sees only its type and bits.
Contraction: the omission identity (O.12) relates the readings with $q$ and with its inertia twist to
those of two fresh primes carrying the summed type and bits; in the full two-torsion case $a_p$ is
even, so the contraction coefficient is one. Primary isolation is the corresponding reading. The limit
symbol inherits each rule, since each instance involves finitely many configurations.

In the Lean proof of Theorem 5.3 the rules for the even sources are a clause of the field
`PreLeaves.aux_factor` of [the remaining hypotheses](../remaining-hypotheses.md), and the odd readings
enter through `PostLeaves.address`.

## Depends on

- [Section 7: typed graphs and coefficient symbols](README.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
