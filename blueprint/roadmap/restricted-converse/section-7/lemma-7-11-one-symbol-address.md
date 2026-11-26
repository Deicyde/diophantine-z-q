---
article_id: af_0c6c5ab9c8312f5cd00e7765
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Symbols.one_symbol_address
---

# Lemma 7.11: one symbol with a stationary base

Assume that $A$ satisfies [the coefficient rules](lemma-7-6-coefficient-rules.md). Let $\Gamma$ be a
nonempty compatible typed graph whose terminal polynomial is nonzero, all of whose vertices are
stationary, and let $b\ge1$. Then there is a compatible $\Gamma'\supseteq\Gamma$ such that:

- the vertices of $\Gamma$, their types and their mutual bits are unchanged;
- every new vertex has type $0$ (it is primary) and a nonzero activation $\lambda\in\mathbb F_2^b$;
- $A(\Gamma'_x)=1$ at every address $x\ne0$, where $\Gamma'_x$ keeps the vertices present at $x$.

No new vertex is present at $x=0$. Only the incidences of the new vertices are chosen.

The Lean statement is about abstract typed graphs. It has no filter hypothesis: a symbol that vanishes
off its filter has a nonzero terminal polynomial only on the filter. The manuscript's clauses on prime
representatives and on choosing the theta stage before them are not part of the statement; primes are
chosen afterwards, by [finite realization](lemma-7-7-finite-realization.md). Extra splitting conditions
are part of the types. The reduction of Theorem 5.3 does not use this theorem: the cubes of units are
a clause of the field `PreLeaves.even_upper` of [the remaining hypotheses](../remaining-hypotheses.md).

**Proof sketch.** As in the manuscript, this is the one-symbol case of the network construction of
Appendix G. A degree count on the top form of the terminal polynomial, taken in the ordinary
polynomial ring before Boolean reduction, selects a set of programs. One network of new primary
vertices is installed for each program, singular networks isolating prescribed derivatives and varying
networks supplying differences, and gluing them makes the symbol one at every nonzero address. In the
stationary case the networks attach to a fixed vertex of $\Gamma$, so no activation anchors are needed.

## Depends on

- [Section 7: addresses and terminal polynomials](README.md)
- [Lemma 7.6: the coefficient rules](lemma-7-6-coefficient-rules.md)

## Sources

- [Section 7](../../../sources/manuscript.md#section-7)
