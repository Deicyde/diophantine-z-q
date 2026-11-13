---
article_id: af_395622cd27cfa2cf768d9408
---

# Natural constructions and the power interface

The compiler writes its conditions as formulas over integer polynomials with fresh
natural witnesses: equality is a difference, conjunction a sum of squares, disjunction a
product, and strict inequality, divisibility, congruence and oddness are single equations
with fresh witnesses.

- [Natural constructions and their macros](natural-constructions.md)
- [The equational gadgets over the naturals](natural-atom-gadgets.md)

Over the naturals a compiled formula vanishes exactly where it holds, and the existential
quantifiers over the witnesses of different conjuncts separate.

- [Compilation and private witnesses over the naturals](natural-compilation.md)

The power template is the compiled power macro: three parameters, $79$ witnesses, $474$
nodes. Its natural zeros are exactly the triples with $P=Q^R$. With it, every macro means
what it should.

- [The power template](power-template.md)
- [Semantics of the power template](power-template-semantics.md)
- [Semantics of the natural macros](macro-semantics.md)

A natural circuit denotes a polynomial, a call node denoting literal substitution into the
power template on a private block; its natural relation quantifies over natural witnesses.
A hierarchical construction yields a well-scoped circuit whose relation is the conjunction
of its macro relations.

- [Natural semantics of a natural circuit](natural-circuit-semantics.md)
- [Circuits of hierarchical constructions](hierarchical-calls.md)
