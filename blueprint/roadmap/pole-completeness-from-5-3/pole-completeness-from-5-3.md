---
article_id: af_d6f273f9b995f5e9f4b210c0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.PoleS12.SilvermanRank.poleCompleteness_of_rankOne
---

# Theorem 5.2 from Theorem 5.3

Assume Theorem 5.3, the Cassels–Tate pairing on the curves $E_\ell$ and Silverman's rank-one implication, as in
[the cited inputs](cited-inputs.md). Then pole completeness holds: the manuscript's Theorem 5.2, for the
manuscript's pole polynomial.

This is the manuscript's derivation in Section 5.1. `ZInQ.OneProof.frozenTarget` derives pole
completeness through it from its hypotheses `hRC`, `hCT` and `hRank` and passes the result to
[the main theorem by Elliot's route](../main/main-theorem.md).

**Proof sketch.** Lemma 5.4 at the curves $E_\ell$ follows from the pairing. With Theorem 5.3 it gives
analytic rank $1$, and Silverman's implication gives rank $1$; together these give $\mathrm{CR}_M$, and
$\mathrm{CR}_M$ with the simultaneous construction gives Theorem 5.2.

## Depends on

- [Pole completeness](../statements/pole-completeness.md)
- [Theorem 5.3: the restricted converse](../restricted-converse/restricted-converse.md)
- [The cited inputs: the Cassels–Tate pairing and Silverman's rank-one implication](cited-inputs.md)

## Proof depends on

- [Lemma 5.4 from the Cassels–Tate pairing](lemma-5-4.md)
- [CR_M from Theorem 5.3, Lemma 5.4 and Lemma 5.5](crm.md)
- [The simultaneous construction](simultaneous-construction.md)
- [Theorem 5.2 from CR_M and the simultaneous construction](pole-completeness-from-crm.md)

## Sources

- [Theorem 5.2](../../sources/manuscript.md#theorem-52)
- [Theorem 5.3](../../sources/manuscript.md#theorem-53)
- [Section 5.1](../../sources/manuscript.md#section-51)
