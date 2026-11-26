---
article_id: af_546c4f2413398cbcf9ca1e1d
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: ZInQ.Manuscript.RC.Symbols.odd_stabilization, ZInQ.Manuscript.RC.Symbols.odd_stabilization_witness
---

# Proposition G.5: one table per cutoff on the ultrafilter

Let $\mathcal L$ be a finite alphabet (an additive group) with sign coordinate $\epsilon$, $\mathcal U$ an
ultrafilter on the stages, and $A_\theta$ a symbol on typed graphs over $\mathcal L$ at each stage $\theta$.
Assume (ELLIOT: Lemma 7.6 gives it for the odd stages from the readings of Appendix F) that
for every cutoff $W$, for $\mathcal U$-many $\theta$, $A_\theta$ satisfies [the coefficient
rules](../section-7/lemma-7-6-coefficient-rules.md) on compatible typed graphs with at most $W+1$
vertices. Then there is a symbol $A_\infty$ on all typed graphs such that:

- $A_\infty$ satisfies the coefficient rules;
- for every finite list of compatible typed graphs, $A_\theta$ agrees with $A_\infty$ on the list for
  $\mathcal U$-many $\theta$, so in particular at one actual stage;
- a compatible typed graph with $A_\theta=1$ for $\mathcal U$-many $\theta$ has $A_\infty=1$, so the
  bounded-weight witness remains a witness.

$A_\infty$ is the intrinsic odd symbol; in the proof it takes at each typed graph the value that the
stage symbols take on a set in $\mathcal U$. No stage common to all cutoffs is chosen.

The Lean statement fixes one finite alphabet for all stages. The manuscript first stabilizes the
abstract type of the bounded label groups and their projections on a set in $\mathcal U$, a pigeonhole
step that the Lean proves separately (`label_type_stabilizes`). The common alphabet with the
stationary tests of $k$, and the statement that $\delta_o$ does not change, are not part of the Lean
statement.

The reduction of Theorem 5.3 takes the intrinsic odd symbol, its rules and its common stages from
`odd_stabilization`, applied to the stage symbols of the odd source in
`addressPackageZeroTotal_of_staged`; the rules of the stage symbols come from the odd models in the field
`PostLeaves.address` of [the remaining hypotheses](../remaining-hypotheses.md).

**Proof sketch.** For a cutoff $W$, the typed graphs with at most $W+1$ vertices have finitely many
normal forms, so there are finitely many tables, and one of them occurs on a set in $\mathcal U$; on
valid stages graph dependence makes the table determine the symbol on every graph of the cutoff. The
tables of two cutoffs agree on the intersection of their sets, so the limit symbol extends each of
them. A rule instance involves finitely many graphs and holds at the cutoff of their size.

## Depends on

- [Section 7: typed graphs](../section-7/README.md)
- [Lemma 7.6: the coefficient rules](../section-7/lemma-7-6-coefficient-rules.md)

## Sources

- [Appendix G](../../../sources/manuscript.md#appendix-g)
