# Scholze comparison handoff

**VERIFIED:** `ScholzeH1Narrow` restricts the added comparison row to
abelian surfaces. All three clauses remain: the de Rham assertion, both
filtration bounds, and the rank of `Fil¹`. G9 uses them at one local
surface; downstream C8 uses G9's weights at 5. The dimensionless HT
argument reaches a discarded slot. `narrow_of_abVar` specializes the old
proposition, and `narrow_iff_abSurf` identifies the result with the
existing surface form.

The contribution, its reader examples, and the generated H chain compile.
The dry run traversed the types and proof values below the old and
proposed H tops and headlines. The all-dimension proposition is present
under both old tops and absent under both proposed tops. The direct de
Rham, Tate duality, Conrad, and Berger inputs are present in all four
closures. Every new theorem checked uses only `propext`,
`Classical.choice`, and `Quot.sound`.

The proposed replacement leaves 33 H hypotheses (5 LEAF / 28 GLUE) and
37 headline hypotheses (5 LEAF / 32 GLUE) under both scoring rules. The
row stays **consequence**, **GLUE / GLUE**, **pending review**. No fold
was applied. The report is `docs/research/scholze-narrow.md`; the proposed
row, generator, dry-run output, and replay instructions are in
`scratch/scholze-narrow/`.

The comparison itself remains open. Manuscript L10996 gives the Hodge
numbers without a citation. The surface row explicitly asks for
`dim_F Fil¹ = 2`; the checked proof obtains the other multiplicity from
total dimension and the filtration bounds. The Scholze locators and
comparison dictionaries still need review.
