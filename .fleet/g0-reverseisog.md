# g0-reverseisog (fleet note)

**Result: `ReverseIsogeny` (G17 after Poincaré) is proved in Lean**, with its statement unchanged.
The proof uses the bundle's research leaf R19 (Gaudron-Rémond: isogenies in both directions), H5's
finiteness (`r.h5.1`) and piece 1 `DimFinite`. It adds no new leaf:
`HSyn.G0RevIsog.reverseIsogeny_of_leaves (r : ResearchLeaves) (hDimF : DimFinite) : ReverseIsogeny`.
So `HSyn.glueOutputs_of_leaves_rev` and `HSyn.sixContactMin_of_leaves_rev` need **nine** glue
pieces instead of ten.

A second route is independent of heights and of `DimFinite`. It needs one textbook leaf,
`IsogenyQuasiInverse` (Mumford §7, Milne AV I §7, numbers UNVERIFIED): an isogeny `φ` has an
isogeny `ψ` back, with `ψφ = [n]` and `φψ = [n]`. The theorem is
`G0RevIsog.reverseIsogeny : IsogenyQuasiInverse → ReverseIsogeny`.

Proved glue:
- `isogeny_of_product`: `f∘p₁ + g∘p₂ : P → J` is an isogeny.
- `topologicalKrullDim_le_of_specializing` (general topology): a continuous, specializing,
  surjective map to a quasi-sober space does not lower Krull dimension.
- `dim_le_of_finite_surjective`.
- `dim_eq_of_isogenies`: gives `dim J = dim P` from isogenies both ways, with no new leaf.

What compiles (VERIFIED):
- `scratch/g0-reverseisog/ReverseIsogeny.lean` (imports only Mathlib, 0 errors).
- `scratch/g0-reverseisog/SplitRev.lean`: Split.lean at wip/g0-split c20fa62b, byte-identical,
  plus §3″. 0 errors, no `sorry`, 2m57s. `#print axioms` gives `propext`, `Classical.choice`,
  `Quot.sound` for `reverseIsogeny`, `reverseIsogeny_of_leaves`, `glueOutputs_of_leaves_rev` and
  `sixContactMin_of_leaves_rev`.

What remains:
- Route B depends on `DimFinite` (task g0-dim) and inherits H5's definitional caveat.
- Route A's leaf needs quotients by finite group schemes, which Mathlib does not have.
- The integration into the merged Split.lean has not been compiled.

Report: docs/research/g0-reverseisog.md.
