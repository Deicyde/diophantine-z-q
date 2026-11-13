# metrization (2026-11-13)

**Verdict.** None of the three targets (copied verbatim from scratch/g0-heightadd/; `Base.lean` is
byte-identical to `HeightAdd.lean`) is false or vacuous.
- `MetrizationDimUnique`: **proved, no hypotheses** (`ZInQ.Metrization.metrizationDimUnique`).
  For g, g' ≥ 1 a new Mathlib-only lemma (`eq_of_finrank_one`: `F ⊗_R ⋀^g C` is a line for at most
  one g ≥ 1 when F is a flat R-algebra and a field); g = 0 < g' is excluded by the uniformizations.
- `MetrizationExists`: **reduced** to def-faltings' `HodgeLatticeTheorem`, the leaf
  `AnalyticUniformizationOfDim` (uniformization theorem at g = dim A) and the glue
  `JacDetNondegenerate` (`metrizationExists_of'`). The glue `JacDetDescends` (the Jacobian
  determinant descends to a τ-semilinear map on the Hodge line) is **proved outright** from
  Mathlib's scheme API (evaluation at complex points, stalk maps, ΓSpecIso naturality) and calculus.
- `ProductMetrizationGeo`: **reduced** to `ProductUniformizationAnalytic` (openness/holomorphy for
  the product uniformization) and `ProductHodgeLattice` (`ω` of a product, multiplicative index)
  (`productMetrizationGeo_of'''`). Proved on the way: `ProductLatticeFacts` (product lattices,
  covolumes multiply), the algebraic half of the product uniformization, `ProductJacobian`
  (block-diagonal Jacobian).
- Finding: `ProductMetrizationGeo` asks for exact equality of coefficients, so `MP` must be built
  from the product uniformization (any other changes `c s` by a unit complex number).

**Compiles.** `bash scratch/metrization/build.sh && lake env lean scratch/metrization/Metrization.lean`:
0 errors, no sorry, all `#print axioms` = [propext, Classical.choice, Quot.sound] (VERIFIED).
`HSyn.G0Split.heightAdditivity_of_metrization_v2 : N1 → LeafAdopt.H5 → AnalyticUniformizationUnique
→ HodgeLatticeTheorem → AnalyticUniformizationOfDim → JacDetNondegenerate →
ProductUniformizationAnalytic → ProductHodgeLattice → HeightAdditivity`.

**Remains.** Glue: `JacDetNondegenerate` (complex-manifold structure of A(ℂ)),
`ProductUniformizationAnalytic` (affine covers of fibre products), `ProductHodgeLattice`
(stalks/differentials of fibre products). Not targets here: `AnalyticUniformizationUnique`,
`HodgeLatticeTheorem` (def-faltings). Note: docs/research/metrization.md; log scratch/metrization/log.md.
