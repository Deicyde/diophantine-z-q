# metrization (2026-11-13)

**Verdict.** None of the three targets (copied verbatim from scratch/g0-heightadd/; `Base.lean` is
byte-identical to `HeightAdd.lean`) is false or vacuous.
- `MetrizationDimUnique`: **proved, no hypotheses** (`ZInQ.Metrization.metrizationDimUnique`).
  For g, g' ≥ 1 a new Mathlib-only lemma (`eq_of_finrank_one`: `F ⊗_R ⋀^g C` is a line for at most
  one g ≥ 1 when F is a field and a flat R-algebra); g = 0 < g' is excluded by the uniformizations.
- `MetrizationExists`: **reduced** to def-faltings' `HodgeLatticeTheorem`, the leaf
  `AnalyticUniformizationOfDim` (uniformization theorem at g = dim A) and the glue
  `JacDetNondegenerate` (`metrizationExists_of'`). The glue `JacDetDescends` (the Jacobian
  determinant descends to a τ-semilinear map on the Hodge line) is **proved outright** from
  Mathlib's scheme API (evaluation at complex points, stalk maps, ΓSpecIso naturality) and calculus.
- `ProductMetrizationGeo`: **reduced** to two pure algebraic-geometry Props, `ProductLocalStructure`
  (affine product charts at complex points) and `ProductHodgeLattice` (ω of a product, multiplicative
  index) (`productMetrizationGeo_of_local`). Proved along the way: `ProductLatticeFacts` (product
  lattices, covolumes multiply), the product uniformization (algebraic half outright, analytic half
  from `ProductLocalStructure`), and `ProductJacobian` (block-diagonal Jacobian).
- Finding: `ProductMetrizationGeo` asks for exact equality of coefficients, so `MP` must be built
  from the product uniformization (any other one changes `c s` by a complex unit).

**Compiles.** `bash scratch/metrization/build.sh && lake env lean scratch/metrization/Metrization.lean`
gives 0 errors, no sorry, and every `#print axioms` = [propext, Classical.choice, Quot.sound]
(VERIFIED).
`HSyn.G0Split.heightAdditivity_of_metrization_v3 : N1 → LeafAdopt.H5 → AnalyticUniformizationUnique
→ HodgeLatticeTheorem → AnalyticUniformizationOfDim → JacDetNondegenerate → ProductLocalStructure →
ProductHodgeLattice → HeightAdditivity`. Integration check (`build_integrated.sh`: all parts
appended to the full leaf-bundle file, closed with `r.h5`): compiles, 0 errors (VERIFIED).

**Remains.** Open glue (the leaf `AnalyticUniformizationOfDim` is cited, not glue): `JacDetNondegenerate` (needs the complex-manifold structure of A(ℂ)),
`ProductLocalStructure` (needs affine opens of fibre products and sections on basic opens), and
`ProductHodgeLattice` (needs stalks and differentials of fibre products). Not targets of this task:
`AnalyticUniformizationUnique` and `HodgeLatticeTheorem` (def-faltings). Report:
docs/research/metrization.md; log: scratch/metrization/log.md.
