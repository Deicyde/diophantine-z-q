# model-glue — report (2026-11-13)

**Main result.** Both glue Props of vert-witness are reduced to one textbook leaf, one glue
statement and the existing leaf T5. All the glue in between is proved.

- `ModelGlue.modelComparison_of_curveBijIso (hT : ObjBridge.TorsionStructure)
  (hC : CurveBijIso) : ModelComparison`
- `ModelGlue.modelCoordinate_of_residue (h : ModelCoordinateResidue) : ModelCoordinate`
- `ModelGlue.heckeVertWitness_of_curveBijIso (hL : ShimuraGoodReduction) (hRR : R1R2fp)
  (hT : ObjBridge.TorsionStructure) (hD : ModelCoordinateResidue) (hC : CurveBijIso) :
  HeckeVertWitness`. vert-witness's `SmoothFibreReduced` is no longer an input: it is proved here
  as `smoothFibreReduced'`, using smooth-fibre's proof.

**What compiles.** `scratch/model-glue/ModelGlue6.lean` is
`import ZInQKernel.Contrib.Mobius.Main` + `scratch/vert-witness/VertWitness.lean` (verbatim) +
six part files. `lake env lean` exits 0, with no `sorry` and no `axiom`. All 34 `#print axioms`
lines read `[propext, Classical.choice, Quot.sound]` (`compile6_out.txt`).
`py/verbatim_check.py` prints `ALL OK`. On this host, build `ZInQKernel.Contrib.Mobius.Main`
first.

**Proved outright in this run** (namespace `ModelGlue`):

- `modelGenericFibre : ModelGenericFibre`
- `germOfQbarValues : GermOfQbarValues`
- `smoothFibreReduced' : SmoothFibreReduced`
- `modelIntegral_of (hT : TwistClassFinite) (hC : CurveBijIso) : ModelIntegral`
- `modelFunctionField_of_curveBijIso (hT : TwistClassFinite) (hC : CurveBijIso) :
  ModelFunctionField`

Proved lemmas behind them:

- `exists_genFib_to_Y`: `R1univProps` gives `𝒴_ℚ → Y`, bijective on `ℚ̄`-points.
- `irreducible_of_chart`: `Y` is irreducible.
- `isReduced_of_smooth_zloc`, `irreducibleSpace_of_genFib`: `𝒴` is reduced and irreducible.
- `isOpenImmersion_specRatToZloc`: `ℚ = ℤ_(p)[1/p]`.
- `germ_eq_of_val_eq`, `germ_chart_eq`: Jacobson density for germs.
- `val_eq_of_same_fibres`: Möbius rigidity.
- `ffMap_bijective`: maps of function fields.

**What remains (not proved).**

- `ModelGlue.CurveBijIso` (textbook leaf): a morphism of proper smooth curves over `ℚ` that is
  bijective on `ℚ̄`-points is an isomorphism. The missing step is degree = number of points in a
  general fibre (generic smoothness), which Mathlib 4.35 lacks.
- `ModelGlue.ModelCoordinateResidue` (glue): the coordinate `ρ` of the tame quotient
  `𝒴/Γ' ≅ P¹_{ℤ_(p)}` with `CoordFibres` and transcendental reduction at the generic points of
  the special fibre. Mathlib 4.35 has no quotient schemes and no `P¹_{ℤ_(p)}`.
- T5 (`ObjBridge.TorsionStructure`, existing leaf), used only through `TwistClassFinite`.

Details: docs/research/model-glue.md and scratch/model-glue/log.md. No statement changes are
proposed, and no existing file was edited.
