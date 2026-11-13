# infra-stalks (2026-11-13)

**Verdict.** Five glue Props are now Lean theorems (statements verbatim; whole owner files copied):
height-bc's `CotangentSpanBC` and `UniformizationLiftAnalytic`, metrization's `ProductLocalStructure`,
mul-rigidity's `KerUnitOpenOfCotangentSurj` and `CotangentMulN`. Consequences: the textbook leaf
`G0FibreSimple.MulIsogeny` (GluePieces2 field 1) is a theorem (`MulRigidity.mulIsogeny`);
H4a/`HodgeLineBaseChange` need only `HodgeBCInjective` + `OmegaBaseChange`
(`modelHeightBaseChange_of_two`); `HeightAdditivity` no longer needs `ProductLocalStructure` (`_v4`).

**General Mathlib-only lemmas** (scratch/infra-stalks/): stalk of `X ×_S Y` is the localization of
`𝒪_x ⊗_{𝒪_s} 𝒪_y` at a prime (`pullback_stalk_isLocalization`, both halves); maximal ideal and residue
field of such stalks; cotangent space of a base change by a field extension is `L' ⊗ T*_x`
(`cotangent_span_pullback` + `cotangent_baseChange_injective`); cotangent space of a product at section
points is the direct sum (`sub_mem_sq_pairPt`, pure-algebra core `sub_mem_maximalIdeal_sq_of_product`);
a section through a field-stalk point of a finite-type `k`-scheme is an open immersion; local structure
of fibre products at field-valued points (`exists_localStructure_pullback`).

**What compiles.** Every file in scratch/infra-stalks/*.lean: 0 errors, no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]` (`lake env lean`; regenerate with `assemble_*.py`).

**What remains.** `HodgeBCInjective` (needs `L ⊗_{𝓞_L} ⋀^g_{𝓞_L} V ≅ ⋀^g_L V` for an `L`-space `V`,
plus specializing the cotangent iso to GroupModels), `OmegaBaseChange` (conormal base change at closed
points + Dedekind local–global for the lattices), `ProductHodgeLattice` and S-alg
`ProductMetrizationOfProductUnif` (exterior powers over `𝓞_L`, lattice splitting, `secIndex`
multiplicativity). Report: docs/research/infra-stalks.md.
