# vert-witness results log

Base: wip/vert-witness (8ec80711) + merge of origin/wip/hecke-rest (1b5849e0).
Target: `HeckeRestNV.HeckeVertWitness` (scratch/hecke-rest/NoVert.lean, verbatim).

## Plan (route GR)
1. `VertGaussWitness E p` (valuation-subring form: a valuation ring of E whose restriction to
   ℤ[X] is the Gauss valuation at p and in which p generates the maximal ideal) ⇒
   `VertLocalWitness` (hecke-rest) ⇒ `VertUnramWitness`. Commutative algebra, to compile.
2. Leaf `ShimuraGoodReduction`: smooth proper model of Y₃ over ℤ_(p), p > 324, with the
   universal family, moduli bijection on ℚ̄-points, Hecke automorphisms over ℤ_(p).
3. Glue `ModelGaussGlue`: leaf data + triple + E ⇒ `VertGaussWitness E p`.
4. Composite `heckeVertWitness_of_goodReduction`.

## Step 1 (17:58) — VERIFIED (lake env lean, 0 errors, ~12 s)
`VertWitness.lean` = NoVert.lean (lines 1-1265) + `VertMain.lean.part` (assemble.sh).
- `vertLocalWitness_of_gauss : VertGaussWitness E p → VertLocalWitness E p` (p prime)
- `vertUnramWitness_of_gauss`, `heckeVertWitness_of_gauss : HeckeVertGauss → HeckeVertWitness`
- leaf `ShimuraGoodReduction` (stated; data `ShimuraSmoothModel p` over `Zloc p = ℤ_(p)`)
- glue `ModelGaussGlue` (stated, unproved)
- `heckeVertWitness_of_goodReduction (hL : ShimuraGoodReduction) (hG : ModelGaussGlue) : HeckeVertWitness`
All #print axioms: [propext, Classical.choice, Quot.sound].

## Step 2 (18:02) — VERIFIED (lake env lean, 0 errors)
Split of the GR glue:
- `IsShimuraModel p 𝒴 𝒜` (clauses of the leaf), `ShimuraSmoothModel p := ∃ 𝒴 𝒜, IsShimuraModel p 𝒴 𝒜`
- `VertDVRWitness E p` (DVR R ↪ E, Frac = E, 𝔪 = (p), 𝔪 ∩ ℤ[X] = pℤ[X])
- `vertGaussWitness_of_DVR : VertDVRWitness E p → VertGaussWitness E p` (compiled)
- glue `SpecialFibreDVR` (scheme theory: some stalk of a nonempty proper smooth rel-dim-1
  ℤ_(p)-scheme is a DVR with 𝔪 = (p)), glue `ModelCoordinateGlue` (comparison + coordinate)
- `modelGaussGlue_of : SpecialFibreDVR → ModelCoordinateGlue → ModelGaussGlue` (compiled;
  nonemptiness of 𝒴 from R1fp's ℚ̄-point + leaf surjectivity)
- `heckeVertWitness_of_goodReduction' (hL) (hC) (hBD) : HeckeVertWitness` (compiled)
All #print axioms [propext, Classical.choice, Quot.sound].

## Step 3 (18:07) — VERIFIED (lake env lean, 0 errors, 1m17s)
`VertAll.lean` = HeckeRestAll.lean (verbatim, all 9854 lines) + VertMain + `VertAllMain.lean.part`:
- `VertWitnessAll.coverModelOfHecke_of_goodReduction (hconn) (hRR) (hT) (hA) (hS) (hW)
   (hL : ShimuraGoodReduction) (hC : SpecialFibreDVR) (hBD : ModelCoordinateGlue) : CoverModelOfHecke`
- `VertWitnessAll.propTSAll_of_goodReduction ... : PropTSAll`
Axioms standard (compile_all.txt). Copy check: `cmp` of NoVert.lean lines 1-1265 vs VertWitness.lean: identical.

## Step 4 (18:16) — VERIFIED (both files 0 errors; VertAll 57 s)
- `dvr_of_maximalIdeal_eq_span` (Mathlib-only): Noetherian local ring, 𝔪 = (t), t ∈ R⁰ ⇒ IsDomain ∧ DVR.
- glue `SpecialFibreUniformizer` (∃ ξ, 𝔪_ξ = (p), p ∈ R⁰ in the stalk) and
  `specialFibreDVR_of_uniformizer : SpecialFibreUniformizer → SpecialFibreDVR` (stalks Noetherian via
  `LocallyOfFiniteType.isLocallyNoetherian`).
- `heckeVertWitness_of_goodReduction'' (hL) (hU : SpecialFibreUniformizer) (hBD) : HeckeVertWitness`.
- Composites in VertAll now take `hU : SpecialFibreUniformizer`.
- Leaf: guard clause `Nonempty (Spec ℚ̄ ⟶ 𝒴.left)` added (reviewer); references reordered
  (Kottwitz, Buzzard first; Carayol's main construction is for F ≠ ℚ).
- Review (read-only model agent): leaf TRUE as a weaker consequence; SpecialFibreDVR TRUE;
  ModelCoordinateGlue TRUE (fix: disjointness of CM sections via finite étale fixed loci, not
  Hurwitz — applied); VertGauss/VertDVR no hidden triviality.
- cmp: VertWitness.lean lines 1-1265 = NoVert.lean 1-1265; VertAll.lean lines 1-9854 = HeckeRestAll.lean.

## Step 5 (18:22) — VERIFIED (VertWitness.lean and VertAll.lean, 0 errors; VertAll 58 s)
Split of `ModelCoordinateGlue` into
- `CoordFibres 𝒴 𝒜 ρ` (R2fp-type clauses for ρ : ToP1 𝒴.left on ℚ̄-points, via IsFibreOf),
- glue (d) `ModelCoordinate`: ∃ ρ with CoordFibres, regular at every ξ (DVR, 𝔪 = (p)) with
  `f(germ ρ.f) ∈ 𝔪_ξ ↔ f ∈ pℤ[X]`,
- glue (b) `ModelComparison`: ∀ ρ with CoordFibres, ∀ ξ ∈ ρ.U, ∃ ι : stalk ξ ↪ E, Frac = E,
  ι(germ ρ.f) = X,
- `intPolyAlg_eq_eval₂`, `modelCoordinateGlue_of : ModelCoordinate → ModelComparison →
  ModelCoordinateGlue` (compiled),
- `heckeVertWitness_of_goodReduction₃ (hL) (hU) (hD) (hB) : HeckeVertWitness`,
- `VertWitnessAll.coverModelOfHecke_of_goodReduction₃` (compiled).
(`Π` is a reserved token; the map is named `ρ`.)

## Step 6 (18:25) — VERIFIED (both files 0 errors; VertAll 57 s)
- `CMObjectsExist` (CM objects of the three types over ℚ̄) and
  `cmObjectsExist_of_R1R2fp : R1R2fp → CMObjectsExist` (compiled: CMExists + X6Surj + X6Props + of_iso).
- `CMObjectsExist →` threaded as a hypothesis into ModelGaussGlue, ModelCoordinateGlue,
  ModelCoordinate, ModelComparison (the coordinate's normalization by the three CM orbits needs
  CM points; otherwise the CM clauses of CoordFibres/R2fp would be vacuous and (b) unprovable
  as a closed theorem).
- Composites now take `hRR : R1R2fp` (a bundle leaf):
  `heckeVertWitness_of_goodReduction₃ (hL) (hRR) (hU) (hD) (hB) : HeckeVertWitness`, etc.

## Step 7 (18:31) — VERIFIED (both files 0 errors, no sorryAx in compile_*.txt)
- `natCast_ne_zero_stalk_Spec`, `natCast_mem_nonZeroDivisors_stalk` (p regular in every stalk of a
  flat ℤ_(p)-scheme; Flat.stalkMap + Module.Flat.isSMulRegular_of_nonZeroDivisors).
- glue `SpecialFibreMaxIdeal` (∃ ξ, 𝔪_ξ = (p)); `specialFibreUniformizer_of_maxIdeal` (compiled).
- finest composites: `heckeVertWitness_of_leaves (hL) (hRR) (hMI) (hD) (hB)`,
  `VertWitnessAll.coverModelOfHecke_of_leaves`.
- Second review (read-only agent): ModelCoordinate TRUE (every qualifying ξ), ModelComparison TRUE
  (every ρ, ξ ∈ ρ.U), SpecialFibreUniformizer TRUE, CMObjectsExist fine, split not circular.
  Docstrings updated (Möbius factorization proof of (b); tameness for p ≥ 5; reliance on the
  stabilizer orders 4, 6, 2).

## Step 8 (18:39) — VERIFIED (both files 0 errors, no sorryAx)
- `maximalIdeal_eq_map_of_mem_minimalPrimes` (Mathlib only): I radical, 𝔮 ∈ I.minimalPrimes ⇒
  𝔪_{A_𝔮} = I·A_𝔮.
- `maximalIdeal_Zloc`: 𝔪_{ℤ_(p)} = (p).
- textbook statement `SmoothFibreReduced` (φ : R → A smooth, m maximal ⇒ mA radical).
- `specialFibreMaxIdeal_of : SmoothFibreReduced → SpecialFibreMaxIdeal` (compiled: closed image
  contains the closed point; affine chart V; appLE smooth (HasRingHomProperty.appLE); maximal ideal
  of Γ(Spec ℤ_(p), ⊤) = (p) via ΓSpecIso; minimal prime 𝔮 of pA under 𝔭_x
  (comap_primeIdealOf_appLE); ξ = fromSpec 𝔮; isLocalization_stalk').
- finest composites: `heckeVertWitness_of_leaves (hL) (hRR) (hSR : SmoothFibreReduced) (hD) (hB)`,
  `VertWitnessAll.coverModelOfHecke_of_leaves` (same inputs + hecke-rest's leaves).

## Final state (18:41)
Finest compiled results:
- `VertWitness.heckeVertWitness_of_leaves (hL : ShimuraGoodReduction) (hRR : R1R2fp)
   (hSR : SmoothFibreReduced) (hD : ModelCoordinate) (hB : ModelComparison) : HeckeVertWitness`
- `VertWitnessAll.coverModelOfHecke_of_leaves` (hecke-rest's leaves + hL hSR hD hB).
Open: leaf ShimuraGoodReduction (literature; locators UNVERIFIED), textbook SmoothFibreReduced
(commutative algebra, missing in Mathlib), glue ModelCoordinate (tame quotient) and
ModelComparison (generic fibre comparison + Möbius rigidity). Both glue Props reviewed TRUE.
