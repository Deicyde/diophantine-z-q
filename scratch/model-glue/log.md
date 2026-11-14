# model-glue results log

Base: wip/model-glue = wip/integrate-w49 (998b4f79). Targets: `VertWitness.ModelCoordinate`,
`VertWitness.ModelComparison` (scratch/vert-witness/VertMain.lean.part, in VertWitness.lean).
Layout: `ModelGlue.lean` = `scratch/vert-witness/VertWitness.lean` (whole file, verbatim) +
`ModelGlue.lean.part` (assemble.sh). The targets are used by name from the verbatim prefix.

## Step 1 (21:24) — VERIFIED (lake env lean, exit 0, ~85 s; compile_out.txt)
- `intCast_mem_maximalIdeal_iff`: local ring, `p ∈ 𝔪` ⇒ `(c:R) ∈ 𝔪 ↔ p ∣ c`.
- `mem_maximalIdeal_iff_of_transcendental`: local ring, `p ∈ 𝔪`, residue of `r` transcendental over
  `(⊥ : Subfield κ)` ⇒ `f.eval₂ Int.cast r ∈ 𝔪 ↔ f ∈ vertPrime p` (Gauss criterion).
- glue `ModelCoordinateResidue` (ModelCoordinate with the criterion replaced by transcendence of
  the reduction of `ρ` at `ξ`); `modelCoordinate_of_residue : ModelCoordinateResidue → ModelCoordinate`.
- glue `ModelIntegral` (𝒴 integral), glue `ModelFunctionField` (surjection `κ : ℚ(𝒴) → E` with
  `κ(germ_η ρ.f) = X` for every `ρ` with CoordFibres);
  `stalk_embedding_of_functionField` (Mathlib-only: integral X, κ surjective ⇒ stalk embedding with
  fraction field E), `modelComparison_of : ModelIntegral → ModelFunctionField → ModelComparison`.
- composites `modelCoordinateGlue_of_parts`, `heckeVertWitness_of_parts`.
- All 7 `#print axioms`: [propext, Classical.choice, Quot.sound]. No sorry in the part file.
- cmp: ModelGlue.lean lines 1-2140 = scratch/vert-witness/VertWitness.lean: identical.

## Step 2 (21:29) — VERIFIED (ModelGlue2.lean: lake env lean exit 0, ~50 s; compile2_out.txt)
`ModelGlue2.lean` = `import ZInQKernel.Contrib.Mobius.Main` + VertWitness.lean (verbatim; cmp of
lines 2-2141: identical) + ModelGlue.lean.part + ModelGlue2.lean.part.
- glue `ModelGenericFibre` (textbook: base change of 𝒴 to ℚ, proper smooth curve S, j : S → 𝒴
  bijective on ℚ̄-points).
- `coordFibres_val_eq (hT : TwistClassFinite) (hG : ModelGenericFibre) (hM) (hCM) (hρ) (hρ') y :
  ρ.val y = ρ'.val y` — Möbius rigidity on ℚ̄-points, from the proved `LeafQM.AV.Pin.curveFacts`
  (argument of `Pin.mobiusGlue_of_curveFacts` on S; finiteness of fibres from leaf clause 4 +
  TwistClassFinite).
- glue `GermOfQbarValues` (Jacobson density: equal ℚ̄-values ⇒ equal germs at η on integral 𝒴).
- glue `ModelFunctionFieldExists` (∃ one ρ₀ with CoordFibres and κ(ρ₀) = X).
- `modelFunctionField_of : TwistClassFinite → ModelGenericFibre → GermOfQbarValues →
  ModelFunctionFieldExists → ModelFunctionField`;
  `modelComparison_of_parts (hT : ObjBridge.TorsionStructure) (hI) (hG) (hJ) (hE) : ModelComparison`;
  `heckeVertWitness_of_parts₂`.
- All 11 `#print axioms`: [propext, Classical.choice, Quot.sound].

## Step 3 (22:40, 2026-11-13) — VERIFIED (ModelGlue3.lean = ModelGlue2.lean + ModelGlue3.lean.part; lake env lean exit 0, ~15 s once oleans built; compile3_out.txt)
(Needed `lake build ZInQKernel.Contrib.Mobius.Main` first on this host, ~2 min.)
- `zloc_prime_eq_bot`: a prime of `ℤ_(p)` not containing `p` is `⊥` (DVR, uniformizer `p`).
- `zlocToRat : Zloc p →+* ℚ`, `specRatToZloc`, `genFib 𝒴 := Over.mk (pullback.snd 𝒴.hom (specRatToZloc p))`.
- **`modelGenericFibre : ModelGenericFibre` — PROVED** (base change; Hom(ℤ_(p), T) is a singleton).
- `genericPoint_mem_range`: on integral flat 𝒴, η ∈ range (pullback.fst) (p ≠ 0 at η by
  `natCast_mem_nonZeroDivisors_stalk`, so η ∈ D(p) whose points lie over ⊥).
- **`germOfQbarValues : GermOfQbarValues` — PROVED** (Jacobson density on the generic fibre;
  `exists_qbarPt`, `eval_res` copied from period-glue).
- `modelComparison_of_parts₃ (hT : ObjBridge.TorsionStructure) (hI : ModelIntegral)
  (hE : ModelFunctionFieldExists) : ModelComparison`; `heckeVertWitness_of_parts₃`.
- All `#print axioms`: [propext, Classical.choice, Quot.sound].
Open after step 3: `ModelCoordinateResidue`, `ModelIntegral`, `ModelFunctionFieldExists`.

## Step 4 (23:20, 2026-11-13) — VERIFIED (ModelGlue4.lean = ModelGlue3.lean + ModelGlue4.lean.part; lake env lean exit 0; compile4_out.txt)
- `famBC 𝒜 j` (pullback of a `QMFamily` along `j : T → S`), `isFibreOf_baseChange`.
- `exists_genFib_to_Y (hM : IsShimuraModel p 𝒴 𝒜) (h1 : R1fpProps Y Φ)`: `g : genFib 𝒴 ⟶ Y` with
  `Φ K (s ≫ g) = M3.mk P` for fibres `P` of `𝒜` at `s ≫ j`, and `s ↦ s ≫ g` bijective on ℚ̄-points
  (from `R1univProps` and leaf clauses 3-5).
- NEW textbook leaf `CurveBijIso` (not proved): a morphism of proper smooth curves over ℚ bijective
  on ℚ̄-points is an isomorphism (STANDARD; Hartshorne/EGA locators UNVERIFIED).
- `irreducible_of_chart (hT : TwistClassFinite) … : IrreducibleSpace Y.left` (closure of the chart
  is everything: else the open complement has infinitely many closed points, by Jacobson and the
  proved `smoothCurveNoIsolatedPoint_of smoothStalkDimOne`, all with π = ∞; π⁻¹(∞) is a finite
  twist class).
- `isReduced_of_smooth_of_isDomain` (smooth algebra over a domain is reduced; smooth-fibre's
  proof with a domain), `isReduced_of_smooth_zloc`.
- `irreducibleSpace_of_genFib` (D(p) dense in reduced flat 𝒴, contained in the image of 𝒴_ℚ).
- **`modelIntegral_of (hT : TwistClassFinite) (hC : CurveBijIso) : ModelIntegral` — PROVED.**
- All `#print axioms`: [propext, Classical.choice, Quot.sound].
