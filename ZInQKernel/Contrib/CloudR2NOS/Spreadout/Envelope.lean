/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): the properness input from the H65 full-universe envelope

New glue (no vendored source in this file).  It discharges `ProperDescendsFor D c` for EVERY
cofiltered system `I : Type u`, `[Category.{u} I]`, of quasi-compact quasi-separated schemes with
affine transition maps and limit cone `c`, with no Noetherian, separatedness or properness
hypothesis on the stages, from the H65 round-2 full-universe theorems (read-only source
`r2/recovery/h65-full-u-current/source`, Apache-2.0, adapted from AxiomMath/Stacks
c496df0d9beea9deaeabcea8492605f9a0a2313b; see `CloudW01Spread/LICENSE` and the H65 notices):

* `ZInQ.Contrib.CloudW01Spread.R2AltChow.hasProperEnvelope_of_finitePresentation`
  (`R2AltChow/FinitePresentationEnvelope.lean`, sha256 6eab257f…): a separated morphism of finite
  presentation to a qcqs scheme has an actual proper envelope;
* `ZInQ.Contrib.CloudW01Spread.R2Envelope.exists_proper_stage_of_envelope`
  (`R2EnvelopeDescent.lean`, sha256 31a9de80…): properness at the limit of a separated, locally
  finite type stage morphism with an envelope holds at a later stage.

The argument follows the H65 proof `ZInQ.Contrib.SpreadOut.EGAIV_8_10_5_xii_proof` (`Proper.lean`,
sha256 1f5a31fa…), at universe `u` and for an arbitrary cofiltered index category:
1. separatedness of the limit object (from properness) descends to a stage — DERIVED by lane 3's
   `exists_isSeparated_next` (published W01 port of Stacks 01ZQ);
2. the stage structure map `X₀ ⟶ 𝟙` gets its H65 proper envelope;
3. H65 envelope descent gives properness one stage further;
4. the result is transported to the base change along the composite ORIGINAL arrow `b ≫ a`.
-/
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.Separated
import ZInQKernel.Contrib.CloudR2NOS.Spreadout.GenericField
import ZInQKernel.Contrib.CloudW01Spread.R2EnvelopeDescent
import ZInQKernel.Contrib.CloudW01Spread.R2AltChow.FinitePresentationEnvelope

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

universe u

open ZInQ.Contrib.SpreadOut (stθ pbNat)

section Envelope

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)] [∀ i, CompactSpace (D.obj i)]
  [∀ i, QuasiSeparatedSpace (D.obj i)] (c : Cone D)

/-- **`ProperDescendsFor` for every cofiltered qcqs system with affine transitions** (EGA IV₃
8.10.5 (xii) at universe `u`), from the H65 full-universe proper envelope and envelope descent. -/
theorem properDescendsFor_of_envelope (hc : IsLimit c) : ProperDescendsFor D c := by
  intro i X hlfp hqc hqs hpr
  haveI := hlfp
  haveI := hqc
  haveI := hqs
  -- 1. separatedness at a stage (derived, not assumed)
  obtain ⟨j, a, hsep⟩ := exists_isSeparated_next hc X (by
    haveI := hpr
    infer_instance)
  -- 2. the stage object and its structure map to the terminal object of `Over (D.obj j)`
  let X₀ := (Over.pullback (D.map a)).obj X
  let Y₀ : Over (D.obj j) := Over.mk (𝟙 (D.obj j))
  let f₀ : X₀ ⟶ Y₀ := Over.homMk X₀.hom
  haveI : IsSeparated X₀.hom := hsep
  haveI : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace X₀.hom
  haveI : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated X₀.hom
  haveI : CompactSpace Y₀.left := inferInstanceAs (CompactSpace (D.obj j))
  haveI : QuasiSeparatedSpace Y₀.left := inferInstanceAs (QuasiSeparatedSpace (D.obj j))
  haveI : LocallyOfFiniteType f₀.left := inferInstanceAs (LocallyOfFiniteType X₀.hom)
  haveI : IsSeparated f₀.left := hsep
  haveI : MorphismProperty.RespectsIso (@IsProper : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hpr₀ : IsProper ((Over.pullback (c.π.app j)).obj X₀).hom :=
    prop_of_iso (@IsProper) ((stθ D c a).app X) hpr
  haveI : IsProper ((Over.pullback (c.π.app j)).map f₀).left :=
    (isProper_pullback_toTerminal_iff (c.π.app j) X₀).2 hpr₀
  -- 3. the actual H65 proper envelope of the stage structure map
  obtain ⟨P, q, X', π, ι, hq, hπ, hπs, hι, hw⟩ :=
    ZInQ.Contrib.CloudW01Spread.R2AltChow.hasProperEnvelope_of_finitePresentation X₀.hom
      ⟨inferInstance, inferInstance, inferInstance⟩
  -- 4. H65 envelope descent at the stage
  obtain ⟨k, b, hk⟩ := ZInQ.Contrib.CloudW01Spread.R2Envelope.exists_proper_stage_of_envelope
    D c hc j X₀ Y₀ f₀ X' P π q ι hπ hπs hq hι hw.symm
  -- 5. back to the base change of the original stage object along the composite original arrow
  have hk' : IsProper ((Over.pullback (D.map b)).obj X₀).hom :=
    (isProper_pullback_toTerminal_iff (D.map b) X₀).1 hk
  refine ⟨k, b ≫ a, ?_⟩
  have e : (Over.pullback (D.map (b ≫ a))).obj X ≅ (Over.pullback (D.map b)).obj X₀ :=
    ((pbNat (D.map b) (D.map a) (D.map (b ≫ a)) (D.map_comp b a).symm).app X).symm
  exact prop_of_iso (@IsProper) e hk'

end Envelope

/-- `ProperDescendsFor` for the system of an arbitrary filtered colimit presentation (no
Noetherian, étale or separatedness hypothesis). -/
theorem properDescendsFor_specDiagram_envelope {R : Type u} [CommRing R] {S : CommAlgCat.{u} R}
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J S) :
    ProperDescendsFor (specDiagram pres) (specCone pres) :=
  properDescendsFor_of_envelope (specDiagram pres) (specCone pres) (isLimit_specCone pres)

/-- **`exists_spread_stage` without the properness input.** -/
theorem exists_spread_stage_envelope {R : Type u} [CommRing R] {S : CommAlgCat.{u} R} {J : Type u}
    [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J S) (K : Type u) [CommRing K]
    [Algebra R K] (N : Grp (Over (specCone pres).pt)) [Smooth N.X.hom] [IsProper N.X.hom]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [LocallyOfFinitePresentation A.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom]
    (φ : (Over.pullback (genFstLim pres K)).mapGrp.obj N ≅
      (Over.pullback (genSndLim pres K)).mapGrp.obj A) :
    ∃ (j : Jᵒᵖ) (G : Grp (Over ((specDiagram pres).obj j))),
      Smooth G.X.hom ∧ IsProper G.X.hom ∧
      Nonempty ((Over.pullback ((specCone pres).π.app j)).mapGrp.obj G ≅ N) ∧
      Nonempty ((Over.pullback (genFst pres K j)).mapGrp.obj G ≅
        (Over.pullback (genSnd pres K j)).mapGrp.obj A) :=
  exists_spread_stage pres K (properDescendsFor_specDiagram_envelope pres) N A φ

/-- **`exists_spread_stage_field` without the properness input**: the generic group isomorphism
is supplied over `Spec (Frac P)` for an injective local homomorphism of DVRs `O → P`. -/
theorem exists_spread_stage_field_envelope {O K P E : Type u} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] [CommRing P]
    [IsDomain P] [IsDiscreteValuationRing P] [Field E] [Algebra P E] [IsFractionRing P E]
    [Algebra O P] [Algebra K E] [Algebra O E] [IsScalarTower O K E] [IsScalarTower O P E]
    (hloc : IsLocalHom (algebraMap O P)) (hinj : Function.Injective (algebraMap O P))
    {J : Type u} [SmallCategory J] [IsFiltered J] (pres : ColimitPresentation J (CommAlgCat.of O P))
    (N : Grp (Over (specCone pres).pt)) [Smooth N.X.hom] [IsProper N.X.hom]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [LocallyOfFinitePresentation A.X.hom]
    [QuasiCompact A.X.hom] [QuasiSeparated A.X.hom]
    (φE : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap P E)) :
        Spec (CommRingCat.of E) ⟶ (specCone pres).pt)).mapGrp.obj N ≅
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K E)))).mapGrp.obj A) :
    ∃ (j : Jᵒᵖ) (G : Grp (Over ((specDiagram pres).obj j))),
      Smooth G.X.hom ∧ IsProper G.X.hom ∧
      Nonempty ((Over.pullback ((specCone pres).π.app j)).mapGrp.obj G ≅ N) ∧
      Nonempty ((Over.pullback (genFst pres K j)).mapGrp.obj G ≅
        (Over.pullback (genSnd pres K j)).mapGrp.obj A) :=
  exists_spread_stage_field hloc hinj pres (properDescendsFor_specDiagram_envelope pres) N A φE

end ZInQ.Contrib.CloudR2NOS.Spreadout
