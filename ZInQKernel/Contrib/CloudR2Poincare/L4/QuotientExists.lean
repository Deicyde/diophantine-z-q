import ZInQKernel.Contrib.CloudR2Poincare.L4.SchemeQuotientOver
import ZInQKernel.Contrib.CloudR2Poincare.L4.QuotientAffineOpen
import ZInQKernel.Contrib.CloudR2Poincare.L4.B3
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_Scheme_exists_quotient_of_finiteLocallyFree_equivalenceRelation

/-!
# Finite stabilizer quotient existence, using the pinned native H5 provider

This is ONLY an H72 bridge. The 17 immutable H5/H76 research provider modules
are source-pinned by the parent/steward and imported from the ONE h72 prefix;
none is edited, copied, renamed, or published by this lane. Provider: FLT
6e837e75355538c7f80bab5b956861e86c4eacc2; exact frozen source/olean bindings
in H5_PROVIDER_CONE.json and H72-QUOTIENT-RESEARCH-PLACEMENT-001.json.

All Scheme-valued tests are used, not just geometric points or Over-k tests.
A genuine coequalizer descends the structure map to Spec k, and the actual
Scheme pullback is reflected to the literal L1 Over kernel pair. No BigFppfSite,
HasSheafify, affine-open, projectivity or quotient hypothesis is assumed.
The separate canonical Stacks E2 work is left untouched.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L4

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

/-- Actual generic finite stabilizer quotient existence; no quotient input remains. -/
theorem FiniteStabilizerQuotientExists_proof : FiniteStabilizerQuotientExists := by
  intro k _ _ A L H
  classical
  let s : (H.K ⊗ A.X).left ⟶ A.X.left := (snd H.K A.X).left
  let t : (H.K ⊗ A.X).left ⟶ A.X.left := (quotientTarget A L H).left
  obtain ⟨hsfin, hsflat, hsfp⟩ := stabilizer_projection_finite_flat_lfp A L H
  obtain ⟨htfin, htflat, htfp⟩ := stabilizer_action_finite_flat_lfp A L H
  haveI : IsFinite s := hsfin
  haveI : Flat s := hsflat
  haveI : LocallyOfFinitePresentation s := hsfp
  haveI : IsFinite t := htfin
  haveI : Flat t := htflat
  haveI : LocallyOfFinitePresentation t := htfp
  let e := (stabilizer_action_isEquivalenceRelation A L H).nonempty_equivalenceRelation.some
  let es : EquivalenceRelation t s := schemeRelationOfOver e
  have hmono : ∀ {T : Scheme} (a b : T ⟶ (H.K ⊗ A.X).left),
      a ≫ s = b ≫ s → a ≫ t = b ≫ t → a = b :=
    fun a b hs ht => es.right_cancellation a b ht hs
  have hequiv : ∀ T : Scheme, Equivalence fun x y : T ⟶ A.X.left =>
      ∃ φ : T ⟶ (H.K ⊗ A.X).left, φ ≫ s = x ∧ φ ≫ t = y :=
    fun T => homRelation_equivalence_swap es T
  have haff : ∀ x : A.X.left, ∃ U : A.X.left.Opens, IsAffineOpen U ∧
      ∀ r : (H.K ⊗ A.X).left, s r = x → t r ∈ U := by
    intro x
    obtain ⟨U, hU, hEU⟩ := abVar_finiteSet_affineOpen A
      (t '' (s ⁻¹' {x})) ((s.finite_preimage_singleton x).image t)
    exact ⟨U, hU, fun r hr => hEU ⟨r, hr, rfl⟩⟩
  obtain ⟨Y, p, w, hpfin, hpflat, hpfp, hpsurj, hpb, hcol⟩ :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.exists_quotient_of_finiteLocallyFree_equivalenceRelation
      s t hmono hequiv haff
  haveI := hpfin
  haveI := hpflat
  haveI := hpfp
  haveI := hpsurj
  exact stabilizerQuotient_of_scheme_coequalizer A L H p w hcol.some hpb

/-- B3 after genuine quotient-input discharge; its native (A)/hA argument remains explicit. -/
theorem StabilizerAbVarQuotientExists_proof : StabilizerAbVarQuotientExists :=
  stabilizerAbVarQuotientExists_of_quotient FiniteStabilizerQuotientExists_proof

end ZInQ.Contrib.CloudR2Poincare.L4
