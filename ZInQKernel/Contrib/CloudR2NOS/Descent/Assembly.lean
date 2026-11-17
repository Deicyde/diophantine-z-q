/-
Copyright (c) 2026 H5/NOS Round-2 lane4 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

H5 scheme-only effective descent, route Q. This follows the Parent-approved plan
SCHEME_DESCENT_NATIVE_PLAN_001, sha 7a0aede9.

Sub-statement Q0, the producer theorem: the SCHEME part of FLT
`exists_descent_of_faithfullyFlat_of_cocycle`. The hypotheses are FLT's (Sol lines 30–55 at
FLT@6e837e75) minus `hL'`; the conclusion is FLT's minus the descended line.

DROP-IN for C5's ProjConstruction′: the call is the FLT call at `ProjConstruction.lean.txt`
l.78–86 with `hM` removed.

NATIVE assembly of Q1–Q14. SOURCE ONLY, UNCOMPILED. Universe u. The only option is
autoImplicit false.
-/
import ZInQKernel.Contrib.CloudR2NOS.Descent.Descend
import ZInQKernel.Contrib.CloudR2NOS.Descent.DescendedPresentation
import ZInQKernel.Contrib.CloudR2NOS.Descent.Compat
import ZInQKernel.Contrib.CloudR2NOS.Descent.Image

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

namespace ZInQ.Contrib.CloudR2NOS.Descent

local notation "CIBS" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.Scheme.Modules.ClosedImmersionBySections
local notation "PSmap" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.map
local notation "PSπ" => ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.π
local notation "pbSec" => ZInQ.Contrib.CloudR2NOS.ClosedSection.pullbackSection

/-- **Q0. Scheme-only effective descent along a faithfully flat map of affine schemes.**

The data are a scheme `X'` over `Spec S'`, a closed-immersion presentation of `L'`, and a
descent datum on `X'` given by the overlaps `X''` and `X'''` with their cartesian squares. It is
accompanied by a descent datum `ψ` on `L'` satisfying FLT's cocycle equation `hψ`. Under these
hypotheses `X'` descends: there is `X` over `Spec S` with `X' = X ×_S S'`, and the two
projections from `X''` coequalise.

Truth check: this is the scheme part of the FLT theorem, which FLT proves, under a subset of
its hypotheses. The construction (Q1–Q14) works as follows:
* descend the degree-1 sections;
* present `L'` by descended generators as a closed immersion into `ℙ^M_{S'}`;
* take the scheme-theoretic image `X` of `X' → ℙ^M_S`;
* prove cartesianness by flat base change of the kernel. -/
theorem exists_descent_scheme_of_faithfullyFlat_of_cocycle
    {S : Type u} [CommRing S] (S' : Type u) [CommRing S'] [Algebra S S'] [Module.FaithfullyFlat S S']
    (X' : Scheme.{u}) (f' : X' ⟶ Spec (CommRingCat.of S')) (L' : X'.Modules)
    (hva : CIBS L' f')
    (X'' : Scheme.{u}) (f'' : X'' ⟶ Spec (CommRingCat.of (S' ⊗[S] S'))) (a₁ a₂ : X'' ⟶ X')
    (ha₁ : IsPullback a₁ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (ha₂ : IsPullback a₂ f'' f' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom)))
    (X''' : Scheme.{u}) (f''' : X''' ⟶ Spec (CommRingCat.of (S' ⊗[S] (S' ⊗[S] S'))))
    (b₁₂ b₁₃ b₂₃ : X''' ⟶ X'')
    (hb₁₂ : IsPullback b₁₂ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₁₃ : IsPullback b₁₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.map (AlgHom.id S S')
        (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S')).toRingHom)))
    (hb₂₃ : IsPullback b₂₃ f''' f'' (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight : S' ⊗[S] S' →ₐ[S] S' ⊗[S] (S' ⊗[S] S')).toRingHom)))
    (h₁ : b₁₂ ≫ a₁ = b₁₃ ≫ a₁) (h₂ : b₁₂ ≫ a₂ = b₂₃ ≫ a₁) (h₃ : b₁₃ ≫ a₂ = b₂₃ ≫ a₂)
    (ψ : (Scheme.Modules.pullback a₁).obj L' ≅ (Scheme.Modules.pullback a₂).obj L')
    (hψ : ((Scheme.Modules.pullbackCongr h₁).app L').symm ≪≫
          ((Scheme.Modules.pullbackComp b₁₂ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₁₂).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₂ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₂).app L') ≪≫
          ((Scheme.Modules.pullbackComp b₂₃ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₂₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₂₃ a₂).app L') ≪≫
          ((Scheme.Modules.pullbackCongr h₃).app L').symm
        = ((Scheme.Modules.pullbackComp b₁₃ a₁).app L').symm ≪≫
          (Scheme.Modules.pullback b₁₃).mapIso ψ ≪≫ ((Scheme.Modules.pullbackComp b₁₃ a₂).app L')) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of S)) (c : X' ⟶ X),
      IsPullback c f' f (Spec.map (CommRingCat.ofHom (algebraMap S S'))) ∧ a₁ ≫ c = a₂ ≫ c := by
  classical
  -- Q3–Q5: the descended sections span `Γ(L', ⊤)` over `S'`
  have hspan := span_descended S' X' f' L' hva X'' f'' a₁ a₂ ha₁ ha₂ X''' f''' b₁₂ b₁₃ b₂₃
    hb₁₂ hb₁₃ hb₂₃ h₁ h₂ h₃ ψ hψ
  -- Q6–Q8: a closed-immersion presentation by descended sections
  obtain ⟨M, 𝔗, h𝔗P, h𝔗ci⟩ := exists_closedImmersion_presentation_of_span f' L' hva
    (fun d => ψ.hom.app ⊤ (pbSec a₁ d) = pbSec a₂ d) (descended_zero a₁ a₂ ψ) hspan
  haveI : IsClosedImmersion 𝔗.toProj := h𝔗ci
  -- Q10: descent compatibility of `𝔗`
  have hcomp : a₁ ≫ 𝔗.toProj ≫ PSmap S S' M = a₂ ≫ 𝔗.toProj ≫ PSmap S S' M :=
    toProj_comp_map_eq S' ha₁ ha₂ ψ 𝔗 h𝔗P
  -- `ℙ^M_{S'} = ℙ^M_S ×_S S'`, and `Spec (S' ⊗ S') = Spec S' ×_S Spec S'`
  have hP := ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.ProjSpace.isPullback_map S S' M
  have hS : IsPullback
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : S' →ₐ[S] S' ⊗[S] S').toRingHom))
      (Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap S S'))) (Spec.map (CommRingCat.ofHom (algebraMap S S'))) :=
    isPullback_SpecMap_of_isPushout _ _ _ _ (CommRingCat.isPushout_tensorProduct S S' S')
  -- Q11: the double overlap is `X' ×_P P'`
  have hsq := isPullback_overlap hS ha₁ ha₂.w 𝔗.toProj_π hP hcomp
  -- Q12: flat base change of the kernel
  haveI : Flat (Spec.map (CommRingCat.ofHom (algebraMap S S'))) := flat_specMap_algebraMap S S'
  haveI : Flat (PSmap S S' M) := MorphismProperty.of_isPullback (P := @Flat) hP inferInstance
  haveI : QuasiCompact (PSmap S S' M) :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hP inferInstance
  have hker := ker_eq_comap_of_isPullback hsq
  -- Q13: `a₂` is split by the diagonal `Spec S' → Spec (S' ⊗ S')`, so the kernel is unchanged
  let μ : S' ⊗[S] S' →+* S' := (Algebra.TensorProduct.lmul' S : S' ⊗[S] S' →ₐ[S] S').toRingHom
  have hμ : μ.comp (Algebra.TensorProduct.includeRight : S' →ₐ[S] S' ⊗[S] S').toRingHom =
      RingHom.id S' := RingHom.ext fun x => by simp [μ]
  let s : X' ⟶ X'' := ha₂.lift (𝟙 X') (f' ≫ Spec.map (CommRingCat.ofHom μ)) (by
    rw [Category.id_comp, Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hμ,
      CommRingCat.ofHom_id, Spec.map_id, Category.comp_id])
  have hs : s ≫ a₂ = 𝟙 X' := ha₂.lift_fst _ _ _
  have hker₂ := ker_comp_of_comp_eq_id a₂ s hs 𝔗.toProj
  -- Q14: the scheme-theoretic image is the descended scheme
  refine ⟨(𝔗.toProj ≫ PSmap S S' M).image, (𝔗.toProj ≫ PSmap S S' M).imageι ≫ PSπ S M,
    (𝔗.toProj ≫ PSmap S S' M).toImage, ?_, ?_⟩
  · exact isPullback_image_base 𝔗.toProj (PSmap S S' M) (hker.symm.trans hker₂) hP 𝔗.toProj_π
  · exact comp_toImage_eq a₁ a₂ 𝔗.toProj (PSmap S S' M) hcomp

end ZInQ.Contrib.CloudR2NOS.Descent
