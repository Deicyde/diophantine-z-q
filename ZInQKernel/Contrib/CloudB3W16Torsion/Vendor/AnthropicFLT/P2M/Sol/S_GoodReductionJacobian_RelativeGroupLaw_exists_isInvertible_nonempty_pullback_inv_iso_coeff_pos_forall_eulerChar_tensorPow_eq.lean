/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafOfModules
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesPullbackMonoidal
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_isInvertible_finiteBySections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_topologicalKrullDim_le
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_SmoothOfRelativeDimension_le_topologicalKrullDim
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_isIntegral_of_field
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_baseChange_of_isPullback
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_FiniteBySections_tensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_exists_isInvertible_nonempty_pullback_inv_iso_coeff_pos_forall_eulerChar_tensorPow_eq

set_option autoImplicit false
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry
open NeronModelInfra
open GoodReductionJacobian

attribute [local instance] MvPolynomial.gradedAlgebra

universe u

namespace P2mSymAmpleTop

section Inv

variable {R : Type u} [CommRing R] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of R)}
  (G : RelativeGroupLaw R f)

theorem inv_natural {T T' : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    (t' : T' ⟶ Spec (CommRingCat.of R)) (ψ : T' ⟶ T) (hψ : ψ ≫ t = t') (x : SchemeHomOver t f) :
    GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x) =
      G.inv t' (GoodReductionJacobian.schemeHomOverComp ψ hψ x) := by
  letI := G.pointGroup t'
  have h : G.mul t' (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x))
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = G.one t' := by
    rw [← G.mul_natural, G.inv_mul_cancel, G.one_natural]
  change (GoodReductionJacobian.schemeHomOverComp ψ hψ (G.inv t x)) *
      (GoodReductionJacobian.schemeHomOverComp ψ hψ x) = 1 at h
  exact eq_inv_of_mul_eq_one_left h

theorem inv_inv_apply {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x : SchemeHomOver t f) :
    G.inv t (G.inv t x) = x := by
  letI := G.pointGroup t
  exact inv_inv x

abbrev invMor : A ⟶ A := (G.inv f RelativeGroupLaw.idPoint).1

theorem invMor_over : invMor G ≫ f = f := (G.inv f RelativeGroupLaw.idPoint).2

theorem invMor_comp_invMor : invMor G ≫ invMor G = 𝟙 A := by
  have h1 : (GoodReductionJacobian.schemeHomOverComp (invMor G) (invMor_over G)
      (G.inv f RelativeGroupLaw.idPoint)).1 = invMor G ≫ invMor G := rfl
  have h2 : GoodReductionJacobian.schemeHomOverComp (invMor G) (invMor_over G)
      (RelativeGroupLaw.idPoint : SchemeHomOver f f) = G.inv f RelativeGroupLaw.idPoint := by
    apply Subtype.ext
    change invMor G ≫ 𝟙 A = invMor G
    exact Category.comp_id _
  rw [← h1, inv_natural, h2, inv_inv_apply]

scoped instance isIso_invMor : IsIso (invMor G) :=
  ⟨⟨invMor G, invMor_comp_invMor G, invMor_comp_invMor G⟩⟩

end Inv

section Square

variable {K : Type u} [Field K] {A : Scheme.{u}} {f : A ⟶ Spec (CommRingCat.of K)}
  (G : RelativeGroupLaw K f)

theorem isPullback_invMor :
    IsPullback (invMor G) f f (Spec.map (CommRingCat.ofHom (algebraMap K K))) := by
  have hid : Spec.map (CommRingCat.ofHom (algebraMap K K)) = 𝟙 _ := by
    rw [Algebra.algebraMap_self, CommRingCat.ofHom_id]
    exact Spec.map_id _
  rw [hid]
  exact IsPullback.of_horiz_isIso ⟨by rw [invMor_over, Category.comp_id]⟩

end Square

section Skel

variable {C : Type*} [Category C] [MonoidalCategory C]

theorem cls_tensor (X Y : C) : toSkeleton (X ⊗ Y) = toSkeleton X * toSkeleton Y :=
  Skeleton.toSkeleton_tensorObj X Y

omit [MonoidalCategory C] in
theorem cls_congr {X Y : C} (e : X ≅ Y) : toSkeleton X = toSkeleton Y :=
  toSkeleton_eq_toSkeleton_iff.mpr ⟨e⟩

end Skel

section Symm

variable {A : Scheme.{u}} (e : A ⟶ A) (he : e ≫ e = 𝟙 A)

theorem cls_pullback_tensor (X Y : A.Modules) :
    toSkeleton ((Scheme.Modules.pullback e).obj (X ⊗ Y)) =
      toSkeleton ((Scheme.Modules.pullback e).obj X) * toSkeleton ((Scheme.Modules.pullback e).obj Y) := by
  rw [cls_congr (Scheme.Modules.pullbackTensorObjIsoFLT e X Y), cls_tensor]

include he in

theorem nonempty_pullback_pullback_iso (X : A.Modules) :
    Nonempty ((Scheme.Modules.pullback e).obj ((Scheme.Modules.pullback e).obj X) ≅ X) :=
  ⟨(Scheme.Modules.pullbackComp e e).app X ≪≫ (Scheme.Modules.pullbackCongr he).app X ≪≫
    (Scheme.Modules.pullbackId A).app X⟩

include he in

theorem nonempty_pullback_symm_iso (𝓛₀ : A.Modules) :
    Nonempty ((Scheme.Modules.pullback e).obj (𝓛₀ ⊗ (Scheme.Modules.pullback e).obj 𝓛₀) ≅
      𝓛₀ ⊗ (Scheme.Modules.pullback e).obj 𝓛₀) := by
  obtain ⟨i⟩ := nonempty_pullback_pullback_iso e he 𝓛₀
  apply toSkeleton_eq_toSkeleton_iff.mp
  rw [cls_pullback_tensor, cls_congr i, cls_tensor, mul_comm]

end Symm

theorem main
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      Nonempty ((Scheme.Modules.pullback (L.inv f RelativeGroupLaw.idPoint).1).obj 𝓛 ≅ 𝓛) ∧
      ∃ q : Polynomial ℚ, 0 < q.coeff g ∧
        ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPowFLT m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ) := by

  haveI : IsIntegral A := hA.isIntegral_of_field
  have hdim : topologicalKrullDim A = g :=
    le_antisymm (SmoothOfRelativeDimension.topologicalKrullDim_le f g)
      (SmoothOfRelativeDimension.le_topologicalKrullDim f g)

  obtain ⟨𝓛₀, h𝓛₀, N, 𝔓, hfin⟩ := AbelianSchemePropertyBundle.exists_isInvertible_finiteBySections K f hA

  obtain ⟨𝔓', -, -, hsq⟩ :=
    Scheme.Modules.ProjPresentation.exists_baseChange_of_isPullback (isPullback_invMor L) 𝔓
  have hfin' : IsFinite 𝔓'.toProj :=
    MorphismProperty.of_isPullback (P := @IsFinite) hsq hfin
  have hfs' : ((Scheme.Modules.pullback (invMor L)).obj 𝓛₀).FiniteBySections f := ⟨N, 𝔓', hfin'⟩

  refine ⟨𝓛₀ ⊗ (Scheme.Modules.pullback (invMor L)).obj 𝓛₀,
    h𝓛₀.tensor (h𝓛₀.pullback (invMor L)), nonempty_pullback_symm_iso (invMor L) (invMor_comp_invMor L) 𝓛₀, ?_⟩

  exact Scheme.Modules.FiniteBySections.exists_polynomial_coeff_pos_forall_eulerChar_tensorPow_eq f g hdim _
    (h𝓛₀.tensor (h𝓛₀.pullback (invMor L))) (Scheme.Modules.FiniteBySections.tensor ⟨N, 𝔓, hfin⟩ hfs') 𝒦

end P2mSymAmpleTop

theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hA : AbelianSchemePropertyBundle K f) (g : ℕ) [SmoothOfRelativeDimension g f]
    (𝒦 : A.OrderedAffineCover) :
    ∃ 𝓛 : A.Modules, Scheme.Modules.IsInvertible 𝓛 ∧
      Nonempty ((Scheme.Modules.pullback (L.inv f RelativeGroupLaw.idPoint).1).obj 𝓛 ≅ 𝓛) ∧
      ∃ q : Polynomial ℚ, 0 < q.coeff g ∧
        ∀ m : ℕ, ((OModulePresheaf.ofModules f (𝓛.tensorPowFLT m)).eulerChar 𝒦 : ℚ) = q.eval (m : ℚ) :=
  P2mSymAmpleTop.main K f L hA g 𝒦
