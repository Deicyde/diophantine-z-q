/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RepresentsRelSubPic
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_RelPicard_IsAlgEquivZero_eulerChar_sectionsOf_tensor_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_eulerChar_sectionsOf_tensor_invModule_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_linearEquiv_sectionsOf_of_iso
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_isInvertible_invModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_IsInvertible_tensor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_subsingleton_H1_and_finrank_H0_sectionsOf_tensor_invModule_pow_ker_of_isAlgEquivZero

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open AlgebraicGeometry.RelPicard
open NeronModelInfra
open CategoryTheory.MonoidalCategory
open AlgebraicCurve

namespace P2FSketch

theorem preimage_id {X : Scheme.{u}} (U : X.Opens) : (𝟙 X) ⁻¹ᵁ U = U := by
  ext1; rfl

theorem cover_ext {X : Scheme.{u}} (𝒱 𝒱' : X.TwoAffineOpenCover) (h0 : 𝒱.U0 = 𝒱'.U0) (h1 : 𝒱.U1 = 𝒱'.U1) :
    𝒱 = 𝒱' := by
  cases 𝒱; cases 𝒱'; cases h0; cases h1; rfl

theorem finrank_eq_of_iso {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    (𝒱 : X.TwoAffineOpenCover) {M M' : X.Modules} (e : M ≅ M') :
    Module.finrank K (𝒱.sectionsOf x M).H0 = Module.finrank K (𝒱.sectionsOf x M').H0 ∧
      Module.finrank K (𝒱.sectionsOf x M).H1 = Module.finrank K (𝒱.sectionsOf x M').H1 := by
  have hφ : (Iso.refl X).hom ≫ x = x := Category.id_comp x
  let e' : M ≅ (Scheme.Modules.pullback (Iso.refl X).hom).obj M' :=
    e ≪≫ ((Scheme.Modules.pullbackId X).app M').symm
  obtain ⟨𝒱₀, h0, h1, ⟨f0⟩, ⟨f1⟩⟩ :=
    Scheme.TwoAffineOpenCover.exists_linearEquiv_sectionsOf_of_iso x x (Iso.refl X) hφ 𝒱 M' M e'
  have h𝒱 : 𝒱₀ = 𝒱 := cover_ext 𝒱₀ 𝒱 (h0.trans (preimage_id _)) (h1.trans (preimage_id _))
  subst h𝒱
  exact ⟨f0.finrank_eq, f1.finrank_eq⟩

end P2FSketch

open P2FSketch in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (g : ℕ)
    (hg : ∀ (L : Type u) [Field L] [Algebra K L] (M : CurveModel K L) (e : M.C ≅ X)
      (_ : e.hom ≫ x = M.toBase) (Kc : Divisor K L) (g' : ℕ),
      (∀ D : Divisor K L, (ell D : ℤ) - ell (Kc - D) = Divisor.degree D + 1 - g') → g' = g)
    (p : Spec (CommRingCat.of K) ⟶ X) (hp : p ≫ x = 𝟙 _)
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) (h0 : IsAlgEquivZero x L)
    (r : ℕ) (hr : 2 * g ≤ r + 1) (𝒱 : X.TwoAffineOpenCover) :
    Subsingleton (𝒱.sectionsOf x (L ⊗ ((p.ker) ^ r).invModule)).H1 ∧
      Module.finrank K (𝒱.sectionsOf x (L ⊗ ((p.ker) ^ r).invModule)).H0 = r + 1 - g := by

  have hI1 : (p.ker).IsCartierFLT := Scheme.Hom.isInvertible_ker_of_comp_eq_id p hp
  have hpow : ∀ n : ℕ, ((p.ker) ^ n).IsCartierFLT := fun n => by
    induction n with
    | zero => rw [pow_zero, Scheme.IdealSheafData.one_eq_top]; exact Scheme.IdealSheafData.isInvertible_topFLT
    | succ n ih => rw [pow_succ]; exact ih.mul hI1
  have hI : ((p.ker) ^ r).IsCartierFLT := hpow r
  have hN : Scheme.Modules.IsInvertible ((p.ker) ^ r).invModule := hI.isInvertible_invModule
  have hLN : Scheme.Modules.IsInvertible (L ⊗ ((p.ker) ^ r).invModule) := hL.tensor hN
  have hO : Scheme.Modules.IsInvertible (SheafOfModules.unit X.ringCatSheaf : X.Modules) :=
    Scheme.Modules.isInvertible_unitFLT _

  obtain ⟨hZ, hdeg, -, -⟩ := Scheme.Hom.isFinite_and_finrank_subschemeIota_ker_pow_of_comp_eq_id p hp r

  have hC := RelPicard.IsAlgEquivZero.eulerChar_sectionsOf_tensor_eq x 𝒱 L ((p.ker) ^ r).invModule hL hN h0
  have hA := Scheme.IdealSheafData.IsCartierFLT.eulerChar_sectionsOf_tensor_invModule_eq x hI hZ hdeg
    (SheafOfModules.unit X.ringCatSheaf : X.Modules) hO 𝒱
  obtain ⟨hU0, hU1⟩ := finrank_eq_of_iso x 𝒱 (M := (SheafOfModules.unit X.ringCatSheaf : X.Modules) ⊗ ((p.ker) ^ r).invModule)
    (M' := ((p.ker) ^ r).invModule) (λ_ (((p.ker) ^ r).invModule))
  obtain ⟨hg1, hg0⟩ :=
    Scheme.TwoAffineOpenCover.finrank_H1_sectionsOf_unit_eq_and_finrank_H0_eq_one K x g hg 𝒱

  have hvan : Subsingleton (𝒱.sectionsOf x (L ⊗ ((p.ker) ^ r).invModule)).H1 := by
    apply Scheme.Modules.IsInvertible.subsingleton_H1_sectionsOf_of_le_eulerChar_sub K x _ hLN 𝒱
    push_cast at hC hA ⊢
    omega
  refine ⟨hvan, ?_⟩
  haveI := hvan
  have h1z : Module.finrank K (𝒱.sectionsOf x (L ⊗ ((p.ker) ^ r).invModule)).H1 = 0 :=
    Module.finrank_zero_of_subsingleton
  have hgle : g ≤ r + 1 := by omega
  have key : (Module.finrank K (𝒱.sectionsOf x (L ⊗ ((p.ker) ^ r).invModule)).H0 : ℤ) = r + 1 - g := by
    push_cast at hC hA ⊢
    omega
  omega
