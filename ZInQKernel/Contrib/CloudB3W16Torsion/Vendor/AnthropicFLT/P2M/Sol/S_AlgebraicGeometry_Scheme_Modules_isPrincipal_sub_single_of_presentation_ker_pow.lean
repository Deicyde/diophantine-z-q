/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_IdealSheafModule
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RelCartier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_invModule_eq_lSpaceOn
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_exists_divisor_range_module_eq_lSpaceOn
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_eq_mul_and_eq_add_ord_of_presentations
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_closedPoint_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_eq_of_range_stalk_eq
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_isInvertible_ker_of_comp_eq_id
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_IsInvertible_pow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_IdealSheafData_range_moduleIota_app_and_injective
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow

set_option autoImplicit false

universe u
open CategoryTheory
open AlgebraicGeometry
-- Source-local namespace is declared by the following inline scaffold.
open Opposite
open TopologicalSpace

namespace AlgebraicGeometry p2m_export "AlgebraicGeometry" "SmoothOfRelativeDimension IsProper Scheme.Hom Spec IsIntegral Scheme IsAffineOpen Scheme.Modules Scheme.IdealSheafData Scheme.IdealSheafData.IsCartierFLT Scheme.IdealSheafData.IsCartierFLT.exists_divisor_range_invModule_eq_lSpaceOn Scheme.IdealSheafData.IsCartierFLT.exists_divisor_range_module_eq_lSpaceOn Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations Scheme.Hom.isInvertible_ker_of_comp_eq_id Scheme.IdealSheafData.range_moduleIota_app_and_injective" namespace Scheme p2m_export "AlgebraicGeometry.Scheme" "Hom Γ functionField affineBasicOpen Modules Opens IdealSheafData IdealSheafData.IsCartierFLT IdealSheafData.IsCartierFLT.exists_divisor_range_invModule_eq_lSpaceOn IdealSheafData.IsCartierFLT.exists_divisor_range_module_eq_lSpaceOn Hom.ord_eq_of_ker_pow_ideal_eq_span Modules.exists_eq_mul_and_eq_add_ord_of_presentations Hom.isInvertible_ker_of_comp_eq_id IdealSheafData.range_moduleIota_app_and_injective" namespace Modules p2m_export "AlgebraicGeometry.Scheme.Modules" "presheaf Hom IsInvertible toUnitSection ofUnitSection_injective exists_eq_mul_and_eq_add_ord_of_presentations" end AlgebraicGeometry.Scheme.Modules
open _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow.AlgebraicGeometry
open scoped _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme _root_.AlgebraicGeometry.Scheme.Modules in
open _root_.AlgebraicGeometry.Scheme.Modules AlgebraicCurve _root_.CategoryTheory.MonoidalCategory in

theorem AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow'
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (n : ℕ)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint K))) X.functionField).range =
        v.toValuationSubring.toSubring)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ((P.ker ^ n).invModule, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).invModule, U), φ V (((P.ker ^ n).invModule).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).invModule, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ((P.ker ^ n).module, U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).module, U), φ' V (((P.ker ^ n).module).presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).module, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D - n • Finsupp.single v 1) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D' + n • Finsupp.single v 1) := by
  classical
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  set pt : X := P.base (IsLocalRing.closedPoint K) with hpt
  have hI : (P.ker ^ n).IsCartierFLT := (Scheme.Hom.isInvertible_ker_of_comp_eq_id P hP).pow n

  have hplace : ∀ (y : X) (w : Place K X.functionField),
      (algebraMap (X.presheaf.stalk y) X.functionField).range = w.toValuationSubring.toSubring →
      ((pt = y → w = v) ∧ (pt ≠ y → w ≠ v)) := by
    intro y w hw
    constructor
    · rintro rfl
      apply Place.ext
      apply ValuationSubring.toSubring_injective
      exact hw.symm.trans hv
    · intro hne heq
      apply hne
      subst heq
      exact (eq_of_range_stalk_eq x pt y (hv.trans hw.symm))

  have hcoef : ∀ (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (y : X) (hyU : y ∈ U), IsClosed ({y} : Set X) →
      (P.ker ^ n).ideal ⟨U, hU⟩ = Ideal.span {g} →
      ∀ w : Place K X.functionField,
        (algebraMap (X.presheaf.stalk y) X.functionField).range = w.toValuationSubring.toSubring →
        haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
        ((n • Finsupp.single v (1 : ℤ) : Divisor K X.functionField) w : ℤ) =
          w.ord (algebraMap Γ(X, U) X.functionField g) := by
    intro U hU g y hyU hy hg w hw
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    have hord := Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span x P hP n U hU g hg y hyU hy w hw
    obtain ⟨h1, h2⟩ := hplace y w hw
    simp only [Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul, nsmul_eq_mul]
    by_cases hyp : pt = y
    · rw [hord.1 hyp, if_pos (h1 hyp).symm, mul_one]
    · rw [hord.2 hyp, if_neg (fun h => h2 hyp h.symm), mul_zero]
  constructor
  ·
    obtain ⟨D₀, φ₀, ⟨h1, h2, h3, h4, h5⟩, hf, hpin⟩ :=
      Scheme.IdealSheafData.IsCartierFLT.exists_divisor_range_invModule_eq_lSpaceOn x hI
    have hsec : ∃ (U : X.Opens) (m : Γ((P.ker ^ n).invModule, U)), m ≠ 0 :=
      ⟨⊤, (P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1), fun h => hf (by rw [h, map_zero])⟩
    obtain ⟨g₁, hg₁, -, hDw, -⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x _ D D₀ φ φ₀
      hnat h1 hsmul h2 hinj h3 hrange h4 hsec
    refine ⟨g₁ * (φ₀ ⊤ ((P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1)))⁻¹,
      mul_ne_zero hg₁ (inv_ne_zero hf), fun w => ?_⟩
    obtain ⟨y, hy, hw⟩ := exists_closedPoint_range_stalk_eq x w
    obtain ⟨U, r, hyr, g, -, hIg⟩ := hI y
    have hc := hcoef (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    have hp := hpin (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    simp only [Finsupp.coe_sub, Pi.sub_apply]
    rw [hc, hDw w, Place.ord_mul _ hg₁ (inv_ne_zero hf), Place.ord_inv]
    haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨y, hyr⟩⟩
    have hp' : D₀ w + w.ord (φ₀ ⊤ ((P.ker ^ n).invModuleSection.app ⊤ (toUnitSection ⊤ 1))) =
        w.ord (algebraMap Γ(X, X.affineBasicOpen r) X.functionField g) := hp
    change D₀ w + w.ord g₁ - _ = _
    omega
  ·
    obtain ⟨D₀, φ₀, ⟨h1, h2, h3, h4, h5⟩, c, hc0, hcφ, hpin⟩ :=
      Scheme.IdealSheafData.IsCartierFLT.exists_divisor_range_module_eq_lSpaceOn x hI

    have hsec : ∃ (U : X.Opens) (m : Γ((P.ker ^ n).module, U)), m ≠ 0 := by
      obtain ⟨U, r, hηr, g, hgnz, hIg⟩ := hI (genericPoint X)
      haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨genericPoint X, hηr⟩⟩
      have hrg := (Scheme.IdealSheafData.range_moduleIota_app_and_injective (P.ker ^ n) (X.affineBasicOpen r)).1
      have hgmem : (toUnitSection (X.affineBasicOpen r) g) ∈ Set.range ((P.ker ^ n).moduleι.app (X.affineBasicOpen r)) := by
        rw [hrg, hIg]
        exact Ideal.mem_span_singleton_self g
      obtain ⟨m, hm⟩ := hgmem
      refine ⟨X.affineBasicOpen r, m, fun h0 => ?_⟩
      rw [h0, map_zero] at hm
      have : g = 0 := (ofUnitSection_injective _ hm).symm
      exact nonZeroDivisors.ne_zero hgnz this
    obtain ⟨g₂, hg₂, -, hDw, -⟩ := Scheme.Modules.exists_eq_mul_and_eq_add_ord_of_presentations x _ D' D₀ φ' φ₀
      hnat' h1 hsmul' h2 hinj' h3 hrange' h4 hsec
    refine ⟨g₂ * c⁻¹, mul_ne_zero hg₂ (inv_ne_zero hc0), fun w => ?_⟩
    obtain ⟨y, hy, hw⟩ := exists_closedPoint_range_stalk_eq x w
    obtain ⟨U, r, hyr, g, -, hIg⟩ := hI y
    have hc := hcoef (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    have hp := hpin (X.affineBasicOpen r) (X.affineBasicOpen r).2 g y hyr hy hIg w hw
    simp only [Finsupp.coe_add, Pi.add_apply]
    rw [hc, hDw w, Place.ord_mul _ hg₂ (inv_ne_zero hc0), Place.ord_inv]
    haveI : Nonempty (X.affineBasicOpen r : X.Opens) := ⟨⟨y, hyr⟩⟩
    change D₀ w + w.ord g₂ + _ = _
    have hp' : D₀ w + w.ord c + w.ord (algebraMap Γ(X, X.affineBasicOpen r) X.functionField g) = 0 := hp
    omega

open _root_.AlgebraicGeometry _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_isPrincipal_sub_single_of_presentation_ker_pow.AlgebraicGeometry _root_.CategoryTheory.MonoidalCategory in
theorem solution
    {K : Type u} [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (n : ℕ)
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk (P.base (IsLocalRing.closedPoint K))) X.functionField).range =
        v.toValuationSubring.toSubring)
    (D D' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Divisor K X.functionField)
    (φ : ∀ U : X.Opens, Γ((P.ker ^ n).invModule, U) →+ (X.functionField : Type u))
    (hnat : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).invModule, U), φ V (((P.ker ^ n).invModule).presheaf.map (homOfLE h).op m) = φ U m)
    (hsmul : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).invModule, U)),
      φ U (a • m) = algebraMap Γ(X, U) X.functionField a * φ U m)
    (hinj : ∀ U : X.Opens, Nonempty U → Function.Injective (φ U))
    (hrange : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D : Set X.functionField))
    (φ' : ∀ U : X.Opens, Γ((P.ker ^ n).module, U) →+ (X.functionField : Type u))
    (hnat' : ∀ (U V : X.Opens) (h : V ≤ U), Nonempty V →
      ∀ m : Γ((P.ker ^ n).module, U), φ' V (((P.ker ^ n).module).presheaf.map (homOfLE h).op m) = φ' U m)
    (hsmul' : ∀ (U : X.Opens) [Nonempty U] (a : Γ(X, U)) (m : Γ((P.ker ^ n).module, U)),
      φ' U (a • m) = algebraMap Γ(X, U) X.functionField a * φ' U m)
    (hinj' : ∀ U : X.Opens, Nonempty U → Function.Injective (φ' U))
    (hrange' : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      ∀ U : X.Opens, IsAffineOpen U → Nonempty U →
        Set.range (φ' U) = (AlgebraicCurve.lSpaceOn (AlgebraicCurve.placesOf x U) D' : Set X.functionField)) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    AlgebraicCurve.Divisor.IsPrincipal (D - n • Finsupp.single v 1) ∧
      AlgebraicCurve.Divisor.IsPrincipal (D' + n • Finsupp.single v 1) :=
  AlgebraicGeometry.Scheme.Modules.isPrincipal_sub_single_of_presentation_ker_pow' x P hP n v hv D D' φ hnat hsmul hinj
    hrange φ' hnat' hsmul' hinj' hrange'
