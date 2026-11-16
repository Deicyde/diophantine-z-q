/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCechSectionsOf
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoChartCech
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlacesOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_TwoAffineOpenCover_exists_sectionsOf_unit_equiv_structureSheafSections
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_nonempty_linearEquiv_cechH0_and_cechH1
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_placesOf_union_eq_univ_of_sup_eq_top
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_not_isAffine_of_isProper_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_functionField
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_cechRiemannRoch_of_genusReached
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_ell_eq_zero_of_degree_neg
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_canonicalDivisor_genus_riemannRoch
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub

set_option autoImplicit false

universe u
open CategoryTheory
open CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
open AlgebraicGeometry

namespace AlgebraicCurve
export AlgebraicCurve (Place Divisor Divisor.degree Divisor.degree_single H1 IsCurveOver IsCurveOver.deg_eq_one_of_isAlgClosed ell ConstantsAreBase ell_zero_eq_one_of_constantsAreBase indexOfSpecialty baseToFunctionField cechH0 cechH1 placesOf nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf nonempty_linearEquiv_cechH0_and_cechH1 placesOf_union_eq_univ_of_sup_eq_top isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one essFiniteType_functionField constantsAreBase_of_deg_eq_one stichtenothGenusExists_of_isCurveOver indexOfSpecialty_eq_of_genusReached cechRiemannRoch_of_genusReached ell_eq_zero_of_degree_neg exists_canonicalDivisor_genus_riemannRoch)
open AlgebraicCurve hiding genus
open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem ne_top_of_isAffineOpen_e9 {C : Scheme.{u}} (hC : ¬ IsAffine C) {U : C.Opens}
    (hU : IsAffineOpen U) : U ≠ ⊤ := by
  intro h
  apply hC
  have hT : IsAffineOpen (⊤ : C.Opens) := h ▸ hU
  haveI : IsAffine (⊤ : C.Opens) := hT
  exact IsAffine.of_isIso C.topIso.inv

theorem subsingleton_H1_sectionsOf_of_le_eulerChar_sub'
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (h : 2 * (Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 : ℤ) - 1
        ≤ ((Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1)
          - ((Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ)
              - Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1)) :
    Subsingleton (𝒱.sectionsOf x M).H1 := by
  letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
  haveI hcurve : IsCurveOver K X.functionField :=
    isCurveOver_of_isIntegral_of_smoothOfRelativeDimension_one x (RingEquiv.refl _) (fun _ => rfl)
  haveI : Algebra.EssFiniteType K X.functionField := essFiniteType_functionField x
  have hNA := not_isAffine_of_isProper_of_smoothOfRelativeDimension_one x
  have hne0 : 𝒱.U0 ≠ ⊤ := ne_top_of_isAffineOpen_e9 hNA 𝒱.isAffineOpen_U0
  have hne1 : 𝒱.U1 ≠ ⊤ := ne_top_of_isAffineOpen_e9 hNA 𝒱.isAffineOpen_U1

  have h0 : Nonempty 𝒱.U0 := by
    by_contra hc
    apply hne1
    have hb : 𝒱.U0 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, bot_sup_eq] at this
  have h1 : Nonempty 𝒱.U1 := by
    by_contra hc
    apply hne0
    have hb : 𝒱.U1 = ⊥ := by
      ext z
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hz => hc ⟨⟨z, hz⟩⟩
    have := 𝒱.sup_eq_top
    rwa [hb, sup_bot_eq] at this
  obtain ⟨hcov, hS0, hS1⟩ :=
    placesOf_union_eq_univ_of_sup_eq_top x 𝒱.U0 𝒱.U1 𝒱.sup_eq_top hne0 hne1
  obtain ⟨v₀, hv₀⟩ := hS0
  haveI : Nonempty (Place K X.functionField) := ⟨v₀⟩
  have hC : ConstantsAreBase K X.functionField :=
    constantsAreBase_of_deg_eq_one v₀ (IsCurveOver.deg_eq_one_of_isAlgClosed v₀)
  have hℓ0 : ell (0 : Divisor K X.functionField) = 1 := ell_zero_eq_one_of_constantsAreBase hC
  obtain ⟨-, hL0, γ, E₀, hγ⟩ := stichtenothGenusExists_of_isCurveOver hC
  haveI := hL0

  obtain ⟨Kc, g, hRR⟩ := exists_canonicalDivisor_genus_riemannRoch K X.functionField
  have hdeg1 : (1 : ℤ) ≤ v₀.deg := by exact_mod_cast (IsCurveOver.deg_eq_one_of_isAlgClosed v₀).ge
  have hγg : γ = g := by
    apply le_antisymm
    · have h1 := hRR E₀
      have h2 := hγ.eq
      have h3 : (0 : ℤ) ≤ ell (Kc - E₀) := by exact_mod_cast Nat.zero_le _
      omega
    · let E : Divisor K X.functionField := Kc + Finsupp.single v₀ 1
      have hKE : Divisor.degree (Kc - E) < 0 := by
        simp only [E, sub_add_cancel_left, map_neg, Divisor.degree_single, one_mul]
        omega
      have h1 := hRR E
      rw [ell_eq_zero_of_degree_neg hKE, Nat.cast_zero, sub_zero] at h1
      have h2 := hγ.isMax E
      omega
  have hKc : Divisor.degree Kc = 2 * g - 2 := by
    have h1 := hRR Kc
    have h2 := hRR 0
    simp only [sub_self, sub_zero, map_zero, hℓ0] at h1 h2
    omega

  obtain ⟨D, ⟨eM0⟩, ⟨eM1⟩⟩ := nonempty_linearEquiv_cechH0_and_cechH1_sectionsOf 𝒱 x h0 h1 M hM
  obtain ⟨hfin0, hfin1, hrk0, hrk1, hchi, -⟩ := cechRiemannRoch_of_genusReached hγ hcov ⟨v₀, hv₀⟩ hS1 D

  obtain ⟨eO0, eO1, -, -⟩ := Scheme.TwoAffineOpenCover.exists_sectionsOf_unit_equiv_structureSheafSections 𝒱 x
  obtain ⟨⟨eS0⟩, ⟨eS1⟩⟩ := nonempty_linearEquiv_cechH0_and_cechH1 𝒱 x h0 h1
  obtain ⟨-, -, hrk0', hrk1', hchi', -⟩ :=
    cechRiemannRoch_of_genusReached hγ hcov ⟨v₀, hv₀⟩ hS1 (0 : Divisor K X.functionField)

  have eqM0 : Module.finrank K (𝒱.sectionsOf x M).H0 = Module.finrank K ↥(cechH0 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) :=
    eM0.finrank_eq
  have eqM1 : Module.finrank K (𝒱.sectionsOf x M).H1 = Module.finrank K (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) :=
    eM1.finrank_eq
  have eqO0 : Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0
      = Module.finrank K ↥(cechH0 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) (0 : Divisor K X.functionField)) :=
    (eO0.trans eS0).finrank_eq
  have eqO1 : Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1
      = Module.finrank K (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) (0 : Divisor K X.functionField)) :=
    (eO1.trans eS1).finrank_eq
  rw [eqM0, eqM1, eqO0, eqO1] at h
  rw [hrk0', hℓ0, map_zero] at hchi'
  have hdeg : 2 * γ - 1 ≤ Divisor.degree D := by
    push_cast at h hchi hchi'
    omega

  have hKD : Divisor.degree (Kc - D) < 0 := by
    rw [map_sub, hKc]
    omega
  have hℓD : (ell D : ℤ) = Divisor.degree D + 1 - g := by
    have h1 := hRR D
    rw [ell_eq_zero_of_degree_neg hKD, Nat.cast_zero, sub_zero] at h1
    exact h1
  have hiD : indexOfSpecialty D = 0 := by
    have h1 := (indexOfSpecialty_eq_of_genusReached hγ D).2
    have : (indexOfSpecialty D : ℤ) = 0 := by rw [h1]; omega
    exact_mod_cast this
  haveI : Module.Finite K (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) := hfin1
  haveI hsub : Subsingleton (cechH1 (placesOf x 𝒱.U0) (placesOf x 𝒱.U1) D) :=
    Module.finrank_zero_iff.mp (hrk1.trans hiD)
  exact eM1.toEquiv.subsingleton

end AlgebraicCurve
open AlgebraicCurve hiding genus in open _root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_IsInvertible_subsingleton_H1_sectionsOf_of_le_eulerChar_sub.AlgebraicCurve in
theorem solution
    (K : Type u) [Field K] [IsAlgClosed K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsProper x] [SmoothOfRelativeDimension 1 x]
    (M : X.Modules) (hM : Scheme.Modules.IsInvertible M) (𝒱 : X.TwoAffineOpenCover)
    (h : 2 * (Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1 : ℤ) - 1
        ≤ ((Module.finrank K (𝒱.sectionsOf x M).H0 : ℤ) - Module.finrank K (𝒱.sectionsOf x M).H1)
          - ((Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H0 : ℤ)
              - Module.finrank K (𝒱.sectionsOf x (SheafOfModules.unit X.ringCatSheaf : X.Modules)).H1)) :
    Subsingleton (𝒱.sectionsOf x M).H1 :=
  subsingleton_H1_sectionsOf_of_le_eulerChar_sub' K x M hM 𝒱 h
