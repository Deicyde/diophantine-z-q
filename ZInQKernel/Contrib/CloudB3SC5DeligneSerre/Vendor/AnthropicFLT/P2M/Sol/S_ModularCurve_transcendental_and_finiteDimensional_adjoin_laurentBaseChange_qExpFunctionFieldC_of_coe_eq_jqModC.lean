/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC (git blob aaa775a8af2011f08ff4e1b44a7695d610f3b5f8, sha256 e2e1dc772e0844f1ac15ae3a2495de5ca69671c2ee90faaa0884cfd81fd8cd6b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_transcendental_jqModC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve
namespace P2MW.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.ModularCurve
end P2MW.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.ModularCurve
namespace IntermediateField
end IntermediateField
namespace CongruenceSubgroup
end CongruenceSubgroup
namespace AlgebraicCurve
end AlgebraicCurve

namespace P2MW.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (intSeriesC intFormRatiosC qExpFunctionFieldC intFormRatiosC_subset coeffMap_single coeffEmb coeffEmb_coeff laurentBaseChange jqModC coeffMap_ofPowerSeries finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index transcendental_jqModC)
namespace FullnessGamma1
open _root_.ModularCurve hiding coeffEmb_injective

open _root_.ModularCurve hiding coeffEmb_injective
open _root_.P2MW.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.ModularCurve
open _root_.IntermediateField

theorem finrank_adjoin_eq_relfinrank {K E : Type*} [Field K] [Field E] [Algebra K E]
    (F : IntermediateField K E) (x : F) :
    Module.finrank (IntermediateField.adjoin K ({x} : Set F)) F =
      (IntermediateField.adjoin K ({(x : E)} : Set E)).relfinrank F := by
  have hlift : IntermediateField.lift (IntermediateField.adjoin K ({x} : Set F)) =
      IntermediateField.adjoin K ({(x : E)} : Set E) := by
    rw [IntermediateField.lift_adjoin]; simp
  have hle : IntermediateField.adjoin K ({(x : E)} : Set E) ≤ F := by
    rw [← hlift]; exact IntermediateField.lift_le _
  rw [IntermediateField.relfinrank_eq_finrank_of_le hle]
  let i : (IntermediateField.adjoin K ({x} : Set F)) ≃+*
      (IntermediateField.adjoin K ({(x : E)} : Set E)) :=
    ((IntermediateField.liftAlgEquiv (IntermediateField.adjoin K ({x} : Set F))).trans
      (IntermediateField.equivOfEq hlift)).toRingEquiv
  let j : F ≃+* (IntermediateField.extendScalars hle) := RingEquiv.refl _
  refine Algebra.finrank_eq_of_equiv_equiv i j ?_
  ext a
  rfl

section BaseChange

variable (K : Type*) [Field K] [Algebra ℚ K]

theorem coeffEmb_injective : Function.Injective (coeffEmb K) := by
  intro x y h
  ext n
  have h1 := congrArg (fun s : LaurentSeries K => s.coeff n) h
  simp only [coeffEmb_coeff] at h1
  exact (algebraMap ℚ K).injective h1

theorem coeffEmb_ne_zero_iff (x : LaurentSeries ℚ) : coeffEmb K x ≠ 0 ↔ x ≠ 0 := by
  rw [Ne, ← map_zero (coeffEmb K), (coeffEmb_injective K).eq_iff]

theorem coeffEmb_intSeriesC (p : PowerSeries ℤ) : coeffEmb K (intSeriesC ℚ p) = intSeriesC K p := by
  rw [coeffEmb, intSeriesC, intSeriesC, coeffMap_ofPowerSeries]
  congr 1
  ext n
  simp [PowerSeries.coeff_map]

theorem algebraMap_laurentSeries_eq_C {L : Type*} [Field L] (a : L) :
    algebraMap L (LaurentSeries L) a = HahnSeries.C a := by
  rw [HahnSeries.algebraMap_apply']
  have h1 : algebraMap L (PowerSeries L) a = PowerSeries.C a := by simp
  rw [h1, HahnSeries.ofPowerSeries_C]

theorem coeffEmb_algebraMap (a : ℚ) :
    coeffEmb K (algebraMap ℚ (LaurentSeries ℚ) a) = algebraMap K (LaurentSeries K) (algebraMap ℚ K a) := by
  rw [algebraMap_laurentSeries_eq_C, algebraMap_laurentSeries_eq_C, HahnSeries.C_apply, HahnSeries.C_apply,
    coeffEmb, coeffMap_single]

variable (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ))

theorem image_intFormRatiosC : (coeffEmb K) '' intFormRatiosC ℚ Γ = intFormRatiosC K Γ := by
  ext z
  constructor
  · rintro ⟨y, ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩, rfl⟩
    refine ⟨w, f, g, pf, pg, hf, hg, ?_, ?_⟩
    · rw [← coeffEmb_intSeriesC K]; exact (coeffEmb_ne_zero_iff K _).mpr hg0
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]
  · rintro ⟨w, f, g, pf, pg, hf, hg, hg0, rfl⟩
    refine ⟨intSeriesC ℚ pf / intSeriesC ℚ pg, ⟨w, f, g, pf, pg, hf, hg, ?_, rfl⟩, ?_⟩
    · rw [← coeffEmb_ne_zero_iff K, coeffEmb_intSeriesC]; exact hg0
    · rw [map_div₀, coeffEmb_intSeriesC, coeffEmb_intSeriesC]

variable {Γ}

theorem coeffEmb_mem_adjoin {S : Set (LaurentSeries ℚ)} {y : LaurentSeries ℚ} (hy : y ∈ adjoin ℚ S) :
    coeffEmb K y ∈ adjoin K ((coeffEmb K) '' S) := by
  have hy' : y ∈ (adjoin ℚ S).toSubfield := hy
  rw [adjoin_toSubfield] at hy'
  have hle : Subfield.closure (Set.range (algebraMap ℚ (LaurentSeries ℚ)) ∪ S) ≤
      (adjoin K ((coeffEmb K) '' S)).toSubfield.comap (coeffEmb K) := by
    rw [Subfield.closure_le]
    rintro z (⟨a, rfl⟩ | hz)
    · change coeffEmb K (algebraMap ℚ (LaurentSeries ℚ) a) ∈ adjoin K ((coeffEmb K) '' S)
      rw [coeffEmb_algebraMap]
      exact IntermediateField.algebraMap_mem _ _
    · change coeffEmb K z ∈ adjoin K ((coeffEmb K) '' S)
      exact subset_adjoin K _ ⟨z, hz, rfl⟩
  exact hle hy'

variable (Γ)

theorem laurentBaseChange_qExpFunctionFieldC_eq :
    laurentBaseChange K (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC K Γ := by
  apply le_antisymm
  · rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
    rintro _ ⟨y, hy, rfl⟩
    have h := coeffEmb_mem_adjoin K (S := intFormRatiosC ℚ Γ) hy
    rwa [image_intFormRatiosC] at h
  · rw [qExpFunctionFieldC, ← image_intFormRatiosC K Γ, laurentBaseChange]
    exact IntermediateField.adjoin.mono K _ _ (Set.image_mono (intFormRatiosC_subset ℚ Γ))

end BaseChange

end ModularCurve.FullnessGamma1

open _root_.ModularCurve hiding coeffEmb_injective
open _root_.P2MW.S_ModularCurve_transcendental_and_finiteDimensional_adjoin_laurentBaseChange_qExpFunctionFieldC_of_coe_eq_jqModC.ModularCurve
open _root_.CongruenceSubgroup
open _root_.AlgebraicCurve
open scoped MatrixGroups

open ModularCurve.FullnessGamma1 IntermediateField in
set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in
theorem solution
    (K : Type*) [Field K] [Algebra ℚ K]
    (Γ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)) [Γ.FiniteIndex] (hT : ModularGroup.T ∈ Γ)
    (y : ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)))
    (hy : (y : LaurentSeries K) = ModularCurve.jqModC K) :
    Transcendental K y ∧
      FiniteDimensional
        ↥(IntermediateField.adjoin K ({y} : Set ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ))))
        ↥(ModularCurve.laurentBaseChange K (ModularCurve.qExpFunctionFieldC ℚ Γ)) := by
  classical
  constructor
  ·
    have hinj : Function.Injective
        (algebraMap ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) (LaurentSeries K)) :=
      (algebraMap ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) (LaurentSeries K)).injective
    rw [← transcendental_algebraMap_iff hinj]
    change Transcendental K (y : LaurentSeries K)
    rw [hy]
    exact ModularCurve.transcendental_jqModC K
  ·
    have hEE : laurentBaseChange K (qExpFunctionFieldC ℚ Γ) = qExpFunctionFieldC K Γ :=
      laurentBaseChange_qExpFunctionFieldC_eq K Γ
    have hjE' : jqModC K ∈ laurentBaseChange K (qExpFunctionFieldC ℚ Γ) := hy ▸ y.2
    have hjE : jqModC K ∈ qExpFunctionFieldC K Γ := hEE ▸ hjE'
    obtain ⟨hfin, -⟩ := ModularCurve.finiteDimensional_and_finrank_adjoin_jqModC_qExpFunctionFieldC_le_index K
      Γ hT Γ le_rfl (fun γ hγ => Or.inl hγ) ⟨jqModC K, hjE⟩ rfl
    haveI := hfin
    have hpos : 0 < Module.finrank
        ↥(IntermediateField.adjoin K ({(⟨jqModC K, hjE⟩ : qExpFunctionFieldC K Γ)} : Set (qExpFunctionFieldC K Γ)))
        ↥(qExpFunctionFieldC K Γ) := Module.finrank_pos
    have e1 := finrank_adjoin_eq_relfinrank (qExpFunctionFieldC K Γ) ⟨jqModC K, hjE⟩
    have e2 := finrank_adjoin_eq_relfinrank (laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) y
    have e12 : (IntermediateField.adjoin K ({((⟨jqModC K, hjE⟩ : qExpFunctionFieldC K Γ) : LaurentSeries K)} :
          Set (LaurentSeries K))).relfinrank (qExpFunctionFieldC K Γ) =
        (IntermediateField.adjoin K ({(y : LaurentSeries K)} : Set (LaurentSeries K))).relfinrank
          (laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) := by
      rw [hy, hEE]
    have hpos' : 0 < Module.finrank
        ↥(IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ))))
        ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) :=
      lt_of_lt_of_eq hpos ((e1.trans e12).trans e2.symm)
    haveI : Module.Free
        ↥(IntermediateField.adjoin K ({y} : Set ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ))))
        ↥(laurentBaseChange K (qExpFunctionFieldC ℚ Γ)) := Module.Free.of_divisionRing _ _
    exact Module.finite_of_finrank_pos hpos'
