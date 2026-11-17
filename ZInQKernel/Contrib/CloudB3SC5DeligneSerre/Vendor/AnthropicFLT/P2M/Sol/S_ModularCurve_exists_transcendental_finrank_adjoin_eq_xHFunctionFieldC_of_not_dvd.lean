/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd (git blob db8a5e138b63fe0b86d2d4d15740c67ce55b99bf, sha256 dfa8ed214be541cf6f9ac50533400b7886efb34739615e1b71595509d383104f).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_jqModC_mem_intFormRatiosC

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace ModularCurve
end ModularCurve

namespace P2MW.S_ModularCurve_exists_transcendental_finrank_adjoin_eq_xHFunctionFieldC_of_not_dvd

set_option autoImplicit false

open _root_.ModularCurve hiding coeffMap_jqModC

namespace DegreeGammaHGlue

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (A : ValuationSubring (AlgebraicClosure ℚ))

theorem coeffMap_jqModC {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) :
    coeffMap f (jqModC R) = jqModC S :=
  map_jqModC f

theorem jqModC_mem_rat : jqModC ℚ ∈ qExpFunctionFieldC ℚ (CohCarrier.GammaH M H) :=
  intFormRatiosC_subset ℚ _ (ModularCurve.jqModC_mem_intFormRatiosC ℚ _)

theorem coeffMap_subtype_jqModC_mem :
    coeffMap A.subtype (jqModC A) ∈
      laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)) := by
  rw [coeffMap_jqModC]
  have h := coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jqModC_mem_rat M H)
  rwa [coeffEmb, coeffMap_jqModC] at h

theorem coeffMap_residue_jqModC_mem :
    coeffMap (IsLocalRing.residue A) (jqModC A) ∈
      qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H) := by
  rw [coeffMap_jqModC]
  exact intFormRatiosC_subset _ _ (ModularCurve.jqModC_mem_intFormRatiosC _ _)

set_option synthInstance.maxHeartbeats 1600000 in
set_option maxHeartbeats 3200000 in

theorem main [NeZero M] {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M) (hA : A.LiesOverPrime ℓ) :
    ∃ (y : LaurentSeries A)
      (hy : coeffMap A.subtype y ∈
        laurentBaseChange (AlgebraicClosure ℚ) (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
      (hyk : coeffMap (IsLocalRing.residue A) y ∈
        qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)),
      Transcendental (IsLocalRing.ResidueField A)
          (⟨_, hyk⟩ : qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) ∧
        0 < Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({(⟨_, hyk⟩ : qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))} :
              Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))))
          (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) ∧
        Module.finrank
            (IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({(⟨_, hy⟩ : laurentBaseChange (AlgebraicClosure ℚ)
                  (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))} :
                Set (laurentBaseChange (AlgebraicClosure ℚ)
                  (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
            (laurentBaseChange (AlgebraicClosure ℚ)
              (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) =
          Module.finrank
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({(⟨_, hyk⟩ : qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))} :
                Set (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))))
            (qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (Gamma1_le_GammaH M H)
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := translation_mem_GammaH M H

  obtain ⟨x, hx, htr, hfin, hle⟩ :=
    ModularCurve.exists_transcendental_finiteDimensional_qExpFunctionFieldC_residueField
      (AlgebraicClosure ℚ) A (CohCarrier.GammaH M H) hT
  have hy := coeffMap_subtype_jqModC_mem M H A
  have hyk := coeffMap_residue_jqModC_mem M H A
  have hxeq : (⟨_, hyk⟩ : qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))
      = x :=
    Subtype.ext (by rw [hx]; exact coeffMap_jqModC _)
  have hyj : ((⟨_, hy⟩ : laurentBaseChange (AlgebraicClosure ℚ)
      (qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) : LaurentSeries (AlgebraicClosure ℚ))
        = jqModC (AlgebraicClosure ℚ) :=
    coeffMap_jqModC _
  refine ⟨jqModC A, hy, hyk, ?_, ?_, ?_⟩
  · rw [hxeq]; exact htr
  · rw [hxeq]; haveI := hfin; exact Module.finrank_pos
  · rw [hxeq]

    exact le_antisymm
      (ModularCurve.finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd M H hℓM A hA x _ hx hyj)
      (hle _ hyj)

end DegreeGammaHGlue

set_option synthInstance.maxHeartbeats 1600000 in
theorem solution
    (M : ℕ) [NeZero M] (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ) :
    ∃ (y : LaurentSeries A)
      (hy : ModularCurve.coeffMap A.subtype y ∈ ModularCurve.xHFunctionFieldBar M H)
      (hyk : ModularCurve.coeffMap (IsLocalRing.residue A) y ∈
        ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H),
      Transcendental (IsLocalRing.ResidueField A)
          (⟨_, hyk⟩ : ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) ∧
        0 < Module.finrank
          (IntermediateField.adjoin (IsLocalRing.ResidueField A)
            ({(⟨_, hyk⟩ : ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)} :
              Set (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)))
          (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) ∧
        Module.finrank
            (IntermediateField.adjoin (AlgebraicClosure ℚ)
              ({(⟨_, hy⟩ : ModularCurve.xHFunctionFieldBar M H)} :
                Set (ModularCurve.xHFunctionFieldBar M H)))
            (ModularCurve.xHFunctionFieldBar M H) =
          Module.finrank
            (IntermediateField.adjoin (IsLocalRing.ResidueField A)
              ({(⟨_, hyk⟩ : ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)} :
                Set (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H)))
            (ModularCurve.xHFunctionFieldC (IsLocalRing.ResidueField A) M H) :=
  DegreeGammaHGlue.main M H A hℓM hA
