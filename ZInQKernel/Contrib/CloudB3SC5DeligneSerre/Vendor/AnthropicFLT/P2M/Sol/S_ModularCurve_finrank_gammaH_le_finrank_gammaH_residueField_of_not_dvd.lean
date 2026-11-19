/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd (git blob 2912d5fca39aead1e93e8cd0ecb0124adf6745ef, sha256 d357d52da80c3f75d3fd2af5db958843de6b83e0e8c1fbe087f24e81167254dd).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X1
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_JqCoeff
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_CohCarrier_Level
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_EllipticCurve_FrobeniusTrace
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ModularCurve_index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_ModularCurve_finrank_gammaH_le_finrank_gammaH_residueField_of_not_dvd

set_option autoImplicit false

namespace FGamHGlue

open CohCarrier CongruenceSubgroup
open scoped MatrixGroups

variable {M : ℕ}

theorem mem_sup_zpowers_neg_one_iff (H : Subgroup (ZMod M)ˣ) (u : (ZMod M)ˣ) :
    u ∈ H ⊔ Subgroup.zpowers (-1) ↔ u ∈ H ∨ -u ∈ H := by
  constructor
  · intro hu
    rw [Subgroup.mem_sup] at hu
    obtain ⟨y, hy, z, hz, rfl⟩ := hu
    rw [Subgroup.mem_zpowers_iff] at hz
    obtain ⟨n, rfl⟩ := hz
    rcases Int.even_or_odd n with hn | hn
    · left; rw [hn.neg_one_zpow, mul_one]; exact hy
    · right; rw [hn.neg_one_zpow, mul_neg_one, neg_neg]; exact hy
  · rintro (h | h)
    · exact Subgroup.mem_sup_left h
    · have : u = -u * -1 := by rw [mul_neg_one, neg_neg]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h)
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))

theorem GammaH_mono {H H' : Subgroup (ZMod M)ˣ} (h : H ≤ H') : GammaH M H ≤ GammaH M H' := by
  intro A hA
  obtain ⟨hA0, hAH⟩ := mem_GammaH_iff.mp hA
  exact mem_GammaH_iff.mpr ⟨hA0, h hAH⟩

theorem neg_mem_Gamma0 {γ : SL(2, ℤ)} (h : γ ∈ Gamma0 M) : -γ ∈ Gamma0 M := by
  rw [Gamma0_mem] at h ⊢
  simp [h]

theorem gamma0Units_neg (γ : SL(2, ℤ)) (h : γ ∈ Gamma0 M) :
    gamma0Units M ⟨-γ, neg_mem_Gamma0 h⟩ = -gamma0Units M ⟨γ, h⟩ := by
  ext
  simp [Gamma0Map]

theorem mem_or_neg_mem_of_mem_GammaH_sup (H : Subgroup (ZMod M)ˣ) (γ : SL(2, ℤ))
    (hγ : γ ∈ GammaH M (H ⊔ Subgroup.zpowers (-1))) : γ ∈ GammaH M H ∨ -γ ∈ GammaH M H := by
  obtain ⟨hγ0, hγH⟩ := mem_GammaH_iff.mp hγ
  rcases (mem_sup_zpowers_neg_one_iff H _).mp hγH with h | h
  · exact Or.inl (mem_GammaH_iff.mpr ⟨hγ0, h⟩)
  · refine Or.inr (mem_GammaH_iff.mpr ⟨neg_mem_Gamma0 hγ0, ?_⟩)
    rw [gamma0Units_neg]
    exact h

end FGamHGlue

open FGamHGlue in
set_option synthInstance.maxHeartbeats 1600000 in

theorem solution (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) {ℓ : ℕ} [Fact ℓ.Prime] (hℓM : ¬ ℓ ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime ℓ)
    (x : ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H))
    (y : ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
      (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))
    (hx : (x : LaurentSeries (IsLocalRing.ResidueField A)) =
      ModularCurve.jqModC (IsLocalRing.ResidueField A))
    (hy : (y : LaurentSeries (AlgebraicClosure ℚ)) = ModularCurve.jqModC (AlgebraicClosure ℚ)) :
    Module.finrank
        (IntermediateField.adjoin (AlgebraicClosure ℚ)
          ({y} : Set (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
            (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H)))))
        (ModularCurve.laurentBaseChange (AlgebraicClosure ℚ)
          (ModularCurve.qExpFunctionFieldC ℚ (CohCarrier.GammaH M H))) ≤
      Module.finrank
        (IntermediateField.adjoin (IsLocalRing.ResidueField A)
          ({x} : Set (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A)
            (CohCarrier.GammaH M H))))
        (ModularCurve.qExpFunctionFieldC (IsLocalRing.ResidueField A) (CohCarrier.GammaH M H)) := by
  haveI : (CohCarrier.GammaH M H).FiniteIndex :=
    Subgroup.finiteIndex_of_le (ModularCurve.Gamma1_le_GammaH M H)
  have hT : ModularGroup.T ∈ CohCarrier.GammaH M H := ModularCurve.translation_mem_GammaH M H
  refine le_trans
    (ModularCurve.finrank_adjoin_jqModC_laurentBaseChange_qExpFunctionFieldC_le_index
      (AlgebraicClosure ℚ) (CohCarrier.GammaH M H) hT
      (CohCarrier.GammaH M (H ⊔ Subgroup.zpowers (-1))) (GammaH_mono le_sup_left)
      (mem_or_neg_mem_of_mem_GammaH_sup H) y hy) ?_
  exact ModularCurve.index_gammaH_le_finrank_adjoin_jqModC_qExpFunctionFieldC_residueField
    M H hℓM A hA x hx
