import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.MixedPeterssonTrace

/-!
# Orthogonality of rational translates (conditional on transport of the test form)

Let `f` be a weight-three cusp form for `Γ(N)` (`N ≥ 3`) that is orthogonal to the same-level
mixed space. Let `g ∈ GL(2, ℚ)` have positive determinant, and let `L` be a common level
(`N ∣ L` and `g Γ(L) g⁻¹ ≤ Γ(N)`). If a modular form `G` for `Γ(L)` has its inverse translate
`G ∣ g⁻¹` represented by a member of the mixed space at some level `M` divisible by `L`, then
`⟪f ∣ g, G⟫_{Γ(L)} = 0` (`rational_translate_mixed_orthogonal`). The same holds in weight two
for the admissible degree-two product span (`rational_translate_product_orthogonal`).

The representation hypothesis `htrans` is exactly the conclusion of a positive-rational transport
theorem for the test form. The proof uses the translate adjunction, restriction scaling to the
common subgroup `g Γ(L) g⁻¹ ∩ Γ(M)` on both sides, and the all-divisible-level mixed orthogonality
transport.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane Matrix.SpecialLinearGroup
open scoped MatrixGroups ModularForm Pointwise

namespace ZInQ.Contrib.HeckePrimeRationality.MixedPeterssonRational

open MixedPeterssonTrace
open DivisionEisensteinLevelMaps (principal_group_le)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

theorem isFiniteRelIndex_map_of_finiteIndex (H K : Subgroup SL(2, ℤ)) [H.FiniteIndex] :
    (H.map (mapGL ℝ)).IsFiniteRelIndex (K.map (mapGL ℝ)) := by
  have : H.IsFiniteRelIndex ⊤ := Subgroup.isFiniteRelIndex_top_iff.mpr inferInstance
  have h : H.IsFiniteRelIndex K := Subgroup.isFiniteRelIndex_of_le_right H le_top
  exact h.map (mapGL ℝ)

open ConjAct in
/-- **Rational-translate orthogonality**, conditional on the transport representation `htrans`
of the single test form `G`. -/
theorem rational_translate_mixed_orthogonal (g : GL (Fin 2) ℚ)
    (hdet : 0 < ((ratGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)
    (N L : ℕ) [NeZero N] [NeZero L] (h3 : 3 ≤ N) (hNL : N ∣ L)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N)
    (f : CuspForm (ΓP N) 3)
    (horth : ∀ G ∈ MixedAllLevelTrace.mixedSpace N (by omega), cuspModPairing f G = 0)
    (G : _root_.ModularForm (ΓP L) 3)
    (htrans : ∃ (M : ℕ) (hM : 0 < M), L ∣ M ∧ ∃ F : _root_.ModularForm (ΓP M) 3,
      F ∈ MixedAllLevelTrace.mixedSpace M hM ∧ ∀ τ : ℍ, F τ = (⇑G ∣[(3 : ℤ)] (ratGL g)⁻¹) τ) :
    cuspModPairing (CuspForm.restrict (translate_level_le g N L hconj)
      (CuspForm.translate f (ratGL g))) G = 0 := by
  rw [principal_rational_translate g hdet N L h3 hconj f G]
  set G' := _root_.ModularForm.restrict (inverse_translate_level_le g N L hconj)
    (_root_.ModularForm.translate G (ratGL g)⁻¹) with hG'
  have hle'' := conjLevel_le g N L hconj
  rw [cuspModPairing_trace_right hle'' (fun h => absurd h (neg_one_not_mem_Gamma N h3)) f G']
  suffices h : cuspModPairing (CuspForm.restrict (Subgroup.map_mono hle'') f) G' = 0 by
    rw [h, mul_zero]
  obtain ⟨M, hM, hLM, F, hF, hFeq⟩ := htrans
  have : NeZero M := ⟨hM.ne'⟩
  have hNM : N ∣ M := dvd_trans hNL hLM
  have hM3 : 3 ≤ M := h3.trans (Nat.le_of_dvd hM hNM)
  set Γ₄ := conjLevel g L ⊓ CongruenceSubgroup.Gamma M with hΓ₄
  have hle1 : Γ₄ ≤ conjLevel g L := inf_le_left
  have hle2 : Γ₄ ≤ CongruenceSubgroup.Gamma M := inf_le_right
  have : (Γ₄.map (mapGL ℝ)).IsFiniteRelIndex ((conjLevel g L).map (mapGL ℝ)) :=
    isFiniteRelIndex_map_of_finiteIndex Γ₄ _
  have : (Γ₄.map (mapGL ℝ)).IsFiniteRelIndex (ΓP M) :=
    isFiniteRelIndex_map_of_finiteIndex Γ₄ _
  have hA := cuspModPairing_restrict_restrict hle1
    (fun h => absurd (hle'' h) (neg_one_not_mem_Gamma N h3))
    (CuspForm.restrict (Subgroup.map_mono hle'') f) G'
  have hB := cuspModPairing_restrict_restrict hle2
    (fun h => absurd h (neg_one_not_mem_Gamma M hM3))
    (CuspForm.restrict (principal_group_le hNM) f) F
  have hzero := mixed_orthogonal_restrict N M h3 hM hNM f horth F hF
  rw [hzero, mul_zero] at hB
  have hcusp : CuspForm.restrict (Subgroup.map_mono hle1)
      (CuspForm.restrict (Subgroup.map_mono hle'') f) =
      CuspForm.restrict (Subgroup.map_mono hle2) (CuspForm.restrict (principal_group_le hNM) f) := by
    apply CuspForm.ext
    intro τ
    rfl
  have hmod : _root_.ModularForm.restrict (Subgroup.map_mono hle1) G' =
      _root_.ModularForm.restrict (Subgroup.map_mono hle2) F := by
    apply _root_.ModularForm.ext
    intro τ
    change G' τ = F τ
    rw [hFeq τ, hG']
    rfl
  rw [hcusp, hmod, hB] at hA
  have hidx : (((Γ₄.map (mapGL ℝ)).relIndex ((conjLevel g L).map (mapGL ℝ)) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.relIndex_ne_zero
  exact (mul_eq_zero.mp hA.symm).resolve_left hidx

open ConjAct in
/-- **Rational-translate orthogonality in weight two** (degree-two product span), conditional on the transport representation `htrans`
of the single test form `G`. -/
theorem rational_translate_product_orthogonal (g : GL (Fin 2) ℚ)
    (hdet : 0 < ((ratGL g : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ).det)
    (N L : ℕ) [NeZero N] [NeZero L] (h3 : 3 ≤ N) (hNL : N ∣ L)
    (hconj : toConjAct (ratGL g) • (ΓP L) ≤ ΓP N)
    (f : CuspForm (ΓP N) 2)
    (horth : ∀ G ∈ TorsionQuadraticGenerators.productSpan N (by omega), cuspModPairing f G = 0)
    (G : _root_.ModularForm (ΓP L) 2)
    (htrans : ∃ (M : ℕ) (hM : 0 < M), L ∣ M ∧ ∃ F : _root_.ModularForm (ΓP M) 2,
      F ∈ TorsionQuadraticGenerators.productSpan M hM ∧ ∀ τ : ℍ, F τ = (⇑G ∣[(2 : ℤ)] (ratGL g)⁻¹) τ) :
    cuspModPairing (CuspForm.restrict (translate_level_le g N L hconj)
      (CuspForm.translate f (ratGL g))) G = 0 := by
  rw [principal_rational_translate g hdet N L h3 hconj f G]
  set G' := _root_.ModularForm.restrict (inverse_translate_level_le g N L hconj)
    (_root_.ModularForm.translate G (ratGL g)⁻¹) with hG'
  have hle'' := conjLevel_le g N L hconj
  rw [cuspModPairing_trace_right hle'' (fun h => absurd h (neg_one_not_mem_Gamma N h3)) f G']
  suffices h : cuspModPairing (CuspForm.restrict (Subgroup.map_mono hle'') f) G' = 0 by
    rw [h, mul_zero]
  obtain ⟨M, hM, hLM, F, hF, hFeq⟩ := htrans
  have : NeZero M := ⟨hM.ne'⟩
  have hNM : N ∣ M := dvd_trans hNL hLM
  have hM3 : 3 ≤ M := h3.trans (Nat.le_of_dvd hM hNM)
  set Γ₄ := conjLevel g L ⊓ CongruenceSubgroup.Gamma M with hΓ₄
  have hle1 : Γ₄ ≤ conjLevel g L := inf_le_left
  have hle2 : Γ₄ ≤ CongruenceSubgroup.Gamma M := inf_le_right
  have : (Γ₄.map (mapGL ℝ)).IsFiniteRelIndex ((conjLevel g L).map (mapGL ℝ)) :=
    isFiniteRelIndex_map_of_finiteIndex Γ₄ _
  have : (Γ₄.map (mapGL ℝ)).IsFiniteRelIndex (ΓP M) :=
    isFiniteRelIndex_map_of_finiteIndex Γ₄ _
  have hA := cuspModPairing_restrict_restrict hle1
    (fun h => absurd (hle'' h) (neg_one_not_mem_Gamma N h3))
    (CuspForm.restrict (Subgroup.map_mono hle'') f) G'
  have hB := cuspModPairing_restrict_restrict hle2
    (fun h => absurd h (neg_one_not_mem_Gamma M hM3))
    (CuspForm.restrict (principal_group_le hNM) f) F
  have hzero := product_orthogonal_restrict N M h3 hM hNM f horth F hF
  rw [hzero, mul_zero] at hB
  have hcusp : CuspForm.restrict (Subgroup.map_mono hle1)
      (CuspForm.restrict (Subgroup.map_mono hle'') f) =
      CuspForm.restrict (Subgroup.map_mono hle2) (CuspForm.restrict (principal_group_le hNM) f) := by
    apply CuspForm.ext
    intro τ
    rfl
  have hmod : _root_.ModularForm.restrict (Subgroup.map_mono hle1) G' =
      _root_.ModularForm.restrict (Subgroup.map_mono hle2) F := by
    apply _root_.ModularForm.ext
    intro τ
    change G' τ = F τ
    rw [hFeq τ, hG']
    rfl
  rw [hcusp, hmod, hB] at hA
  have hidx : (((Γ₄.map (mapGL ℝ)).relIndex ((conjLevel g L).map (mapGL ℝ)) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Subgroup.relIndex_ne_zero
  exact (mul_eq_zero.mp hA.symm).resolve_left hidx

end ZInQ.Contrib.HeckePrimeRationality.MixedPeterssonRational
