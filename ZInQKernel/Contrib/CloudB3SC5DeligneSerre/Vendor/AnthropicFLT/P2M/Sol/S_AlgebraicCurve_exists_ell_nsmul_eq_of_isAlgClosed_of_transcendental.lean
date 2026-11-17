/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental (git blob 0ec94dfbb2ffd5305f6427a1a3cc5ccb7b4f3dee, sha256 072b150d8d844f5c91c12574fed0261ea9e0f8761ffdc1d31815f7b5c86b3634).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_isCurveOver_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_constantsAreBase_of_isAlgClosed_of_transcendental
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_stichtenothGenusExists_of_isCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_of_genusReached
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_RiemannGenusReachedAt_eq_of_ge
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_indexOfSpecialty_eq_finrank_H1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_exists_ell_nsmul_eq_of_isAlgClosed_of_transcendental

set_option autoImplicit false
set_option maxHeartbeats 4800000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [IsAlgClosed K] [Field F] [Algebra K F]
    (x : F) (hx : Transcendental K x)
    [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x)) :
    ell (0 : Divisor K F) = 1 ∧
    ∃ M : ℕ, 1 ≤ M ∧ ∀ N, M ≤ N →
      (ell (N • D) : ℤ) = N * Divisor.degree D + 1 - genusFF K F := by
  classical

  haveI hICO : IsCurveOver K F := isCurveOver_of_isAlgClosed_of_transcendental x hx
  have hC : ConstantsAreBase K F := constantsAreBase_of_isAlgClosed_of_transcendental x hx
  haveI hEFT : Algebra.EssFiniteType K F :=
    essFiniteType_of_transcendental_of_finiteDimensional hx inferInstance
  have hell0 : ell (0 : Divisor K F) = 1 := ell_zero_eq_one_of_constantsAreBase hC
  refine ⟨hell0, ?_⟩

  obtain ⟨hNon, hFD, γ, D₀, hRGA⟩ := stichtenothGenusExists_of_isCurveOver hC
  haveI : Nonempty (Place K F) := hNon
  haveI : FiniteDimensional K ↥(LSpace (0 : Divisor K F)) := hFD

  have hidx0 : (indexOfSpecialty (0 : Divisor K F) : ℤ)
      = (ell (0 : Divisor K F) : ℤ) - (Divisor.degree (0 : Divisor K F) + 1 - γ) :=
    (indexOfSpecialty_eq_of_genusReached hRGA 0).2
  have hγ : γ = (genusFF K F : ℤ) := by
    have hgFF : indexOfSpecialty (0 : Divisor K F) = genusFF K F := by
      rw [indexOfSpecialty_eq_finrank_H1]; rfl
    have hdeg0 : Divisor.degree (0 : Divisor K F) = 0 := map_zero _
    rw [hgFF, hdeg0, hell0] at hidx0
    push_cast at hidx0
    linarith

  have hDnn : ∀ v, 0 ≤ D v := fun v ↦ by rw [hD v]; exact le_max_left 0 _
  have hDne : D ≠ 0 := by
    intro h0

    have hxmem : x ∈ LSpace (0 : Divisor K F) := by
      rw [mem_lSpace_iff_ord]
      right
      intro v
      have hDv0 : max 0 (-v.ord x) = 0 := by
        have := hD v; rw [h0] at this; exact this.symm
      have : -v.ord x ≤ 0 := max_eq_left_iff.mp hDv0
      simpa using neg_nonpos.mp this
    rw [hC] at hxmem
    obtain ⟨a, ha⟩ := hxmem
    exact hx (ha ▸ isAlgebraic_algebraMap a)

  obtain ⟨Q, hQ⟩ := Finsupp.support_nonempty_iff.mpr hDne
  have hDQ : 1 ≤ D Q := by
    have hne : D Q ≠ 0 := Finsupp.mem_support_iff.mp hQ
    have hnn := hDnn Q
    omega

  obtain ⟨n₀, hRGAQ⟩ :=
    exists_riemannGenusReachedAt_nsmul_single_of_stichtenothGenusExists hRGA Q

  refine ⟨max 1 n₀, le_max_left _ _, fun N hN ↦ ?_⟩
  have hNn₀ : n₀ ≤ N := (le_max_right _ _).trans hN
  have hle : (n₀ : ℤ) • Finsupp.single Q (1 : ℤ) ≤ N • D := by
    intro v
    simp only [Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Finsupp.single_apply,
      nsmul_eq_mul]
    split_ifs with h
    · subst h
      calc (n₀ : ℤ) * 1 = (n₀ : ℤ) := mul_one _
        _ ≤ (N : ℤ) := by exact_mod_cast hNn₀
        _ = (N : ℤ) * 1 := (mul_one _).symm
        _ ≤ (N : ℤ) * D Q := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hDQ) (Nat.cast_nonneg N)
    · calc (n₀ : ℤ) * 0 = 0 := mul_zero _
        _ ≤ (N : ℤ) * D v := mul_nonneg (Nat.cast_nonneg N) (hDnn v)
  have heq : Divisor.degree (N • D) - (ell (N • D) : ℤ) = γ - 1 :=
    hRGAQ.eq_of_ge hle
  have hdegNsmul : Divisor.degree (N • D) = (N : ℤ) * Divisor.degree D := by
    rw [AddMonoidHom.map_nsmul, nsmul_eq_mul]
  rw [hdegNsmul, hγ] at heq
  linarith
