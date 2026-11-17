/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf (git blob 3b981157eba803bff896ab23a9184d7d6d426bc1, sha256 5d97e35035b5fbc6e2039a6f0b59f1ccf8b9fcfe028d40e76c5f2bfedf77155b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularProlongation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Repartitions
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_isPrincipalIdealRing_of_finiteDimensional_adjoin
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_mem_iff_ord_nonneg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_RegularProlongation_span_residue_lSpace_le_residueSpan_inf

open AlgebraicCurve

theorem solution
    {L : Type*} [Field L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    {ι : Type*} [Fintype ι] (Fb : ι → Type*) [∀ i, Field (Fb i)]
    [∀ i, Algebra (IsLocalRing.ResidueField A) (Fb i)]
    (R : ∀ i, RegularProlongation A F (Fb i))
    (f : F) (hf : ∀ i, f ∈ (R i).integers)
    (hfd : FiniteDimensional (IntermediateField.adjoin L ({f} : Set F)) F)
    (D : Divisor L F) (hD : ∀ v : Place L F, D v = max 0 (-v.ord f))
    (M : ℕ) :
    Submodule.span (IsLocalRing.ResidueField A)
        {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
          u ∈ LSpace (M • D) ∧ ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ≤
      Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} ⊓
        Submodule.span (IsLocalRing.ResidueField A)
          {h : ∀ i, Fb i | ∃ u : F, ∃ hu : ∀ i, u ∈ (R i).integers,
            (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
              u * (f ^ M)⁻¹ ∈ V) ∧
            ∀ i, (R i).residue ⟨u, hu i⟩ = h i} := by
  classical
  haveI := hfd

  have mkPlace : ∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → V ≠ ⊤ →
      ∃ v : Place L F, v.toValuationSubring = V := fun V hV hVt =>
    ⟨⟨V, hV, hVt, ValuationSubring.isPrincipalIdealRing_of_finiteDimensional_adjoin f V hV hVt⟩,
      rfl⟩
  have hMD : ∀ v : Place L F, (M • D) v = (M : ℤ) * D v := fun v => by
    simp [Finsupp.smul_apply]

  have key : ∀ u : F, u ∈ LSpace (M • D) →
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f ∈ V → u ∈ V) ∧
      (∀ V : ValuationSubring F, (∀ a : L, algebraMap L F a ∈ V) → f⁻¹ ∈ V →
        u * (f ^ M)⁻¹ ∈ V) := by
    intro u hu
    rcases eq_or_ne u 0 with rfl | hu0
    · exact ⟨fun V _ _ => V.zero_mem, fun V _ _ => by rw [zero_mul]; exact V.zero_mem⟩
    have hord : ∀ v : Place L F, -(M • D) v ≤ v.ord u :=
      ((mem_lSpace_iff_ord).1 hu).resolve_left hu0

    have hreg : ∀ v : Place L F, f ∈ v.toValuationSubring → u ∈ v.toValuationSubring := by
      intro v hfV
      rw [Place.mem_iff_ord_nonneg v hu0]
      have hDv : D v = 0 := by
        rw [hD v]
        rcases eq_or_ne f 0 with hf0 | hf0
        · simp [hf0]
        · exact max_eq_left (neg_nonpos.mpr ((Place.mem_iff_ord_nonneg v hf0).1 hfV))
      have h1 := hord v
      rw [hMD, hDv, mul_zero, neg_zero] at h1
      exact h1
    refine ⟨fun V hV hfV => ?_, fun V hV hfV => ?_⟩
    · by_cases hVt : V = ⊤
      · rw [hVt]; exact ValuationSubring.mem_top u
      obtain ⟨v, rfl⟩ := mkPlace V hV hVt
      exact hreg v hfV
    · by_cases hVt : V = ⊤
      · rw [hVt]; exact ValuationSubring.mem_top _
      obtain ⟨v, rfl⟩ := mkPlace V hV hVt
      rcases eq_or_ne f 0 with hf0 | hf0
      ·
        subst hf0
        have huV : u ∈ v.toValuationSubring := hreg v v.toValuationSubring.zero_mem
        rcases Nat.eq_zero_or_pos M with hM | hM
        · subst hM; simpa using huV
        · rw [zero_pow hM.ne', inv_zero, mul_zero]; exact v.toValuationSubring.zero_mem
      · have hfi : 0 ≤ v.ord f⁻¹ := (Place.mem_iff_ord_nonneg v (inv_ne_zero hf0)).1 hfV
        rw [Place.ord_inv] at hfi
        have hDv : D v = -v.ord f := by rw [hD v]; exact max_eq_right hfi
        have h1 := hord v
        rw [hMD, hDv] at h1
        have hne : (f ^ M)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hf0)
        rw [Place.mem_iff_ord_nonneg v (mul_ne_zero hu0 hne), v.ord_mul hu0 hne,
          v.ord_inv, ← zpow_natCast, v.ord_zpow]
        nlinarith [h1]
  refine le_inf (Submodule.span_mono ?_) (Submodule.span_mono ?_)
  · rintro h ⟨u, hu, huL, hres⟩
    exact ⟨u, hu, (key u huL).1, hres⟩
  · rintro h ⟨u, hu, huL, hres⟩
    exact ⟨u, hu, (key u huL).2, hres⟩
