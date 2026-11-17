/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor (git blob 9f8139a9b6725901fdab1bfde8351d7755201a49, sha256 a69702b5b1b420f561efb92c01a0214a56e27f7da7e517c1796d659537684aec).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_mul_mem_lSpace_nsmul_succ_and_reflects_of_poleDivisor

set_option autoImplicit false
set_option maxHeartbeats 4800000

open AlgebraicCurve

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F]
    (x : F) (D : Divisor K F) (hD : ∀ v : Place K F, D v = max 0 (-v.ord x))
    (m : ℕ) :
    (∀ g ∈ LSpace ((m : ℕ) • D), x * g ∈ LSpace ((m + 1) • D)) ∧
    (∀ g ∈ LSpace ((m + 1) • D), x * g ∈ LSpace ((m + 1) • D) → g ∈ LSpace (m • D)) := by
  have hDnn : ∀ v, 0 ≤ D v := fun v => (hD v).symm ▸ le_max_left 0 _
  have hDmin : ∀ v, -D v = min 0 (v.ord x) := fun v => by
    rw [hD v]; omega
  have hsm : ∀ (n : ℕ) (v : Place K F),
      -((n • D : Divisor K F) v) = (n : ℤ) * min 0 (v.ord x) := fun n v => by
    simp only [Finsupp.coe_smul, Pi.smul_apply, nsmul_eq_mul]
    rw [neg_mul_eq_mul_neg, hDmin v]
  constructor
  ·
    intro g hg
    rw [mem_lSpace_iff_ord] at hg ⊢
    rcases eq_or_ne (x * g) 0 with h0 | hne
    · exact Or.inl h0
    refine Or.inr fun v => ?_
    obtain ⟨hx0, hg0⟩ := mul_ne_zero_iff.mp hne
    rcases hg with rfl | hg
    · exact absurd rfl hg0
    rw [hsm (m + 1), Place.ord_mul v hx0 hg0]
    have hgv := hg v; rw [hsm m] at hgv
    rcases le_or_gt 0 (v.ord x) with hxp | hxn
    ·
      have : min 0 (v.ord x) = 0 := min_eq_left hxp
      rw [this, mul_zero] at hgv ⊢
      linarith [hxp]
    ·
      have : min 0 (v.ord x) = v.ord x := min_eq_right (le_of_lt hxn)
      rw [this] at hgv ⊢
      push_cast; linarith
  ·
    intro g hg hxg
    rw [mem_lSpace_iff_ord] at hg hxg ⊢
    rcases eq_or_ne g 0 with rfl | hg0
    · exact Or.inl rfl
    refine Or.inr fun v => ?_
    rcases hg with rfl | hg; · exact absurd rfl hg0
    rw [hsm m]
    have hgv := hg v; rw [hsm (m+1)] at hgv
    rcases le_or_gt 0 (v.ord x) with hxp | hxn
    ·
      have hmin0 : min 0 (v.ord x) = 0 := min_eq_left hxp
      rw [hmin0, mul_zero] at hgv ⊢; exact hgv
    ·
      have hx0 : x ≠ 0 := fun h => absurd (h ▸ hxn) (lt_irrefl _ ∘ (Place.ord_zero v ▸ ·))
      rcases hxg with hxg0 | hxg
      · exact absurd hxg0 (mul_ne_zero hx0 hg0)
      have hxgv := hxg v; rw [hsm (m+1), Place.ord_mul v hx0 hg0] at hxgv
      have hmin : min 0 (v.ord x) = v.ord x := min_eq_right (le_of_lt hxn)
      rw [hmin] at hxgv ⊢
      push_cast at hxgv ⊢; linarith
