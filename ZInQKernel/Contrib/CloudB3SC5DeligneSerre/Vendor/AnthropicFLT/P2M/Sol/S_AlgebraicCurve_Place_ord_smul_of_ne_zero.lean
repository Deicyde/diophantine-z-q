/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ord_smul_of_ne_zero (git blob b4d4f714f82e999baf184370ce0150e8993a26a6, sha256 66a0041c7170de96dae4174919b724105f9a9af0a5c98874f11a452e6bd1e415).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_ord_smul_of_ne_zero

set_option autoImplicit false

open AlgebraicCurve

theorem solution {K F : Type*} [Field K] [Field F] [Algebra K F] (v : Place K F) {c : K} (hc : c ≠ 0) (x : F) : v.ord (c • x) = v.ord x := by
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [smul_zero]
  · have halg : algebraMap K F c ≠ 0 :=
      fun h => hc ((algebraMap K F).injective (by rw [h, map_zero]))
    have hunit : IsUnit (⟨algebraMap K F c, v.algebraMap_mem' c⟩ : v.toValuationSubring) := by
      refine isUnit_iff_exists_inv.mpr ⟨⟨algebraMap K F c⁻¹, v.algebraMap_mem' c⁻¹⟩, ?_⟩
      ext
      simp [mul_inv_cancel₀ halg]
    have h0 : v.ord (algebraMap K F c) = 0 := by
      have h1 : v.adicValuation (algebraMap K F c) = 1 :=
        (v.adicValuation_coe_eq_one_iff ⟨algebraMap K F c, v.algebraMap_mem' c⟩).mpr hunit
      simp [AlgebraicCurve.Place.ord, h1]
    rw [Algebra.smul_def, v.ord_mul halg hx0, h0, zero_add]
