/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicCurve_Place_ramificationIndexAlong_comp (git blob 0e10dc324ef975ab62574221d8bc0497d66f1561, sha256 2cd919a82b2a44b63c3a5da9d5ca739d5cecf89e71da0184098e76b32ea1ac16).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_Correspondence
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicCurve_Place_restrictAlong_restrictAlong

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicCurve_Place_ramificationIndexAlong_comp

set_option autoImplicit false

open IsDedekindDomain AlgebraicCurve

theorem solution {K F F' F'' : Type*} [Field K] [Field F] [Field F'] [Field F''] [Algebra K F] [Algebra K F'] [Algebra K F''] (φ : F →ₐ[K] F') (χ : F' →ₐ[K] F'') (hφ : φ.toRingHom.IsIntegral) (hχ : χ.toRingHom.IsIntegral) (hχφ : (χ.comp φ).toRingHom.IsIntegral) (W : Place K F'') : Place.ramificationIndexAlong (χ.comp φ) W = Place.ramificationIndexAlong χ W * Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible
    (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring
  have hπord : (W.restrictAlong (χ.comp φ) hχφ).ord
      ((π : (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring) : F) = 1 :=
    (W.restrictAlong (χ.comp φ) hχφ).ord_coe_irreducible hπ
  set f : F := ((π : (W.restrictAlong (χ.comp φ) hχφ).toValuationSubring) : F) with hf
  have h1 : W.ord ((χ.comp φ) f) = (Place.ramificationIndexAlong (χ.comp φ) W : ℤ) := by
    rw [W.ord_restrictAlong (χ.comp φ) hχφ, hπord, mul_one]
  have h2 : W.ord ((χ.comp φ) f)
      = (Place.ramificationIndexAlong χ W : ℤ)
          * (Place.ramificationIndexAlong φ (W.restrictAlong χ hχ) : ℤ) := by
    rw [AlgHom.comp_apply, W.ord_restrictAlong χ hχ, (W.restrictAlong χ hχ).ord_restrictAlong φ hφ,
      AlgebraicCurve.Place.restrictAlong_restrictAlong φ χ hφ hχ hχφ, hπord, mul_one]
  exact_mod_cast h1.symm.trans h2
