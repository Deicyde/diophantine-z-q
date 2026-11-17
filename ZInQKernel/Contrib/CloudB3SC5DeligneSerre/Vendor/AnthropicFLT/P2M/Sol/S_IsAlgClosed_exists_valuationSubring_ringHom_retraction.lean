/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction (git blob 704063c80a5b1bba07055ed1fdb4102b81721859, sha256 a3a957693f5a443400cc6e1b2c565bb7d9f7d01286d71e28f03e4ae44934f925).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Theorems.Thm_ValuationSubring_exists_ringHom_extend_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_IsAlgClosed_exists_valuationSubring_ringHom_retraction

set_option autoImplicit false

theorem solution
    (K K' : Type*) [Field K] [IsAlgClosed K] [Field K'] [Algebra K K'] :
    ∃ (A : ValuationSubring K') (hK : ∀ c : K, algebraMap K K' c ∈ A) (σ : A →+* K),
      RingHom.ker σ = IsLocalRing.maximalIdeal A ∧
      ∀ c : K, σ ⟨algebraMap K K' c, hK c⟩ = c := by
  let f : K →+* K' := algebraMap K K'
  let e : K ≃+* f.range := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h => f.injective (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  obtain ⟨O, hRO, ψ, hψ, hker⟩ :=
    ValuationSubring.exists_ringHom_extend_of_isAlgClosed (Ω := K) f.range e.symm.toRingHom
  refine ⟨O, fun c => hRO ⟨c, rfl⟩, ψ, hker, fun c => ?_⟩
  have h1 : ψ (Subring.inclusion hRO ⟨f c, ⟨c, rfl⟩⟩) = e.symm ⟨f c, ⟨c, rfl⟩⟩ := by
    rw [← RingHom.comp_apply, hψ]; rfl
  have h2 : e.symm ⟨f c, ⟨c, rfl⟩⟩ = c := by
    apply e.injective
    rw [RingEquiv.apply_symm_apply]
    rfl
  rw [h2] at h1
  exact h1
