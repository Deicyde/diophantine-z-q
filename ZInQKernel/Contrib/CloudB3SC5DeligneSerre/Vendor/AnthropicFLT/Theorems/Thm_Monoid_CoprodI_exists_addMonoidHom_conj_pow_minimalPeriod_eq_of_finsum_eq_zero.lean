/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero (git blob 24a1fcf882accf9bc8ba994f2e1b5e4c40dd72e1, sha256 4f43afabbe54fba8e566781e33a1c4b72813adaf2baa1d684d0f6a9a5eecad20).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false
theorem Monoid.CoprodI.exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero
    (t : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))))
    (ht : t = Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 0)
                (Multiplicative.ofAdd 1) *
              Monoid.CoprodI.of (M := fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) (i := 1)
                (Multiplicative.ofAdd 1))
    (H : Subgroup (Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2)))))
    [H.FiniteIndex] (R : Type) [AddCommGroup R]
    (a : MulAction.orbitRel.Quotient (Subgroup.zpowers t)
          (Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H) → R)
    (ha : ∑ᶠ c, a c = 0) :
    ∃ φ : Additive H →+ R,
      ∀ (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))))
        (hg : g⁻¹ * t ^ Function.minimalPeriod (fun x => t • x)
                (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H) * g ∈ H),
        φ (Additive.ofMul ⟨_, hg⟩)
          = a (Quotient.mk (MulAction.orbitRel (Subgroup.zpowers t) _)
              (g : Monoid.CoprodI (fun i : Fin 2 => Multiplicative (ZMod (i.val + 2))) ⧸ H)) := by
  revert t ht H R a ha
  exact @_root_.P2MW.S_Monoid_CoprodI_exists_addMonoidHom_conj_pow_minimalPeriod_eq_of_finsum_eq_zero.solution
