/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_slot_algHom_modularFunctionFieldFullC_of_ord_neg (git blob 4c951546669b98610b058724c5d0aaeb0b1d5beb, sha256 a557927d92a5382c8a87d5fbf669c84301a27276b3631d54109787d6ca2ba9aa).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0ModL
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_PhiGen
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_slot_algHom_modularFunctionFieldFullC_of_ord_neg

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open ModularCurve AlgebraicCurve

theorem ModularCurve.exists_slot_algHom_modularFunctionFieldFullC_of_ord_neg
    (K : Type*) [Field K] (N : ℕ) [NeZero N] (hN : (N : K) ≠ 0)
    (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) N)
    (w : AlgebraicCurve.Place K (ModularCurve.modularFunctionFieldFullC K N))
    (hw : w.ord (⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K N⟩ :
      ModularCurve.modularFunctionFieldFullC K N) < 0) :
    ∃ a b : ℕ, a ∣ N ∧ b < N / a ∧ Nat.gcd (Nat.gcd a b) (N / a) = 1 ∧
      ∃ (_ : NeZero a) (ι : ModularCurve.modularFunctionFieldFullC K N →ₐ[K] LaurentSeries K),
        ι ⟨ModularCurve.jqModC K, ModularCurve.jqModC_mem_full K N⟩ =
            ModularCurve.qExpand K N (ModularCurve.jqModC K) ∧
        ι ⟨ModularCurve.jqNModC K N, ModularCurve.jqModCd_mem_full K N (dvd_refl N)⟩ =
            ModularCurve.qExpand K (a * a)
              (ModularCurve.qTwist (ζ ^ (b * a)) (ModularCurve.jqModC K)) ∧
        ∀ x, w.ord x * ((a * Nat.gcd a (N / a) : ℕ) : ℤ) = (ι x).order := by
  revert K N hN ζ hζ w hw
  exact @_root_.P2MW.S_ModularCurve_exists_slot_algHom_modularFunctionFieldFullC_of_ord_neg.solution
