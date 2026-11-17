/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH (git blob 257ba8c4fe6657fb1aced761fe2df9869320ea74, sha256 a440cc1c7820d12aff829f388be00622c577573abb5b33bba613427bc449db0b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XHOperators
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


theorem ModularCurve.nonempty_basis_fin_two_rationalTateModule_jH
    (M p : ℕ) [NeZero M] [Fact p.Prime] (H : Subgroup (ZMod M)ˣ) (S : Finset ℕ)
    (hin : ModularCurve.HeckeDiamondInputsHAll M H) :
    Nonempty (Module.Basis (Fin 2)
      ↥(Algebra.adjoin ℚ_[p] (Set.range fun g : CohCarrier.Gen M (↑S : Set ℕ) =>
          (ModularCurve.tateGenOpH M H (↑S : Set ℕ) p g).baseChange ℚ_[p]))
      (TensorProduct ℤ_[p] ℚ_[p] (TateModule p (ModularCurve.JH M H)))) := by
  revert M p H S hin
  exact @_root_.P2MW.S_ModularCurve_nonempty_basis_fin_two_rationalTateModule_jH.solution
