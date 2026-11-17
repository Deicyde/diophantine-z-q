/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH (git blob 7b948ccd067e9fcddbe894a410488ac61d55eb4e, sha256 446da95321ecdec2c6fd5b641d9ed2c45fccafa644dd2778937c30e61a186e33).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_ComplexPlaceDictionaryOf
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_XH
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open scoped MatrixGroups Topology

theorem ModularCurve.exists_realizeOf_eventuallyEq_of_meromorphic_gammaH (M : ℕ) [NeZero M]
    (H : Subgroup (ZMod M)ˣ) (F : UpperHalfPlane → ℂ)
    (hmer : ∀ τ : UpperHalfPlane, MeromorphicAt (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) (τ : ℂ))
    (hinv : ∀ γ ∈ CohCarrier.GammaH M H, ∀ τ : UpperHalfPlane, F (γ • τ) = F τ)
    (hcusp : ∀ σ : SL(2, ℤ), ∃ C : ℝ,
      Asymptotics.IsBigO UpperHalfPlane.atImInfty (fun τ : UpperHalfPlane => F (σ • τ))
        fun τ : UpperHalfPlane => Real.exp (C * τ.im)) :
    ∃ x ∈ ModularCurve.laurentBaseChange ℂ (ModularCurve.xHFunctionField M H),
      ∀ τ : UpperHalfPlane, (fun z : ℂ => F (UpperHalfPlane.ofComplex z)) =ᶠ[𝓝[≠] (τ : ℂ)]
        fun z : ℂ => ModularCurve.realizeOf (CohCarrier.GammaH M H) x (UpperHalfPlane.ofComplex z) := by
  revert M H F hmer hinv hcusp
  exact @_root_.P2MW.S_ModularCurve_exists_realizeOf_eventuallyEq_of_meromorphic_gammaH.solution
