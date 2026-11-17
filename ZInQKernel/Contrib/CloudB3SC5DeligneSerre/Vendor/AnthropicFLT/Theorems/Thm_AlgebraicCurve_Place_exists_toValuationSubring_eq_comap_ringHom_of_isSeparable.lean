/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable (git blob 3fcae882f984edc3cc5ba17be2d35722cbe29e9a, sha256 33dd951d5ddc23e0ec419b69a5ece63b1824069bbb093b7cca199229ecdc0d1b).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom_of_isSeparable {K F F' : Type*} [Field K] [Field F] [Field F']
    [Algebra K F] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F]
    [Algebra.IsSeparable (IntermediateField.adjoin K ({x} : Set F)) F]
    (φ : F →+* F') (w : ValuationSubring F')
    (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) :
    ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by
  revert K F F' x φ w hwK hwx
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom_of_isSeparable.solution
