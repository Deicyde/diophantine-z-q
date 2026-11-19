/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom (git blob 731b77933a322bf6e656a7c15e057f9faaf6cd25, sha256 8aa8f0e76746255440058675dd20772bd89715f9e0a32e0704c049af0a7d351e).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem AlgebraicCurve.Place.exists_toValuationSubring_eq_comap_ringHom {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [CharZero K] (x : F) [FiniteDimensional (IntermediateField.adjoin K ({x} : Set F)) F] (φ : F →+* F') (w : ValuationSubring F') (hwK : ∀ a : K, φ (algebraMap K F a) ∈ w) (hwx : ∃ y : F, φ y ∉ w) : ∃ v : AlgebraicCurve.Place K F, v.toValuationSubring = w.comap φ := by
  revert K F F' x φ w hwK hwx
  exact @_root_.P2MW.S_AlgebraicCurve_Place_exists_toValuationSubring_eq_comap_ringHom.solution
