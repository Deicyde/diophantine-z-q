/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed (git blob 3c53a14f919405db36972a374bb20618317caca9, sha256 985b86050f148319260e93ab23e5c861d62d9d16fd54c23a4e323eb4a256f391).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.FieldTheory.IsAlgClosed.Basic
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

theorem RingHom.exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed {A B K : Type*} [CommRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B] [Field K] [IsAlgClosed K] (χ : A →+* K) (hker : RingHom.ker (algebraMap A B) ≤ RingHom.ker χ) : ∃ ψ : B →+* K, ψ.comp (algebraMap A B) = χ := by
  revert A B K χ hker
  exact @_root_.P2MW.S_RingHom_exists_comp_algebraMap_eq_of_isIntegral_of_isAlgClosed.solution
