/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus_complex (git blob 3d0df29f9e1f4cacf5ff62cd760c65f9e71e9267, sha256 9f2bf23979c72c2db96f33e8d19aa6f7f9540e36cabe90279022d2b20f49dbd0).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus_complex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve
theorem AlgebraicCurve.Pic0.natCard_torsion_prime_eq_pow_genus_complex (F : Type*) [Field F]
    [Algebra ℂ F]
    (hfg : ∃ x : F, Transcendental ℂ x ∧ FiniteDimensional (IntermediateField.adjoin ℂ ({x} : Set F)) F)
    [IsCurveOver ℂ F] [HasCanonicalDivisor (K := ℂ) (F := F)]
    (p : ℕ) [Fact p.Prime] :
    Nat.card (Pic0.torsion ℂ F p) = p ^ (2 * genus ℂ F) := by
  revert F hfg p
  exact @_root_.P2MW.S_AlgebraicCurve_Pic0_natCard_torsion_prime_eq_pow_genus_complex.solution
