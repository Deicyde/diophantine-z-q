/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicCurve_Place_sum_ramification_evalAt_eq (git blob 1a2e07daf5ce9a15f34df8c826b54d4fd8175666, sha256 a23468719c7007adf926a738776142e0cdcac8022242f1b968ec5e1537611533).
Ported to Lean 4.35 / Mathlib 56a0058; changes from upstream are marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_IsCurveOver
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CanonicalDivisor
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_RegularDifferentials
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_PlaceEvaluation
import ZInQKernel.Contrib.CloudB3SC5DeligneSerre.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicCurve_Place_sum_ramification_evalAt_eq

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false


open AlgebraicCurve IntermediateField

theorem AlgebraicCurve.Place.sum_ramification_evalAt_eq {F : Type*} [Field F] [Algebra ℂ F] [IsCurveOver ℂ F]
    [HasCanonicalDivisor (K := ℂ) (F := F)]
    {x : F} (htr : Transcendental ℂ x) [FiniteDimensional (↥(adjoin ℂ ({x} : Set F))) F]
    (B : Finset ℂ)
    (hB : ∀ (b : ℂ) (w : Place ℂ F), x ∈ w.toValuationSubring → Place.evalAt w x = b →
      (w.ord (x - algebraMap ℂ F b)).toNat ≠ 1 → b ∈ B)
    (t : ℂ → Finset (Place ℂ F))
    (ht : ∀ b ∈ B, ∀ w : Place ℂ F, w ∈ t b ↔ x ∈ w.toValuationSubring ∧ Place.evalAt w x = b)
    (p : Finset (Place ℂ F)) (hp : ∀ w : Place ℂ F, w ∈ p ↔ x ∉ w.toValuationSubring) :
    (∑ b ∈ B, ∑ w ∈ t b, (((w.ord (x - algebraMap ℂ F b)).toNat : ℤ) - 1)) +
        ∑ w ∈ p, (((w.ord x⁻¹).toNat : ℤ) - 1) =
      2 * (Module.finrank ℂ ↥(regularDifferentials ℂ F) : ℤ) - 2 +
        2 * (Module.finrank (↥(adjoin ℂ ({x} : Set F))) F : ℤ) := by
  revert F x htr B hB t ht p hp
  exact @_root_.P2MW.S_AlgebraicCurve_Place_sum_ramification_evalAt_eq.solution
