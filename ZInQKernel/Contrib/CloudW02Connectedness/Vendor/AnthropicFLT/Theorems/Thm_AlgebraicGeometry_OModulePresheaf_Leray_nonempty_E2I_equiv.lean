/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.LinearAlgebra.Quotient.Pi
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.nonempty_E2I_equiv
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    (∀ b : ℕ, Nonempty (DoubleComplex.E₂I (OModulePresheaf.Leray.LerayDblCpx p πZ K K') 0 b
        ≃ₗ[R] (OModulePresheaf.Leray.relHPresheaf p πZ K' b).H0 K)) ∧
      ∀ a b : ℕ, Nonempty (DoubleComplex.E₂I (OModulePresheaf.Leray.LerayDblCpx p πZ K K') (a + 1) b
        ≃ₗ[R] (OModulePresheaf.Leray.relHPresheaf p πZ K' b).HSucc K a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_nonempty_E2I_equiv.solution
