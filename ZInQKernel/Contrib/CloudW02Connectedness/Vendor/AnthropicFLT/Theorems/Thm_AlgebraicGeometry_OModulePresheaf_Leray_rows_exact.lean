/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafLerayDoubleComplex
import Mathlib.AlgebraicGeometry.Morphisms.Separated
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.OModulePresheaf.Leray.rows_exact
    {R : Type u} [CommRing R] {V' Z : Scheme.{u}} (p : V' ⟶ Z) (πZ : Z ⟶ Spec (.of R))
    [IsSeparated πZ] [IsSeparated (p ≫ πZ)] (K : Z.OrderedAffineCover) (K' : V'.OrderedAffineCover) :
    (∀ a b : ℕ, LinearMap.ker ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH (a + 1) b)
        ≤ LinearMap.range ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH a b)) ∧
      (∀ b : ℕ, LinearMap.ker ((OModulePresheaf.Leray.LerayDblCpx p πZ K K').dH 0 b)
        = LinearMap.range (OModulePresheaf.Leray.biAug p πZ K K' b)) ∧
      ∀ b : ℕ, Function.Injective (OModulePresheaf.Leray.biAug p πZ K K' b) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_Leray_rows_exact.solution
