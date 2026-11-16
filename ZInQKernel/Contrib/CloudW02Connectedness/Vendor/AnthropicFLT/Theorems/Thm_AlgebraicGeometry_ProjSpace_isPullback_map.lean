/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_ProjSpace_isPullback_map
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_isPullback_map

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.ProjSpace.isPullback_map (R A : Type u) [CommRing R] [CommRing A] [Algebra R A] (n : ℕ) :
    IsPullback (ProjSpace.map R A n) (ProjSpace.π A n) (ProjSpace.π R n)
      (Spec.map (CommRingCat.ofHom (algebraMap R A))) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_isPullback_map.solution
