/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X
Modification notice (2026-11-14, Cloud Worker 2): local import paths are relocated;
mathematical definitions, theorem statements, and proof bodies are unchanged.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjSpace
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X

open CategoryTheory AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

universe u
theorem AlgebraicGeometry.ProjSpace.map_preimage_basicOpen_X (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    (n : ℕ) (j : Fin (n + 1)) :
    ProjSpace.map R A n ⁻¹ᵁ Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) (MvPolynomial.X j)
      = Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) (MvPolynomial.X j) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_map_preimage_basicOpen_X.solution
