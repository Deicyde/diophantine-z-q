/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_linearEquiv_twistObj_of_le_pullbackChart
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (π : X ⟶ Spec (.of A)) (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A))
    (m : ℕ) {i : Fin (N + 1)} {W : X.Opens} (hW : W ≤ ProjSpace.pullbackChart φ i) :
    ∃ e : ProjSpace.twistObj π φ m W ≃ₗ[Γ(X, W)] Γ(X, W),
      (∀ g : ProjSpace.twistObj π φ m W,
        ProjSpace.restrictFun (inf_le_left : W ⊓ ProjSpace.pullbackChart φ i ≤ W) (e g) = g.val i) ∧
      (∀ (a : Γ(X, W)) (j : Fin (N + 1)),
        (e.symm a).val j =
          ProjSpace.restrictFun (inf_le_right : W ⊓ ProjSpace.pullbackChart φ j ≤ ProjSpace.pullbackChart φ j)
              (ProjSpace.frameUnit φ j i) ^ m *
            ProjSpace.restrictFun (inf_le_left : W ⊓ ProjSpace.pullbackChart φ j ≤ W) a) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_ProjSpace_exists_linearEquiv_twistObj_of_le_pullbackChart.solution
