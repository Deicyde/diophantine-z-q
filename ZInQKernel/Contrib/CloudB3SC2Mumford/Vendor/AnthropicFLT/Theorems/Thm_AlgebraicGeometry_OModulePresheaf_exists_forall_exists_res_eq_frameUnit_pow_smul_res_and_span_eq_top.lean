/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top
    {A : Type u} [CommRing A] {N : ℕ} {X : Scheme.{u}}
    (φ : X ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) A)) [IsAffineHom φ]
    {π : X ⟶ Spec (CommRingCat.of A)} (F : OModulePresheaf π) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      ∃ (m : ℕ) (s : Fin m → ∀ i : Fin (N + 1), F.obj (ProjSpace.pullbackChart φ i)),
        (∀ (a : Fin m) (i j : Fin (N + 1)),
          F.res (ProjSpace.pullbackOverlap_le_left φ i j) (s a i) =
            ProjSpace.restrictFun (ProjSpace.pullbackOverlap_le_left φ i j) (ProjSpace.frameUnit φ i j) ^ d •
              F.res (ProjSpace.pullbackOverlap_le_right φ i j) (s a j)) ∧
        ∀ i : Fin (N + 1),
          Submodule.span Γ(X, ProjSpace.pullbackChart φ i) (Set.range fun a : Fin m => s a i) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_res_eq_frameUnit_pow_smul_res_and_span_eq_top.solution
