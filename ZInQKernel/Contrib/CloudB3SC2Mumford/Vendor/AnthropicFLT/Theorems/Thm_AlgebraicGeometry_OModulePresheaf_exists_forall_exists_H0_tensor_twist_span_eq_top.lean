/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top
Modified for the Z-in-Q kernel (2026-11-16, CloudB3SC2Mumford): local import paths are relocated
(modules already vendored in this repository are imported from their existing copies; `P2M.Util`
is the copy published under CloudW02Connectedness) and the upstream lakefile options are set as
`set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3SC2Mumford.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_forall_exists_H0_tensor_twist_span_eq_top
    {A : Type u} [CommRing A]
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : OModulePresheaf q) (hc : F.IsCoherent) (hq : F.IsQuasicoherent) :
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d →
      ∃ (m : ℕ) (σ : Fin m → ↥((F.tensor (ProjSpace.twist q ι d)).H0 (ProjSpace.stdCoverPullback ι))),
        ∀ s : (ProjSpace.stdCoverPullback ι).Idx 0,
          Submodule.span Γ(P, (ProjSpace.stdCoverPullback ι).inter s)
              (Set.range fun l : Fin m =>
                (σ l : (F.tensor (ProjSpace.twist q ι d)).cochain (ProjSpace.stdCoverPullback ι) 0) s) = ⊤ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_exists_forall_exists_H0_tensor_twist_span_eq_top.solution
