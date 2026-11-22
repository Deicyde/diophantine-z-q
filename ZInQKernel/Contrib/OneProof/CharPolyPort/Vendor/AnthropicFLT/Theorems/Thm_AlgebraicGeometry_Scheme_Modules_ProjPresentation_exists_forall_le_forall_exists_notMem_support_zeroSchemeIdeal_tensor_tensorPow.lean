/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow. Apache-2.0.
Modification notice (CloudB3 Worker13, 2026-11-15/16): ported to Lean 4.35.0 / Mathlib v4.35.0
(namespace-wrapped port on origin/cloud-b3/w13-recovery).
Modified for the Z-in-Q kernel (charpoly-port, 2026-11-17): the Worker13 port unwrapped into the
CloudB3W16Torsion conventions (original declaration namespaces; imports relocated to the
CloudB3W16Torsion vendor; the FLT-suffixed renames of CloudB3W16Torsion/NOTICE.md applied; port
shim commands removed). Mathematical statements and proofs retained, subject to Lean 4.35 adaptations
listed in scratch/charpoly-port/log.md.
Full original notices/credits: LICENSE, NOTICE.upstream, ATTRIBUTION.upstream.md in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesProjPresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory
open MonoidalCategory
open AlgebraicGeometry
open TopologicalSpace

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.Scheme.Modules.ProjPresentation.exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow
    {R : Type u} [CommRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    {H : X.Modules} {N : ℕ} (𝔓 : H.ProjPresentation f N) [IsAffineHom 𝔓.toProj]
    (L : X.Modules) (hL : Scheme.Modules.IsInvertible L) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : X,
      ∃ s : 𝟙_ X.Modules ⟶ L ⊗ H.tensorPowFLT n, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_ProjPresentation_exists_forall_le_forall_exists_notMem_support_zeroSchemeIdeal_tensor_tensorPow.solution

