/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt

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

theorem AlgebraicGeometry.Scheme.Modules.exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt
    {k : Type u} [Field k] [Infinite k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [NoetherianSpace V]
    {n : ℕ} (N : Fin n → V.Modules) (hN : ∀ i, Scheme.Modules.IsInvertible (N i))
    (hbpf : ∀ (i : Fin n) (x : V), ∃ s : 𝟙_ V.Modules ⟶ N i, x ∉ (Scheme.Modules.zeroSchemeIdeal s).support)
    (B : Set V) (hB : IsClosed B) (hdim : topologicalKrullDim B < n) :
    ∃ s : ∀ i : Fin n, (𝟙_ V.Modules ⟶ N i),
      B ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) = ∅ := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Modules_exists_inter_iInter_support_zeroSchemeIdeal_eq_empty_of_topologicalKrullDim_lt.solution

