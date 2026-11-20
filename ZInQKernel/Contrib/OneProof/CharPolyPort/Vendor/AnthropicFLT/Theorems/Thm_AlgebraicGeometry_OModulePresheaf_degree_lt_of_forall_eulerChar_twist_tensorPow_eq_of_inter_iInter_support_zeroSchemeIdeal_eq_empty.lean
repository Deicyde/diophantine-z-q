/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_OModulePresheaf_degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_OModulePresheafTensor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesTensorPow
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_ModulesSectionZeroScheme
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_OModulePresheaf_degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty

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

theorem AlgebraicGeometry.OModulePresheaf.degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty
    {k : Type u} [Field k] {V : Scheme.{u}} (π : V ⟶ Spec (.of k)) [IsProper π]
    (K : V.OrderedAffineCover) (L : V.Modules)
    (hL : ∀ x : V, ∃ (U : V.Opens), x ∈ U ∧
      Nonempty ((Scheme.Modules.pullback U.ι).obj L ≅ SheafOfModules.unit U.toScheme.ringCatSheaf))
    {r : ℕ} (s : Fin r → (𝟙_ V.Modules ⟶ L))
    (G : OModulePresheaf π) (hc : G.IsCoherent) (hq : G.IsQuasicoherent)
    (Y : Closeds V) (hY : G.SupportedIn Y)
    (hs : (Y : Set V) ∩ ⋂ i, ((Scheme.Modules.zeroSchemeIdeal (s i)).support : Set V) = ∅)
    (p : Polynomial ℚ)
    (hp : ∀ n : ℕ, ((G.twist (L.tensorPowFLT n)).eulerChar K : ℚ) = p.eval (n : ℚ)) :
    p.degree < r := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_OModulePresheaf_degree_lt_of_forall_eulerChar_twist_tensorPow_eq_of_inter_iInter_support_zeroSchemeIdeal_eq_empty.solution

