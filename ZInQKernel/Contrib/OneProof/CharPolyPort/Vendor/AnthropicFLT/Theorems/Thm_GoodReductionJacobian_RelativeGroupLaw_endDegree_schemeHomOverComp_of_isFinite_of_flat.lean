/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelEndomorphismExtension
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativeGroupLawEndDegree
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.endDegree_schemeHomOverComp_of_isFinite_of_flat
    (K : Type u) [Field K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]
    [PreconnectedSpace A] (L : RelativeGroupLaw K f) (β γ : SchemeHomOver f f)
    [IsFinite β.1] [Flat β.1] [IsFinite γ.1] [Flat γ.1] :
    L.endDegree (NeronModelInfra.schemeHomOverComp β γ) = L.endDegree β * L.endDegree γ := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_endDegree_schemeHomOverComp_of_isFinite_of_flat.solution

