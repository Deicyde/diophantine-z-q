/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle. Apache-2.0.
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
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra GoodReductionJacobian
set_option maxHeartbeats 800000 in

theorem GoodReductionJacobian.RelativeGroupLaw.flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle
    {R : Type u} [CommRing R] [IsNoetherianRing R]
    {J : Scheme.{u}} {f : J ⟶ Spec (CommRingCat.of R)} (L : RelativeGroupLaw R f)
    (hJ : AbelianSchemePropertyBundle R f)
    (hcomm : ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) (x y : SchemeHomOver t f),
      L.mul t x y = L.mul t y x)
    (n : ℕ) (hn : 0 < n) (hfin : IsFinite (L.schemeNsmul n)) :
    Flat (L.schemeNsmul n) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_flat_schemeNsmul_of_isFinite_of_abelianSchemePropertyBundle.solution

