/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ. Apache-2.0.
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
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits

theorem Module.flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ
    {R : Type u} [CommRing R] {S : Type u} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (IsLocalRing.ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_flat_of_isLocalHom_of_isNoetherianRing_of_finite_of_tor_one_residueField_isZero_univ.solution

