/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ. Apache-2.0.
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
import ZInQKernel.Contrib.OneProof.CharPolyPort.Vendor.AnthropicFLT.P2M.Sol.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

universe u

theorem IsLocalRing.flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ
    {R S S' : Type u} [CommRing R] [CommRing S] [CommRing S']
    [Algebra R S] [Algebra S S'] [Algebra R S'] [IsScalarTower R S S']
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing S']
    [IsLocalHom (algebraMap R S)] [IsLocalHom (algebraMap S S')]
    [IsNoetherianRing S] [IsNoetherianRing S'] :
    letI : Algebra (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) :=
      Ideal.Quotient.algebraQuotientOfLEComap (Ideal.map_le_iff_le_comap.mp (le_of_eq
        (by rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq R S S'])))
    Module.Flat R S' →
    Module.Flat (S ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S))
        (S' ⧸ (IsLocalRing.maximalIdeal R).map (algebraMap R S')) →
    Module.Flat S S' := by p2m_exact_reverting @_root_.P2MW.S_IsLocalRing_flat_of_isScalarTower_of_flat_of_flat_quotient_maximalIdeal_map_univ.solution

