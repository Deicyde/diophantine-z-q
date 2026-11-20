/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField

set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory CategoryTheory.Limits IsLocalRing

theorem Module.flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField
    {R : Type u} [CommRing R] {S : Type v} [CommRing S] [Algebra R S]
    [IsLocalRing R] [IsLocalRing S] [IsLocalHom (algebraMap R S)]
    [IsNoetherianRing R] [IsNoetherianRing S]
    {M : Type u} [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
    [Module.Finite S M]
    (hκ : IsZero (((Tor (ModuleCat.{u} R) 1).obj
      (ModuleCat.of R (ResidueField R))).obj (ModuleCat.of R M))) :
    Module.Flat R M := by p2m_exact_reverting @_root_.P2MW.S_Module_flat_of_isLocalHom_of_finite_of_isZero_tor_one_residueField.solution
