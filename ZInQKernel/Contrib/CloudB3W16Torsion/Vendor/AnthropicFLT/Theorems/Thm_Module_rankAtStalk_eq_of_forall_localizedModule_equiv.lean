/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_rankAtStalk_eq_of_forall_localizedModule_equiv. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_rankAtStalk_eq_of_forall_localizedModule_equiv

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

theorem Module.rankAtStalk_eq_of_forall_localizedModule_equiv
    {R A : Type u} [CommRing R] [CommRing A] [Algebra R A] [Module.Finite R A]
    (M N : Type u) [AddCommGroup M] [Module R M] [Module A M] [IsScalarTower R A M]
    [Module.Finite R M] [Module.Flat R M]
    [AddCommGroup N] [Module R N] [Module A N] [IsScalarTower R A N]
    [Module.Finite R N] [Module.Flat R N] (s : Set A) (hs : Ideal.span s = ⊤)
    (H : ∀ h ∈ s, Nonempty
      (LocalizedModule (Submonoid.powers h) M ≃ₗ[A] LocalizedModule (Submonoid.powers h) N)) :
    Module.rankAtStalk (R := R) M = Module.rankAtStalk N := by p2m_exact_reverting @_root_.P2MW.S_Module_rankAtStalk_eq_of_forall_localizedModule_equiv.solution
