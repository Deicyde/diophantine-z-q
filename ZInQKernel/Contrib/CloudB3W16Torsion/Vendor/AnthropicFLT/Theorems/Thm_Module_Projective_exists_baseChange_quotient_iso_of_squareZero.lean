/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_Module_Projective_exists_baseChange_quotient_iso_of_squareZero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_Module_Projective_exists_baseChange_quotient_iso_of_squareZero

set_option backward.isDefEq.respectTransparency false

universe u

set_option autoImplicit false

open TensorProduct

theorem Module.Projective.exists_baseChange_quotient_iso_of_squareZero
    {R : Type u} [CommRing R] (I : Ideal R) (hI : I ^ 2 = ⊥)
    (P : Type u) [AddCommGroup P] [Module (R ⧸ I) P]
    [Module.Projective (R ⧸ I) P] [Module.Finite (R ⧸ I) P] :
    ∃ (P' : Type u) (_ : AddCommGroup P') (_ : Module R P'),
      Module.Projective R P' ∧ Module.Finite R P' ∧
      Nonempty (((R ⧸ I) ⊗[R] P') ≃ₗ[R ⧸ I] P) := by p2m_exact_reverting @_root_.P2MW.S_Module_Projective_exists_baseChange_quotient_iso_of_squareZero.solution
