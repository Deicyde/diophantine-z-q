/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgHom_injective_of_finite_of_isFractionRing. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgHom_injective_of_finite_of_isFractionRing

set_option backward.isDefEq.respectTransparency false

universe u
theorem AlgHom.injective_of_finite_of_isFractionRing {k A B K : Type u} [Field k]
    [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Field K] [Algebra k K] [Algebra A K] [IsFractionRing A K] [IsScalarTower k A K]
    [Algebra B K] [IsFractionRing B K] [IsScalarTower k B K]
    (φ : A →ₐ[k] B) (hφ : φ.toRingHom.Finite) : Function.Injective φ := by p2m_exact_reverting @_root_.P2MW.S_AlgHom_injective_of_finite_of_isFractionRing.solution
