/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_JacJ1Iface
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_GoodReductionJacobian_RelativeGroupLawKernel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

theorem GoodReductionJacobian.RelativeGroupLaw.natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero
    (K : Type u) [Field K] [IsAlgClosed K] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of K))
    (L : RelativeGroupLaw K f) (hc : L.IsCommutative) (hA : AbelianSchemePropertyBundle K f)
    (g : ℕ) [SmoothOfRelativeDimension g f] (n : ℕ) (hn : (n : K) ≠ 0) :
    Nat.card {x : SchemeHomOver (𝟙 (Spec (CommRingCat.of K))) f //
        L.IsTorsionPoint (𝟙 (Spec (CommRingCat.of K))) n x} = n ^ (2 * g) := by p2m_exact_reverting @_root_.P2MW.S_GoodReductionJacobian_RelativeGroupLaw_natCard_isTorsionPoint_eq_pow_of_natCast_ne_zero.solution
