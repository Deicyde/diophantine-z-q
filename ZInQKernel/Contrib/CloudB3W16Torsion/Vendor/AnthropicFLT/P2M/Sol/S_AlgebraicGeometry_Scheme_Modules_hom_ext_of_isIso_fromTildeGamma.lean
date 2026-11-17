/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_Scheme_Modules_hom_ext_of_isIso_fromTildeGamma

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry Opposite

theorem solution {R : CommRingCat.{u}}
    {M N : (Spec (.of R)).Modules} [IsIso (Scheme.Modules.fromTildeΓ M)] (φ ψ : M ⟶ N)
    (h : ∀ m : Γ(M, ⊤), φ.app ⊤ m = ψ.app ⊤ m) : φ = ψ := by
  have hΓ : (moduleSpecΓFunctor (R := R)).map φ = (moduleSpecΓFunctor (R := R)).map ψ := by
    ext m
    exact h m
  have n1 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality φ
  have n2 := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality ψ
  simp only [Functor.comp_map, Functor.id_map] at n1 n2
  rw [← cancel_epi (Scheme.Modules.fromTildeΓ M)]
  change (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ φ =
    (Scheme.Modules.fromTildeΓNatTrans (R := R)).app M ≫ ψ
  refine n1.symm.trans ?_
  rw [hΓ]
  exact n2
