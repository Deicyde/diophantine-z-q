/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

theorem AlgebraicGeometry.RelEffCartierDiv.existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine
    {𝒞 S : Scheme.{u}} [IsAffine 𝒞] [IsAffine S] {f : 𝒞 ⟶ S} {r : ℕ}
    {X Y R : Scheme.{u}} [IsAffine X] [IsAffine Y] {gX : X ⟶ S} {gY : Y ⟶ S} {gR : R ⟶ S}
    (p : X ⟶ Y) (hp : p ≫ gY = gX)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] [Surjective p]
    (s t : R ⟶ X) (hs : s ≫ gX = gR) (ht : t ≫ gX = gR) (hR : IsPullback s t p p)
    (D : RelEffCartierDiv f r gX) (hD : D.pullbackAlong s hs = D.pullbackAlong t ht) :
    ∃! DY : RelEffCartierDiv f r gY, DY.pullbackAlong p hp = D := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_RelEffCartierDiv_existsUnique_pullbackAlong_eq_of_isPullback_of_isAffine.solution
