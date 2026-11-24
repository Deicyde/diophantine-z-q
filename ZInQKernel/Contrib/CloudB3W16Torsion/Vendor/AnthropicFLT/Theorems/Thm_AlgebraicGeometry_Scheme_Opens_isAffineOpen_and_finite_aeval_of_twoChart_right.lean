/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.Scheme.Opens.isAffineOpen_and_finite_aeval_of_twoChart_right
    {R : Type u} [CommRing R] [IsNoetherianRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    [IsProper c] [SmoothOfRelativeDimension 1 c] [GeometricallyIntegral c]
    (U V : C.Opens) (f : Γ(C, U)) (g : Γ(C, V))
    (hcov : U ⊔ V = ⊤) (hVU : U ⊓ V = C.basicOpen f)
    (hfg : (C.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op).hom f *
      (C.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom g = 1)
    (hft : ∀ (K : Type u) [Field K] [Algebra R K],
      letI := Scheme.TwoAffineOpenCover.algebraOfHom
        (pullback.snd c (Scheme.TwoAffineOpenCover.specMap R K))
        ((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)) ⁻¹ᵁ V);
      Transcendental K (((pullback.fst c (Scheme.TwoAffineOpenCover.specMap R K)).app V).hom g)) :
    IsAffineOpen V ∧
      (letI := Scheme.TwoAffineOpenCover.algebraOfHom c V
       (Polynomial.aeval g : R[X] →ₐ[R] Γ(C, V)).toRingHom.Finite) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_isAffineOpen_and_finite_aeval_of_twoChart_right.solution
