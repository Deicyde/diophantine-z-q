/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry Polynomial

theorem AlgebraicGeometry.Scheme.Opens.finite_preimage_singleton_toSpecPolynomial
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [SmoothOfRelativeDimension 1 c] [QuasiCompact c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s))
    (p : Spec (CommRingCat.of k[X])) :
    (((U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))).base ⁻¹' {p}).Finite := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial.solution
