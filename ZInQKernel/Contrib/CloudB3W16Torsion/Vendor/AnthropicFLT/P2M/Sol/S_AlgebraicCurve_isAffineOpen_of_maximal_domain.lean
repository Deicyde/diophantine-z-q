/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicCurve_isAffineOpen_of_maximal_domain. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Opens_isProper_toSpecPolynomial_of_maximal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Scheme_Opens_finite_preimage_singleton_toSpecPolynomial
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_valuationRing_stalk_of_smoothOfRelativeDimension_one
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicCurve_isAffineOpen_of_maximal_domain

universe u
open CategoryTheory
open CategoryTheory.Limits
open AlgebraicGeometry
open Polynomial
open AlgebraicGeometry.Polynomial

theorem solution
    {k : Type u} [Field k] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of k))
    [IsIntegral C] [IsProper c] [SmoothOfRelativeDimension 1 c]
    (U : C.Opens) [Nonempty U] (s : Γ(C, U))
    (hU : ∀ x : C, C.germToFunctionField U s ∈
      (algebraMap (C.presheaf.stalk x) C.functionField).range → x ∈ U)
    (hs : letI := (AlgebraicCurve.baseToFunctionField c).toAlgebra
      Transcendental k (C.germToFunctionField U s)) :
    IsAffineOpen U := by

  let φ : (U : Scheme.{u}) ⟶ Spec (CommRingCat.of k[X]) :=
    (U : Scheme.{u}).toSpecΓ ≫ Spec.map (CommRingCat.ofHom
      (Polynomial.eval₂RingHom ((U.ι ≫ c).appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
        (U.topIso.inv s)))

  haveI : IsProper φ := Scheme.Opens.isProper_toSpecPolynomial_of_maximal c
    (valuationRing_stalk_of_smoothOfRelativeDimension_one c) U s hU

  haveI : LocallyQuasiFinite φ := LocallyQuasiFinite.of_finite_preimage_singleton φ
    (Scheme.Opens.finite_preimage_singleton_toSpecPolynomial c U s hs)

  haveI : IsFinite φ := IsFinite.of_isProper_of_locallyQuasiFinite φ
  exact isAffine_of_isAffineHom φ
