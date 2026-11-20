/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Theorems.Thm_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicCurve_CurveModel
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.Hom.ord_eq_of_ker_pow_ideal_eq_span
    {K : Type u} [Field K] {X : Scheme.{u}} (x : X ⟶ Spec (CommRingCat.of K))
    [IsIntegral X] [IsSeparated x]
    (P : Spec (CommRingCat.of K) ⟶ X) (hP : P ≫ x = 𝟙 _) (n : ℕ)
    (U : X.Opens) (hU : IsAffineOpen U) (g : Γ(X, U)) (hg : (P.ker ^ n).ideal ⟨U, hU⟩ = Ideal.span {g})
    (y : X) (hyU : y ∈ U) (hy : IsClosed ({y} : Set X))
    (v : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      AlgebraicCurve.Place K X.functionField)
    (hv : letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
      (algebraMap (X.presheaf.stalk y) X.functionField).range = v.toValuationSubring.toSubring) :
    letI := (AlgebraicCurve.baseToFunctionField x).toAlgebra
    haveI : Nonempty U := ⟨⟨y, hyU⟩⟩
    (P.base (IsLocalRing.closedPoint K) = y → v.ord (algebraMap Γ(X, U) X.functionField g) = n) ∧
      (P.base (IsLocalRing.closedPoint K) ≠ y → v.ord (algebraMap Γ(X, U) X.functionField g) = 0) := by p2m_exact_reverting @_root_.P2MW.S_AlgebraicGeometry_Scheme_Hom_ord_eq_of_ker_pow_ideal_eq_span.solution
