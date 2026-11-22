/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Theorems.Thm_Ideal_height_eq_height_under_of_isIntegrallyClosed_of_isIntegral
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false
-- [port] The normal-polynomial instance search is larger in the pinned Mathlib.
set_option maxHeartbeats 2000000

namespace P2MW.S_Ideal_height_eq_height_under_of_finiteType_of_isIntegral

set_option autoImplicit false

universe u

theorem solution
    (k A B : Type u) [Field k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B]
    [Algebra A B] [IsScalarTower k A B] [FaithfulSMul A B] [Algebra.IsIntegral A B]
    (q : Ideal B) [q.IsPrime] :
    q.height = (q.under A).height := by
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k A
  haveI : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing k B
  obtain ⟨d, g, hinj, hint⟩ := exists_integral_inj_algHom_of_fg k A
  -- [port] Cache the standard polynomial normality instance before adding tower algebras.
  haveI : IsIntegrallyClosed (MvPolynomial (Fin d) k) :=
    UniqueFactorizationMonoid.instIsIntegrallyClosed
  letI : Algebra (MvPolynomial (Fin d) k) A := g.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin d) k) B := ((algebraMap A B).comp g.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin d) k) A B := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : FaithfulSMul (MvPolynomial (Fin d) k) A :=
    (faithfulSMul_iff_algebraMap_injective _ A).mpr hinj
  haveI : FaithfulSMul (MvPolynomial (Fin d) k) B :=
    (faithfulSMul_iff_algebraMap_injective _ B).mpr
      ((FaithfulSMul.algebraMap_injective A B).comp hinj)
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k) A := ⟨hint⟩
  haveI : Algebra.IsIntegral (MvPolynomial (Fin d) k) B := Algebra.IsIntegral.trans A
  rw [Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) B q,
    Ideal.height_eq_height_under_of_isIntegrallyClosed_of_isIntegral (MvPolynomial (Fin d) k) A
      (q.under A), Ideal.under_under]
