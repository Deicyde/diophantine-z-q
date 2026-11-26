import ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.QuotientRegularity
import ZInQKernel.Contrib.OneProof.ModularEquationGeneric

/-! # Geometric tests for the cyclic-pair coordinates -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric3

open LeafModCurves ModelGeneric ModelGeneric2 ModularCurve

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000

variable {N : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- The regular Vélu coordinate satisfies the modular equation on the pinned
rational algebra, so the equation holds on every specialization. -/
theorem rationalQuotientCoordinate_modularEquation (data : ModularPolynomialData N) :
    (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom ℚ))).eval₂
      (Y0RationalJMap h₂).toRingHom (rationalQuotientCoordinate h₂).val = 0 := by
  let := (Y0RationalJMap h₂).toRingHom.toAlgebra
  apply (Y0RationalGenericJInclusion_injective h₂)
  rw [Polynomial.hom_eval₂, map_zero, (rationalQuotientCoordinate h₂).property]
  have h : (Y0RationalGenericJInclusion h₂).comp (Y0RationalJMap h₂).toRingHom =
      (algebraMap Qj (Y0RationalGenericJ h₂)).comp (algebraMap (Polynomial ℚ) Qj) :=
    RingHom.ext fun f =>
      (Algebra.TensorProduct.includeRight (R := Polynomial ℚ) (A := Qj)
        (B := Y0RationalAlgebra h₂)).commutes f
  rw [h, ← Polynomial.eval₂_map]
  exact genericQuotientJ_aeval h₂ data

/-- At every complex point, the second regular coordinate is a root of the
modular polynomial specialized at the pinned pair's source invariant. -/
theorem rationalQuotientCoordinate_complexRoot (data : ModularPolynomialData N)
    (x : Y0RationalAlgebra h₂ →ₐ[ℚ] ℂ) :
    (data.Φ.map (Polynomial.eval₂RingHom (Int.castRingHom ℂ)
      (pairJ (rationalPoints h₂ x)))).IsRoot (x (rationalQuotientCoordinate h₂).val) := by
  have h := congrArg x (rationalQuotientCoordinate_modularEquation h₂ data)
  change x.toRingHom _ = x.toRingHom 0 at h
  rw [Polynomial.hom_eval₂, map_zero, Polynomial.eval₂_map] at h
  rw [Polynomial.IsRoot, Polynomial.eval_map]
  convert h using 2
  apply Polynomial.ringHom_ext' (RingHom.ext_int _ _)
  rw [Polynomial.coe_eval₂RingHom, Polynomial.eval₂_X, rationalPoints_j]
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_X, Y0RationalJMap]
  change x (Y0RationalJ h₂) =
    x (Polynomial.aeval (Y0RationalJ h₂) (Polynomial.X : Polynomial ℚ))
  rw [Polynomial.aeval_X]

/-- At a transcendental source j the two actual invariants distinguish
complex cyclic-pair classes. -/
theorem complexPairClass_eq_of_transcendental_coordinates
    (a b : PairClasses ℂ N) (ht : Transcendental ℚ (pairJ a))
    (hj : pairJ a = pairJ b) (hq : pairQuotientJ a = pairQuotientJ b) :
    a = b := by
  obtain ⟨A, rfl⟩ := Quot.exists_rep a
  let := A.elliptic
  have hb : pairJ b = A.equation.j := hj.symm
  obtain ⟨D, hD⟩ := subgroupPair_surjective A.equation ⟨b, hb⟩
  have hDb : ((subgroupPair A.equation D).val : PairClasses ℂ N) = b :=
    congrArg Subtype.val hD
  rw [← hDb] at hq ⊢
  change A.equation.cyclicQuotientJ A.subgroup.val N =
    A.equation.cyclicQuotientJ D.val N at hq
  let data := Classical.choice (nonempty_modularPolynomialData N)
  have hinj := (FltCqj2.cyclicQuotientJBijOn_proof ℚ N data ℂ
    (Nat.cast_ne_zero.mpr (NeZero.ne N)) A.equation ht).injOn
  have hEq : A.subgroup = D := Subtype.ext (hinj A.subgroup.property D.property hq)
  cases A
  subst D
  rfl

omit [NeZero N] in
/-- The dilated first coordinate and the original second coordinate also
satisfy the modular equation of the complementary degree. This pins a
candidate intermediate invariant by two modular equations. -/
theorem complementary_modularEquation {d m : ℕ} [NeZero d] [NeZero m]
    (data : ModularPolynomialData m) :
    data.Φ.eval₂ (Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (jqN d))
      (jqN (d * m)) = 0 := by
  have h := congrArg (qExpand ℚ d) data.eval_eq_zero
  change qExpand ℚ d _ = qExpand ℚ d 0 at h
  rw [Polynomial.hom_eval₂, map_zero] at h
  have hcoeff : (qExpand ℚ d).comp evalAtJ =
      Polynomial.eval₂RingHom (Int.castRingHom (LaurentSeries ℚ)) (jqN d) := by
    apply Polynomial.ringHom_ext' (RingHom.ext_int _ _)
    simp [jqN]
  have hq : qExpand ℚ d (jqN m) = jqN (d * m) := qExpand_qExpand m d jq
  rw [hcoeff, hq] at h
  exact h

#print axioms rationalQuotientCoordinate_modularEquation
#print axioms rationalQuotientCoordinate_complexRoot
#print axioms complexPairClass_eq_of_transcendental_coordinates
#print axioms complementary_modularEquation

end WeierstrassCurve.ModelLevels.ModelGeneric3
