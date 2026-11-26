import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.CoordinateLifting
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.CoverTransition
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.GeneratorOrbits
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.MultiplicationCoordinates

/-! # Multiplication by a unit on the relative exact-order cover -/

namespace WeierstrassCurve.ModelLevels

open Polynomial WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

variable {A : Type*} [CommRing A] (W : WeierstrassCurve A) [W.IsElliptic]
  {n : ℕ} (hN : IsUnit ((n + 3 : ℕ) : A))

private noncomputable def evaluateOnGenerator (p : A[X][Y]) : ExactOrderAlgebra W hN :=
  (p.map (mapRingHom (algebraMap A (ExactOrderAlgebra W hN)))).evalEval
    (generatorX W hN) (generatorY W hN)

private theorem evaluateOnGenerator_map {k : Type*} [Field k] [Algebra A k]
    (f : ExactOrderAlgebra W hN →ₐ[A] k) (p : A[X][Y]) :
    f (evaluateOnGenerator W hN p) =
      (p.map (mapRingHom (algebraMap A k))).evalEval (f (generatorX W hN)) (f (generatorY W hN)) := by
  unfold evaluateOnGenerator
  change f.toRingHom _ = _
  rw [← map_mapRingHom_evalEval, Polynomial.map_map, mapRingHom_comp,
    show f.toRingHom.comp (algebraMap A (ExactOrderAlgebra W hN)) = algebraMap A k from
      f.comp_algebraMap]
  rfl

private noncomputable def multipleDenominator (a : (ZMod (n + 3))ˣ) :
    ExactOrderAlgebra W hN :=
  evaluateOnGenerator W hN (W.ψ ((a : ZMod (n + 3)).val : ℤ))

private theorem multipleDenominator_isUnit (a : (ZMod (n + 3))ˣ) :
    IsUnit (multipleDenominator W hN a) := by
  apply isUnit_of_nonzero_at_fields (A := A)
  intro k _ _ f
  classical
  obtain ⟨h, he⟩ := exactOrderFibrePoints_coordinates W hN f
  have ho := (exactOrderFibrePoints W hN f).2
  rw [he] at ho
  rw [multipleDenominator, evaluateOnGenerator_map, ← W.map_ψ]
  exact divisionDenominator_ne_zero (W.map (algebraMap A k)) h (by omega) ho
    (ZMod.val_coe_unit_coprime a)

private noncomputable def inverseDenominator (a : (ZMod (n + 3))ˣ) : ExactOrderAlgebra W hN :=
  ((multipleDenominator_isUnit W hN a).unit⁻¹ : (ExactOrderAlgebra W hN)ˣ)

private theorem inverseDenominator_map {k : Type*} [Field k] [Algebra A k]
    (f : ExactOrderAlgebra W hN →ₐ[A] k) (a : (ZMod (n + 3))ˣ) :
    f (inverseDenominator W hN a) = (f (multipleDenominator W hN a))⁻¹ := by
  let u := (multipleDenominator_isUnit W hN a).unit
  have h := (multipleDenominator_isUnit W hN a).unit_spec
  change f.toMonoidHom (↑u⁻¹) = _
  rw [← Units.coe_map_inv f.toMonoidHom u, Units.val_inv_eq_inv_val]
  change (f (↑u : ExactOrderAlgebra W hN))⁻¹ = _
  exact congrArg (fun z => (f z)⁻¹) h

private noncomputable def multipleX (a : (ZMod (n + 3))ˣ) : ExactOrderAlgebra W hN :=
  evaluateOnGenerator W hN (W.φ ((a : ZMod (n + 3)).val : ℤ)) *
    inverseDenominator W hN a ^ 2

private noncomputable def multipleY (a : (ZMod (n + 3))ˣ) : ExactOrderAlgebra W hN :=
  evaluateOnGenerator W hN (W.ωe ((a : ZMod (n + 3)).val : ℤ)) *
    inverseDenominator W hN a ^ 3

private theorem multiple_coordinate_lift [IsDomain A] (a : (ZMod (n + 3))ˣ) :
    ∃ g : ExactOrderAlgebra W hN →ₐ[A] ExactOrderAlgebra W hN,
      g (generatorX W hN) = multipleX W hN a ∧ g (generatorY W hN) = multipleY W hN a := by
  let : IsReduced (ExactOrderAlgebra W hN) := exactOrderAlgebra_isReduced W hN
  apply exists_exactOrder_map_of_fields W hN
  intro k _ _ f
  classical
  let V := W.map (algebraMap A k)
  let e := exactOrderFibrePoints (k := k) W hN
  let P : Generators V.toAffine.Point (n + 3) := e f
  let g := e.symm (a • P)
  have hg : (e g : Generators V.toAffine.Point (n + 3)) = a • P := e.apply_symm_apply _
  obtain ⟨h, he⟩ := exactOrderFibrePoints_coordinates W hN f
  have ho : addOrderOf (Point.some (f (generatorX W hN)) (f (generatorY W hN)) h) = n + 3 :=
    he ▸ (e f).2
  obtain ⟨h', he'⟩ := coprimeMultiple_coordinates V h (by omega) ho (ZMod.val_coe_unit_coprime a)
  obtain ⟨h'', he''⟩ := exactOrderFibrePoints_coordinates W hN g
  have H : (e g).1 = Point.some _ _ h' := by
    rw [show (e g).1 = (a • P).1 from congrArg Subtype.val hg, generatorAction_apply]
    change (a : ZMod (n + 3)).val • (e f).1 = _
    rw [he]
    exact he'
  rw [he''] at H
  rw [Point.some.injEq] at H
  refine ⟨g, ?_, ?_⟩
  · rw [multipleX, map_mul, map_pow, evaluateOnGenerator_map, inverseDenominator_map,
      multipleDenominator, evaluateOnGenerator_map, ← W.map_ψ, ← W.map_φ]
    simpa only [div_eq_mul_inv, inv_pow] using H.1
  · rw [multipleY, map_mul, map_pow, evaluateOnGenerator_map, inverseDenominator_map,
      multipleDenominator, evaluateOnGenerator_map, ← W.map_ψ, ← W.map_ωe]
    simpa only [div_eq_mul_inv, inv_pow] using H.2

/-- The pullback of multiplication by the unit on the exact-order cover.
Its coordinates are the Jacobian division formulas, with powers of the
unit denominator inverted in the coordinate algebra. -/
noncomputable def exactOrderUnitHom [IsDomain A] (a : (ZMod (n + 3))ˣ) :
    ExactOrderAlgebra W hN →ₐ[A] ExactOrderAlgebra W hN :=
  (multiple_coordinate_lift W hN a).choose

/-- The map on the coordinate algebra induces multiplication by the unit
on every specialized point, in characteristic zero or positive
characteristic prime to the level. -/
theorem exactOrderUnitHom_point [IsDomain A] {k : Type*} [Field k] [Algebra A k] [DecidableEq k]
    (a : (ZMod (n + 3))ˣ) (f : ExactOrderAlgebra W hN →ₐ[A] k) :
    (exactOrderFibrePoints W hN (f.comp (exactOrderUnitHom W hN a)) :
      Generators (W.map (algebraMap A k)).toAffine.Point (n + 3)) =
        (generatorAction (G := (W.map (algebraMap A k)).toAffine.Point) (N := n + 3)).smul a
          (exactOrderFibrePoints W hN f) := by
  let g := exactOrderUnitHom W hN a
  have hx : g (generatorX W hN) = multipleX W hN a := (multiple_coordinate_lift W hN a).choose_spec.1
  have hy : g (generatorY W hN) = multipleY W hN a := (multiple_coordinate_lift W hN a).choose_spec.2
  obtain ⟨hp, he⟩ := exactOrderFibrePoints_coordinates W hN f
  obtain ⟨hg, he'⟩ := exactOrderFibrePoints_coordinates W hN (f.comp g)
  have ho := (exactOrderFibrePoints W hN f).2
  rw [he] at ho
  obtain ⟨h, hm⟩ := coprimeMultiple_coordinates (W.map (algebraMap A k)) hp (by omega) ho
    (ZMod.val_coe_unit_coprime a)
  apply Subtype.ext
  change (exactOrderFibrePoints W hN (f.comp g)).1 =
    (a : ZMod (n + 3)).val • (exactOrderFibrePoints W hN f).1
  rw [he', he, hm, Point.some.injEq]
  change f (g (generatorX W hN)) = _ ∧ f (g (generatorY W hN)) = _
  rw [hx, hy]
  simp only [multipleX, multipleY, map_mul, map_pow, inverseDenominator_map,
    multipleDenominator, evaluateOnGenerator_map, ← W.map_ψ, ← W.map_φ, ← W.map_ωe,
    div_eq_mul_inv, inv_pow, and_self]

private theorem exactOrderUnitHom_one [IsDomain A] :
    exactOrderUnitHom W hN 1 = AlgHom.id A _ := by
  let : IsReduced (ExactOrderAlgebra W hN) := exactOrderAlgebra_isReduced W hN
  ext x
  apply eq_of_eq_at_fields (A := A)
  intro k _ _ f
  classical
  have h : f.comp (exactOrderUnitHom W hN 1) = f := by
    apply (exactOrderFibrePoints W hN).injective
    let P : Generators (W.map (algebraMap A k)).toAffine.Point (n + 3) :=
      exactOrderFibrePoints W hN f
    exact (exactOrderUnitHom_point W hN 1 f).trans (one_smul _ P)
  exact DFunLike.congr_fun h x

private theorem exactOrderUnitHom_mul [IsDomain A] (a b : (ZMod (n + 3))ˣ) :
    exactOrderUnitHom W hN (a * b) =
      (exactOrderUnitHom W hN a).comp (exactOrderUnitHom W hN b) := by
  let : IsReduced (ExactOrderAlgebra W hN) := exactOrderAlgebra_isReduced W hN
  ext x
  apply eq_of_eq_at_fields (A := A)
  intro k _ _ f
  classical
  have h : f.comp (exactOrderUnitHom W hN (a * b)) =
      (f.comp (exactOrderUnitHom W hN a)).comp (exactOrderUnitHom W hN b) := by
    apply (exactOrderFibrePoints W hN).injective
    change (_ : Generators (W.map (algebraMap A k)).toAffine.Point (n + 3)) = _
    rw [exactOrderUnitHom_point, exactOrderUnitHom_point, exactOrderUnitHom_point, mul_comm a b]
    let P : Generators (W.map (algebraMap A k)).toAffine.Point (n + 3) :=
      exactOrderFibrePoints W hN f
    change (b * a) • P = b • (a • P)
    exact mul_smul b a P
  exact DFunLike.congr_fun h x

/-- Multiplication by units as algebra automorphisms of the exact-order
cover over an elliptic coefficient domain. -/
noncomputable def exactOrderUnitAut [IsDomain A] :
    (ZMod (n + 3))ˣ →* (ExactOrderAlgebra W hN ≃ₐ[A] ExactOrderAlgebra W hN) where
  toFun a := AlgEquiv.ofAlgHom (exactOrderUnitHom W hN a) (exactOrderUnitHom W hN a⁻¹)
    (by rw [← exactOrderUnitHom_mul, mul_inv_cancel, exactOrderUnitHom_one])
    (by rw [← exactOrderUnitHom_mul, inv_mul_cancel, exactOrderUnitHom_one])
  map_one' := AlgEquiv.ext fun x => DFunLike.congr_fun (exactOrderUnitHom_one W hN) x
  map_mul' a b := AlgEquiv.ext fun x => DFunLike.congr_fun (exactOrderUnitHom_mul W hN a b) x

/-- The algebra automorphism acts on geometric generators by multiplication
by the given unit, in particular in residue characteristic prime to the level. -/
theorem exactOrderUnitAut_point [IsDomain A] {k : Type*} [Field k] [Algebra A k] [DecidableEq k]
    (a : (ZMod (n + 3))ˣ) (f : ExactOrderAlgebra W hN →ₐ[A] k) :
    (exactOrderFibrePoints W hN (f.comp ((exactOrderUnitAut W hN) a).toAlgHom)).1 =
      (a : ZMod (n + 3)).val • (exactOrderFibrePoints W hN f).1 :=
  congrArg Subtype.val (exactOrderUnitHom_point W hN a f)

#print axioms evaluateOnGenerator
#print axioms evaluateOnGenerator_map
#print axioms multipleDenominator
#print axioms multipleDenominator_isUnit
#print axioms inverseDenominator
#print axioms inverseDenominator_map
#print axioms multipleX
#print axioms multipleY
#print axioms multiple_coordinate_lift
#print axioms exactOrderUnitHom
#print axioms exactOrderUnitHom_point
#print axioms exactOrderUnitHom_one
#print axioms exactOrderUnitHom_mul
#print axioms exactOrderUnitAut
#print axioms exactOrderUnitAut_point

section Transition

open scoped TensorProduct

variable {B : Type*} [CommRing B] [Algebra A B]

private theorem exactOrderTransition_evaluate (p : A[X][Y]) :
    exactOrderTransition (B := B) W hN (evaluateOnGenerator W hN p) =
      evaluateOnGenerator (W.map (algebraMap A B))
        (show IsUnit ((n + 3 : ℕ) : B) by simpa only [map_natCast] using hN.map (algebraMap A B))
        (p.map (mapRingHom (algebraMap A B))) := by
  let V := W.map (algebraMap A B)
  let hB : IsUnit ((n + 3 : ℕ) : B) := by
    simpa only [map_natCast] using hN.map (algebraMap A B)
  let e := exactOrderBaseChange (B := B) W hN
  let f := exactOrderTransition (B := B) W hN
  have hc : f.comp (algebraMap A (ExactOrderAlgebra W hN)) =
      (algebraMap B (ExactOrderAlgebra V hB)).comp (algebraMap A B) := by
    ext a
    change e (1 ⊗ₜ[A] algebraMap A (ExactOrderAlgebra W hN) a) =
      algebraMap B (ExactOrderAlgebra V hB) (algebraMap A B a)
    rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
    exact e.commutes _
  unfold evaluateOnGenerator
  rw [← map_mapRingHom_evalEval, Polynomial.map_map, mapRingHom_comp,
    exactOrderTransition_x, exactOrderTransition_y, Polynomial.map_map, mapRingHom_comp, hc]

private theorem exactOrderTransition_denominator (a : (ZMod (n + 3))ˣ) :
    exactOrderTransition (B := B) W hN (multipleDenominator W hN a) =
      multipleDenominator (W.map (algebraMap A B))
        (show IsUnit ((n + 3 : ℕ) : B) by simpa only [map_natCast] using hN.map (algebraMap A B))
        a := by
  unfold multipleDenominator
  rw [exactOrderTransition_evaluate, ← W.map_ψ]

private theorem exactOrderTransition_inverse (a : (ZMod (n + 3))ˣ) :
    exactOrderTransition (B := B) W hN (inverseDenominator W hN a) =
      inverseDenominator (W.map (algebraMap A B))
        (show IsUnit ((n + 3 : ℕ) : B) by simpa only [map_natCast] using hN.map (algebraMap A B))
        a := by
  let V := W.map (algebraMap A B)
  let hB : IsUnit ((n + 3 : ℕ) : B) := by
    simpa only [map_natCast] using hN.map (algebraMap A B)
  let f := exactOrderTransition (B := B) W hN
  let u := (multipleDenominator_isUnit W hN a).unit
  let u' := (multipleDenominator_isUnit V hB a).unit
  have h : Units.map f.toMonoidHom u = u' := by
    apply Units.ext
    change f ↑u = ↑u'
    rw [(multipleDenominator_isUnit W hN a).unit_spec,
      (multipleDenominator_isUnit V hB a).unit_spec]
    exact exactOrderTransition_denominator W hN a
  change f.toMonoidHom (↑u⁻¹) = ↑u'⁻¹
  rw [← Units.coe_map_inv, h]

/-- The Jacobian unit formulas commute with the transition between two
coefficient domains. Equality can be checked on the two named roots.
For a nonreduced target the action is defined by scalar extension. -/
theorem exactOrderUnitHom_transition_coordinates [IsDomain A] [IsDomain B] (a : (ZMod (n + 3))ˣ) :
    let V := W.map (algebraMap A B)
    let hB : IsUnit ((n + 3 : ℕ) : B) := by
      simpa only [map_natCast] using hN.map (algebraMap A B)
    let f := exactOrderTransition (B := B) W hN
    f (exactOrderUnitHom W hN a (generatorX W hN)) =
        exactOrderUnitHom V hB a (f (generatorX W hN)) ∧
      f (exactOrderUnitHom W hN a (generatorY W hN)) =
        exactOrderUnitHom V hB a (f (generatorY W hN)) := by
  intro V hB f
  have hx := (multiple_coordinate_lift W hN a).choose_spec.1
  have hy := (multiple_coordinate_lift W hN a).choose_spec.2
  have hX := (multiple_coordinate_lift V hB a).choose_spec.1
  have hY := (multiple_coordinate_lift V hB a).choose_spec.2
  change exactOrderUnitHom W hN a (generatorX W hN) = _ at hx
  change exactOrderUnitHom W hN a (generatorY W hN) = _ at hy
  change exactOrderUnitHom V hB a (generatorX V hB) = _ at hX
  change exactOrderUnitHom V hB a (generatorY V hB) = _ at hY
  dsimp only [f]
  constructor
  · rw [hx, exactOrderTransition_x, hX, multipleX, multipleX, map_mul, map_pow,
      exactOrderTransition_evaluate, exactOrderTransition_inverse, ← W.map_φ]
  · rw [hy, exactOrderTransition_y, hY, multipleY, multipleY, map_mul, map_pow,
      exactOrderTransition_evaluate, exactOrderTransition_inverse, ← W.map_ωe]

#print axioms exactOrderTransition_evaluate
#print axioms exactOrderTransition_denominator
#print axioms exactOrderTransition_inverse
#print axioms exactOrderUnitHom_transition_coordinates

end Transition

end WeierstrassCurve.ModelLevels
