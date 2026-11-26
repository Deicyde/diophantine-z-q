import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderGrading
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.CyclicLevel

/-! # Compatibility of generator multiplication with the short grading -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion WeierstrassCurve.Affine

universe u

variable {R : Type u} [CommRing R] [IsDomain (ShortBase R)]
  {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]

/-- The pinned multiplication-by-a-unit automorphisms over the ground
ring, obtained by restriction of scalars from the short coefficient ring. -/
noncomputable def shortLevelUnitAut (a : (ZMod (n + 2))ˣ) :
    ExactOrderAlgebra (shortFamily R) hn ≃ₐ[R] ExactOrderAlgebra (shortFamily R) hn :=
  ((levelUnitAut (shortFamily R) hn (by omega)) a).restrictScalars R

set_option backward.isDefEq.respectTransparency false in
private theorem shortLevelUnitAut_on_sigma {k : Type*} [Field k] [Algebra R k] [DecidableEq k]
    (a : (ZMod (n + 2))ˣ) (c : ShortBase R →ₐ[R] k)
    (P : Generators ((shortFamily R).map c.toRingHom).toAffine.Point (n + 2)) :
    letI : Algebra (ShortBase R) k := c.toRingHom.toAlgebra
    let e := exactOrderFibrePoints (shortFamily R) (k := k) hn
    let v := (levelUnitAut (shortFamily R) hn (by omega)) a
    ((shortExactOrderPoints hn).symm ⟨c, P⟩).comp (shortLevelUnitAut hn a).toAlgHom =
      (shortExactOrderPoints hn).symm ⟨c, e ((e.symm P).comp v.toAlgHom)⟩ := by
  intro e v
  let : Algebra (ShortBase R) k := c.toRingHom.toAlgebra
  ext x
  have h := e.symm_apply_apply ((e.symm P).comp v.toAlgHom)
  exact (DFunLike.congr_fun h x).symm

private theorem cast_generator_nsmul {k : Type*} [Field k] [DecidableEq k]
    {W W' : WeierstrassCurve k} (h : W' = W)
    (P : Generators W.toAffine.Point (n + 2)) (Q' : Generators W'.toAffine.Point (n + 2))
    (a : ℕ)
    (hq : Q'.val = a • ((h.symm ▸ P) : Generators W'.toAffine.Point (n + 2)).val) :
    ((h ▸ Q') : Generators W.toAffine.Point (n + 2)).val = a • P.val := by
  cases h
  exact hq

set_option backward.isDefEq.respectTransparency false in
/-- A pinned level automorphism precomposes the point by the corresponding
scalar multiplication on the generator. -/
theorem shortLevelUnitAut_on_generator {k : Type*} [Field k] [Algebra R k]
    [DecidableEq k] (a : (ZMod (n + 2))ˣ) (W : WeierstrassCurve k)
    [W.IsElliptic] [W.IsShortNF] (P : Generators W.toAffine.Point (n + 2)) :
    ∃ Q : Generators W.toAffine.Point (n + 2),
      Q.val = (a : ZMod (n + 2)).val • P.val ∧
      (exactOrderPointOfGenerator hn W P).comp (shortLevelUnitAut hn a).toAlgHom =
        exactOrderPointOfGenerator hn W Q := by
  let c := shortCoefficientPoint (R := R) W
  let h : (shortFamily R).map c.toRingHom = W := shortFamily_map_coefficientPoint (R := R) W
  let P' : Generators ((shortFamily R).map c.toRingHom).toAffine.Point (n + 2) := h.symm ▸ P
  letI : Algebra (ShortBase R) k := c.toRingHom.toAlgebra
  let e := exactOrderFibrePoints (shortFamily R) (k := k) hn
  let v := (levelUnitAut (shortFamily R) hn (by omega)) a
  let Q' := e ((e.symm P').comp v.toAlgHom)
  let Q : Generators W.toAffine.Point (n + 2) := h ▸ Q'
  have hq : Q'.val = (a : ZMod (n + 2)).val • P'.val := by
    have hh := levelUnitAut_point (shortFamily R) hn (by omega) a (e.symm P')
    change Q'.val = (a : ZMod (n + 2)).val • (e (e.symm P')).val at hh
    simpa only [Equiv.apply_symm_apply] using hh
  refine ⟨Q, ?_, ?_⟩
  · exact cast_generator_nsmul h P Q' _ hq
  · change ((shortExactOrderPoints hn).symm ⟨c, P'⟩).comp _ =
      (shortExactOrderPoints hn).symm ⟨c, h.symm ▸ h ▸ Q'⟩
    rw [shortLevelUnitAut_on_sigma]
    have undo {V V' : WeierstrassCurve k} (hh : V = V')
        (p : Generators V.toAffine.Point (n + 2)) :
        ((hh.symm ▸ hh ▸ p) : Generators V.toAffine.Point (n + 2)) = p := by
      cases hh
      rfl
    rw [undo h Q']

set_option maxHeartbeats 1000000 in
set_option backward.isDefEq.respectTransparency false in
/-- Reading a scaled point applies the short change of variables to
its specialized equation and generator. -/
theorem scale_inverse_shortExactOrderPoints {k : Type*} [Field k] [Algebra R k]
    [DecidableEq k] (u : kˣ) (c : ShortBase R →ₐ[R] k)
    (P : Generators ((shortFamily R).map c.toRingHom).toAffine.Point (n + 2)) :
    let W := (shortFamily R).map c.toRingHom
    let : W.IsShortNF := ⟨by simp [W, shortFamily, shortEquation],
      by simp [W, shortFamily, shortEquation], by simp [W, shortFamily, shortEquation]⟩
    let e := (Point.addEquivVariableChange W (shortScaling u)).symm
    let : (shortScaling u • W).IsShortNF := (shortScaling_coefficients W u).1
    scaleShortExactOrderPoint hn u ((shortExactOrderPoints hn).symm ⟨c, P⟩) =
      exactOrderPointOfGenerator hn (shortScaling u • W)
        ⟨e P.val, (shortScaling_order_mul W u P.val 0).1.trans P.property⟩ := by
  intro W hW e hVs
  let scaleReading :
      (Σ c : ShortBase R →ₐ[R] k,
        Generators ((shortFamily R).map c.toRingHom).toAffine.Point (n + 2)) →
      (ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) := fun data => by
    let W := (shortFamily R).map data.1.toRingHom
    let : W.IsShortNF := ⟨by simp [W, shortFamily, shortEquation],
      by simp [W, shortFamily, shortEquation], by simp [W, shortFamily, shortEquation]⟩
    let V := shortScaling u • W
    let : V.IsShortNF := (shortScaling_coefficients W u).1
    exact exactOrderPointOfGenerator hn V
      ⟨(Point.addEquivVariableChange W (shortScaling u)).symm data.2.val,
        (shortScaling_order_mul W u data.2.val 0).1.trans data.2.property⟩
  change scaleReading (shortExactOrderPoints hn ((shortExactOrderPoints hn).symm ⟨c, P⟩)) =
    scaleReading ⟨c, P⟩
  rw [Equiv.apply_symm_apply]

set_option backward.isDefEq.respectTransparency false in
/-- On geometric field points, changing the generator by a unit commutes
with scaling the short curve and the generator. -/
theorem scaleShortExactOrderPoint_comp_unit {k : Type*} [Field k] [Algebra R k] [DecidableEq k]
    (a : (ZMod (n + 2))ˣ) (u : kˣ)
    (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) :
    scaleShortExactOrderPoint hn u (f.comp (shortLevelUnitAut hn a).toAlgHom) =
      (scaleShortExactOrderPoint hn u f).comp (shortLevelUnitAut hn a).toAlgHom := by
  obtain ⟨⟨c, P⟩, rfl⟩ := (shortExactOrderPoints hn).symm.surjective f
  rw [shortLevelUnitAut_on_sigma, scale_inverse_shortExactOrderPoints,
    scale_inverse_shortExactOrderPoints]
  let W := (shortFamily R).map c.toRingHom
  let : W.IsShortNF := ⟨by simp [W, shortFamily, shortEquation],
    by simp [W, shortFamily, shortEquation], by simp [W, shortFamily, shortEquation]⟩
  let V := shortScaling u • W
  let : V.IsShortNF := (shortScaling_coefficients W u).1
  let d : W.toAffine.Point ≃+ V.toAffine.Point := (Point.addEquivVariableChange W (shortScaling u)).symm
  letI : Algebra (ShortBase R) k := c.toRingHom.toAlgebra
  let e := exactOrderFibrePoints (shortFamily R) (k := k) hn
  let v := (levelUnitAut (shortFamily R) hn (by omega)) a
  let Q := e ((e.symm P).comp v.toAlgHom)
  let Ps : Generators V.toAffine.Point (n + 2) :=
    ⟨d P.val, (shortScaling_order_mul W u P.val 0).1.trans P.property⟩
  let Qs : Generators V.toAffine.Point (n + 2) :=
    ⟨d Q.val, (shortScaling_order_mul W u Q.val 0).1.trans Q.property⟩
  change exactOrderPointOfGenerator hn V Qs =
    (exactOrderPointOfGenerator hn V Ps).comp (shortLevelUnitAut hn a).toAlgHom
  obtain ⟨Qs', hQs', h⟩ := shortLevelUnitAut_on_generator hn a V Ps
  rw [h]
  congr 1
  apply Subtype.ext
  have hq : Q.val = (a : ZMod (n + 2)).val • P.val := by
    have hh := levelUnitAut_point (shortFamily R) hn (by omega) a (e.symm P)
    change Q.val = (a : ZMod (n + 2)).val • (e (e.symm P)).val at hh
    simpa only [Equiv.apply_symm_apply] using hh
  change d Q.val = Qs'.val
  rw [hq, map_nsmul, hQs']

/-- The pinned multiplication-by-unit automorphisms preserve every
homogeneous summand of the actual cover. -/
theorem shortLevelUnitAut_mem (a : (ZMod (n + 2))ˣ) {i : ℤ}
    {x : ExactOrderAlgebra (shortFamily R) hn} (hx : x ∈ shortExactOrderGrading hn i) :
    shortLevelUnitAut hn a x ∈ shortExactOrderGrading hn i := by
  apply shortExactOrderGrading_mem_of_field_scaling
  intro k _ _ _ u f
  have h := scaleShortExactOrderPoint_homogeneous hn u (f.comp (shortLevelUnitAut hn a).toAlgHom) hx
  rwa [scaleShortExactOrderPoint_comp_unit hn a u, AlgHom.comp_apply, AlgHom.comp_apply] at h

#print axioms shortLevelUnitAut
#print axioms shortLevelUnitAut_on_sigma
#print axioms cast_generator_nsmul
#print axioms shortLevelUnitAut_on_generator
#print axioms scale_inverse_shortExactOrderPoints
#print axioms scaleShortExactOrderPoint_comp_unit
#print axioms shortLevelUnitAut_mem

end WeierstrassCurve.ModelLevels
