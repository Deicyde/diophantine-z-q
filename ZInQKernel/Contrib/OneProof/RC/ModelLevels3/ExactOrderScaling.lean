import ZInQKernel.Contrib.OneProof.RC.ModelLevels3.ExactOrderPresentation
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.ShortBasePoints
import ZInQKernel.Contrib.OneProof.RC.ModelLevels2.ShortScaling
import ZInQKernel.Contrib.OneProof.RC.ModelLevels.GeneratorOrbits
import Mathlib.RingTheory.AlgebraTower

/-! # Scaling the field readings of the whole short locus -/

namespace WeierstrassCurve.ModelLevels

open ModelTorsion WeierstrassCurve.Affine
open scoped TensorProduct

section Coordinates

variable {A k : Type*} [CommRing A] [Field k] [Algebra A k] [DecidableEq k]
  (W : WeierstrassCurve A) [W.IsElliptic] [W.IsShortNF]

set_option backward.isDefEq.respectTransparency false in
private theorem exactOrderFibrePoints_two (hN : IsUnit (2 : A))
    (f : ExactOrderAlgebra W hN →ₐ[A] k) :
    let V := W.map (algebraMap A k)
    ∃ h : V.toAffine.Nonsingular (f (exactOrderX W hN)) (f (exactOrderY W hN)),
      (exactOrderFibrePoints W hN f).1 = Point.some _ _ h := by
  let V := W.map (algebraMap A k)
  let : V.IsShortNF := ⟨by simp [V], by simp [V, a₂_of_isShortNF], by simp [V]⟩
  let hNk : IsUnit (2 : k) := by simpa only [map_ofNat] using hN.map (algebraMap A k)
  let e := exactOrderBaseChange (B := k) W hN
  let f' := (AlgHom.liftEquiv A k _ k f).comp e.symm.toAlgHom
  let g := f'.comp (affineToExactOrder V hNk)
  have hg (s : AffineTorsionAlgebra W 2) :
      g (affineTorsionAlgebraBaseChange W 2 (1 ⊗ₜ[A] s)) =
        f (affineToExactOrder W hN s) := by
    change f' (affineToExactOrder V hNk _) = _
    rw [← exactOrderBaseChange_affine W hN (1 : k) s]
    change (AlgHom.liftEquiv A k _ k f) (e.symm (e _)) = _
    simp
  have hP : (exactOrderFibrePoints W hN f).1 = (affineTorsionPoints V 2 hNk g).1 := rfl
  obtain ⟨q | q, hq⟩ := productFieldPoints.surjective g
  · have hz := (quadraticChartPoints V 2 q).2.1
    simp [preΨ'_two] at hz
  · have hx := hg (torsionChartX W 2)
    have hy := hg (torsionChartY W 2)
    rw [affineTorsionBaseChange_x, ← hq] at hx
    rw [affineTorsionBaseChange_y, ← hq] at hy
    change q (AdjoinRoot.root _) = f (exactOrderX W hN) at hx
    change q 0 = f (exactOrderY W hN) at hy
    rw [map_zero] at hy
    rw [hP, ← hq]
    simp only [affineTorsionPoints, affineTorsionCoordinateEquiv, Equiv.trans_apply,
      Equiv.symm_apply_apply, Equiv.sumCongr, Equiv.coe_fn_mk, Sum.map_inr,
      Equiv.ofBijective, Sum.elim_inr]
    let x := branchChartPoints V 2 q
    have hroot : V.Ψ₂Sq.eval x.1 = 0 := by
      simpa only [branchPolynomial, ite_eq_left (by decide : Even 2)] using x.2
    have hchoose := (branch_eq_zero_iff_existsUnique_ordinate V hNk x.1).mp hroot
    have hy' : hchoose.choose = 0 := by
      have hh := hchoose.choose_spec.1.2
      simpa [a₁_of_isShortNF, a₃_of_isShortNF, hNk.ne_zero] using hh
    have hns := V.toAffine.equation_iff_nonsingular.mp hchoose.choose_spec.1.1
    have hcoords : V.toAffine.Nonsingular (f (exactOrderX W hN)) (f (exactOrderY W hN)) :=
      hx ▸ (hy'.trans hy) ▸ hns
    refine ⟨hcoords, ?_⟩
    rw [Point.some.injEq]
    exact ⟨hx, hy'.trans hy⟩

/-- The two affine coordinates of every field reading of a short
exact-order cover agree with the named generators of the presentation. -/
theorem shortExactOrderFibrePoints_coordinates {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : A))
    (f : ExactOrderAlgebra W hn →ₐ[A] k) :
    let V := W.map (algebraMap A k)
    ∃ h : V.toAffine.Nonsingular (f (exactOrderX W hn)) (f (exactOrderY W hn)),
      (exactOrderFibrePoints W hn f).1 = Point.some _ _ h := by
  obtain _ | n := n
  · exact exactOrderFibrePoints_two W hn f
  · exact exactOrderFibrePoints_coordinates W hn f

end Coordinates

section Absolute

variable {R k : Type*} [CommRing R] [Field k] [Algebra R k] [DecidableEq k]
  {n : ℕ} (hn : IsUnit ((n + 2 : ℕ) : ShortBase R))
  [Algebra R (ExactOrderAlgebra (shortFamily R) hn)]
  [IsScalarTower R (ShortBase R) (ExactOrderAlgebra (shortFamily R) hn)]

/-- Points of the whole short exact-order cover are a coefficient map
and a point of exact order on its specialized elliptic curve. -/
noncomputable def shortExactOrderPoints :
    (ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) ≃
      Σ c : ShortBase R →ₐ[R] k,
        Generators ((shortFamily R).map c.toRingHom).toAffine.Point (n + 2) :=
  algHomEquivSigma.trans (Equiv.sigmaCongrRight fun c =>
    letI : Algebra (ShortBase R) k := c.toRingHom.toAlgebra
    exactOrderFibrePoints (shortFamily R) hn)

theorem shortFamily_IsShortNF :
    (shortFamily R).IsShortNF :=
  ⟨map_zero _, map_zero _, map_zero _⟩

set_option backward.isDefEq.respectTransparency false in
theorem shortExactOrderPoints_affine
    (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) :
    ∃ h : ((shortFamily R).map (shortExactOrderPoints hn f).1.toRingHom).toAffine.Nonsingular
      (f (exactOrderX (shortFamily R) hn)) (f (exactOrderY (shortFamily R) hn)),
      (shortExactOrderPoints hn f).2.1 = Point.some _ _ h := by
  let : (shortFamily R).IsShortNF := shortFamily_IsShortNF (R := R)
  let c := f.domRestrict (ShortBase R)
  let : Algebra (ShortBase R) k := c.toRingHom.toAlgebra
  exact shortExactOrderFibrePoints_coordinates (n := n) (k := k) (shortFamily R) hn
    (f.extendScalars (ShortBase R))

/-- Realize a short curve with a chosen generator as a point of the
universal presentation. -/
noncomputable def exactOrderPointOfGenerator (W : WeierstrassCurve k)
    [W.IsElliptic] [W.IsShortNF] (P : Generators W.toAffine.Point (n + 2)) :
    ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k :=
  (shortExactOrderPoints hn).symm
    ⟨shortCoefficientPoint (R := R) W, (shortFamily_map_coefficientPoint (R := R) W).symm ▸ P⟩

theorem exactOrderPointOfGenerator_read (W : WeierstrassCurve k)
    [W.IsElliptic] [W.IsShortNF] (P : Generators W.toAffine.Point (n + 2)) :
    shortExactOrderPoints hn (exactOrderPointOfGenerator hn W P) =
      ⟨shortCoefficientPoint (R := R) W, (shortFamily_map_coefficientPoint (R := R) W).symm ▸ P⟩ :=
  Equiv.apply_symm_apply _ _

private theorem cast_generator_some {V V' : WeierstrassCurve k} (e : V = V')
    {x y : k} (h : V.toAffine.Nonsingular x y) (hP : addOrderOf (Point.some x y h) = n + 2) :
    ((e ▸ (⟨Point.some x y h, hP⟩ : Generators V.toAffine.Point (n + 2)) :
      Generators V'.toAffine.Point (n + 2))).val = Point.some x y (e ▸ h) := by
  cases e
  rfl

set_option backward.isDefEq.respectTransparency false in
private theorem exactOrderPointOfGenerator_coordinates (W : WeierstrassCurve k)
    [W.IsElliptic] [W.IsShortNF] {x y : k} (h : W.toAffine.Nonsingular x y)
    (hP : addOrderOf (Point.some x y h) = n + 2) :
    let f := exactOrderPointOfGenerator hn W ⟨Point.some x y h, hP⟩
    f (exactOrderX (shortFamily R) hn) = x ∧ f (exactOrderY (shortFamily R) hn) = y := by
  let P : Generators W.toAffine.Point (n + 2) := ⟨Point.some x y h, hP⟩
  obtain ⟨h', hread⟩ := shortExactOrderPoints_affine hn (exactOrderPointOfGenerator hn W P)
  revert h' hread
  rw [exactOrderPointOfGenerator_read]
  let W' := (shortFamily R).map (shortCoefficientPoint (R := R) W).toRingHom
  let he : W' = W := shortFamily_map_coefficientPoint (R := R) W
  change ∀ h' : W'.toAffine.Nonsingular _ _, (he.symm ▸ P).val = Point.some _ _ h' → _
  intro h' hread
  have hcast : (he.symm ▸ P).val = Point.some x y (he.symm ▸ h) :=
    cast_generator_some he.symm h hP
  rw [hcast, Point.some.injEq] at hread
  exact ⟨hread.1.symm, hread.2.symm⟩

/-- Scale a point of the whole cover using the short change of variables.
The coefficient point moves with the curve. -/
noncomputable def scaleShortExactOrderPoint (u : kˣ)
    (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) :
    ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k := by
  let W := (shortFamily R).map (shortExactOrderPoints hn f).1.toRingHom
  let : W.IsShortNF := ⟨by simp [W, shortFamily, shortEquation],
    by simp [W, shortFamily, shortEquation], by simp [W, shortFamily, shortEquation]⟩
  let V := shortScaling u • W
  let : V.IsShortNF := (shortScaling_coefficients W u).1
  let P := (shortExactOrderPoints hn f).2
  exact exactOrderPointOfGenerator hn V
    ⟨(Point.addEquivVariableChange W (shortScaling u)).symm P.1,
      (shortScaling_order_mul W u P.1 0).1.trans P.2⟩

private theorem exactOrderPointOfGenerator_coefficients (W : WeierstrassCurve k)
    [W.IsElliptic] [W.IsShortNF] (P : Generators W.toAffine.Point (n + 2)) (a : ShortBase R) :
    exactOrderPointOfGenerator hn W P (algebraMap (ShortBase R) _ a) =
      shortCoefficientPoint (R := R) W a :=
  congrArg (fun z => z.1 a) (exactOrderPointOfGenerator_read hn W P)

set_option backward.isDefEq.respectTransparency false in
/-- The geometric scaling gives the prescribed five weights on the
polynomial generators, including the negative weight of the inverse. -/
theorem scaleShortExactOrderPoint_coordinates (u : kˣ)
    (f : ExactOrderAlgebra (shortFamily R) hn →ₐ[R] k) (i : Fin 5) :
    scaleShortExactOrderPoint hn u f (exactOrderShortCoordinates hn i) =
      (u : k) ^ (shortCoordinateWeight i) * f (exactOrderShortCoordinates hn i) := by
  let W := (shortFamily R).map (shortExactOrderPoints hn f).1.toRingHom
  let : W.IsShortNF := ⟨by simp [W, shortFamily, shortEquation],
    by simp [W, shortFamily, shortEquation], by simp [W, shortFamily, shortEquation]⟩
  let V := shortScaling u • W
  obtain ⟨hs, h₄, h₆, hΔ⟩ := shortScaling_coefficients W u
  let : V.IsShortNF := hs
  let g := scaleShortExactOrderPoint hn u f
  have hg (a : ShortBase R) : g (algebraMap (ShortBase R) _ a) = shortCoefficientPoint V a :=
    exactOrderPointOfGenerator_coefficients hn V _ a
  have hV := shortFamily_map_coefficientPoint (R := R) V
  have hbase (a : ShortBase R) :
      (shortExactOrderPoints hn f).1 a = f (algebraMap (ShortBase R) _ a) := rfl
  have hV₄ : shortCoefficientPoint V (shortFamily R).a₄ = V.a₄ :=
    congrArg WeierstrassCurve.a₄ hV
  have hV₆ : shortCoefficientPoint V (shortFamily R).a₆ = V.a₆ :=
    congrArg WeierstrassCurve.a₆ hV
  have hinv (c : ShortBase R →ₐ[R] k) :
      c (IsLocalization.Away.invSelf (S := ShortBase R) (shortEquation R).Δ) =
        (((shortFamily R).map c.toRingHom).Δ)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [map_Δ, shortFamily, map_Δ]
    change c (IsLocalization.Away.invSelf (shortEquation R).Δ) *
      c (algebraMap (MvPolynomial (Fin 2) R) (ShortBase R) (shortEquation R).Δ) = 1
    rw [mul_comm, ← map_mul, IsLocalization.Away.mul_invSelf, map_one]
  obtain ⟨hf, hP⟩ := shortExactOrderPoints_affine hn f
  obtain ⟨hf', hP'⟩ := shortScaling_point W u hf
  have hval := congrArg ((Point.addEquivVariableChange W (shortScaling u)).symm) hP
  rw [hP'] at hval
  have hxy : g (exactOrderX (shortFamily R) hn) = (u : k) ^ 2 * f (exactOrderX (shortFamily R) hn) ∧
      g (exactOrderY (shortFamily R) hn) = (u : k) ^ 3 * f (exactOrderY (shortFamily R) hn) := by
    let P := (shortExactOrderPoints hn f).2
    let e := (Point.addEquivVariableChange W (shortScaling u)).symm
    let horder : addOrderOf (e P.val) = n + 2 :=
      (shortScaling_order_mul W u P.val 0).1.trans P.property
    let horder' : addOrderOf (Point.some _ _ hf') = n + 2 := hval ▸ horder
    have heq : (⟨e P.val, horder⟩ : Generators V.toAffine.Point (n + 2)) =
      ⟨Point.some _ _ hf', horder'⟩ := Subtype.ext hval
    change exactOrderPointOfGenerator hn V ⟨e P.val, horder⟩ _ = _ ∧
      exactOrderPointOfGenerator hn V ⟨e P.val, horder⟩ _ = _
    rw [heq]
    exact exactOrderPointOfGenerator_coordinates hn V hf' horder'
  fin_cases i
  · change g (algebraMap (ShortBase R) _ (shortFamily R).a₄) = (u : k) ^ (4 : ℤ) * W.a₄
    rw [hg, hV₄, h₄, zpow_ofNat]
  · change g (algebraMap (ShortBase R) _ (shortFamily R).a₆) = (u : k) ^ (6 : ℤ) * W.a₆
    rw [hg, hV₆, h₆, zpow_ofNat]
  · simpa only [exactOrderShortCoordinates, shortCoordinateWeight, zpow_ofNat] using hxy.1
  · simpa only [exactOrderShortCoordinates, shortCoordinateWeight, zpow_ofNat] using hxy.2
  · change g (algebraMap (ShortBase R) _ (IsLocalization.Away.invSelf (shortEquation R).Δ)) =
      (u : k) ^ (-12 : ℤ) * f (algebraMap (ShortBase R) _
        (IsLocalization.Away.invSelf (shortEquation R).Δ))
    rw [hg, ← hbase, hinv, hinv, hV, hΔ, mul_inv_rev, zpow_neg, zpow_ofNat, mul_comm]

end Absolute

#print axioms exactOrderFibrePoints_two
#print axioms shortExactOrderFibrePoints_coordinates
#print axioms shortExactOrderPoints
#print axioms shortFamily_IsShortNF
#print axioms shortExactOrderPoints_affine
#print axioms exactOrderPointOfGenerator
#print axioms exactOrderPointOfGenerator_read
#print axioms cast_generator_some
#print axioms exactOrderPointOfGenerator_coordinates
#print axioms scaleShortExactOrderPoint
#print axioms exactOrderPointOfGenerator_coefficients
#print axioms scaleShortExactOrderPoint_coordinates

end WeierstrassCurve.ModelLevels
