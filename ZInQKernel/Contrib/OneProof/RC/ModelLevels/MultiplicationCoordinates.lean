import ZInQKernel.Contrib.OneProof.RC.ModelTorsion.FieldTorsion

/-! # Scalar multiplication on geometric generators -/

namespace WeierstrassCurve.ModelLevels

open WeierstrassCurve.Affine
open scoped Polynomial.Bivariate

variable {k : Type*} [Field k] [DecidableEq k] (W : WeierstrassCurve k)

/-- The denominator of the Jacobian scalar-multiplication formula is nonzero
at an affine point of exact order `N > 1` for every `a` prime to `N`. -/
theorem divisionDenominator_ne_zero {x y : k} (h : W.toAffine.Nonsingular x y)
    {N a : ℕ} (hN : 1 < N) (hP : addOrderOf (Point.some x y h : W.toAffine.Point) = N)
    (ha : a.Coprime N) : (W.ψ (a : ℤ)).evalEval x y ≠ 0 := by
  intro hz
  have hz' := (W.smul_eq_zero_iff_evalEval_ψ h (a : ℤ)).mpr hz
  rw [natCast_zsmul] at hz'
  have hd := addOrderOf_dvd_of_nsmul_eq_zero hz'
  rw [hP] at hd
  exact (Nat.ne_of_gt hN) (Nat.dvd_one.mp (by simpa [ha.gcd_eq_one] using Nat.dvd_gcd hd (dvd_refl N)))

/-- The two affine coordinates of a coprime multiple are obtained from the
vendored Jacobian division-polynomial formula by dividing by the second
and third powers of its nonzero last coordinate, respectively. -/
theorem coprimeMultiple_coordinates {x y : k} (h : W.toAffine.Nonsingular x y)
    {N a : ℕ} (hN : 1 < N) (hP : addOrderOf (Point.some x y h : W.toAffine.Point) = N)
    (ha : a.Coprime N) :
    let ψ := (W.ψ (a : ℤ)).evalEval x y
    let x' := (W.φ (a : ℤ)).evalEval x y / ψ ^ 2
    let y' := (W.ωe (a : ℤ)).evalEval x y / ψ ^ 3
    ∃ h' : W.toAffine.Nonsingular x' y',
      a • (Point.some x y h : W.toAffine.Point) = Point.some x' y' h' := by
  dsimp only
  let P : W.toAffine.Point := Point.some x y h
  let J : W.toJacobian.Point := (a : ℤ) • Jacobian.Point.fromAffine P
  let c := W.smulEval_aflt x y (a : ℤ)
  have hJ : J.point = ⟦c⟧ := W.zsmul_eq_smulEval h (a : ℤ)
  have hns : W.toJacobian.NonsingularLift ⟦c⟧ := hJ ▸ J.nonsingular
  have hz : c 2 ≠ 0 := by
    change (W.ψ (a : ℤ)).evalEval x y ≠ 0
    exact divisionDenominator_ne_zero W h hN hP ha
  have he : J = ⟨hns⟩ := Jacobian.Point.ext_iff.mpr hJ
  have hadd : Jacobian.Point.toAffineAddEquiv W J = a • P := by
      change Jacobian.Point.toAffineAddEquiv W ((a : ℤ) • Jacobian.Point.fromAffine P) = a • P
      rw [map_zsmul, ← Jacobian.Point.toAffineAddEquiv_symm_apply, AddEquiv.apply_symm_apply, natCast_zsmul]
  rw [← hadd, he, Jacobian.Point.toAffineAddEquiv_apply,
    Jacobian.Point.toAffineLift_of_Z_ne_zero hz]
  exact ⟨_, rfl⟩

#print axioms divisionDenominator_ne_zero
#print axioms coprimeMultiple_coordinates

end WeierstrassCurve.ModelLevels
