import ZInQKernel.Contrib.OneProof.RC.ModelTarget.ChartRing
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Presentations of the charts of the projective Weierstrass cubic as quotients
of a polynomial ring in one variable over a polynomial ring in one variable. Each
presentation is monic in the outer variable, so its localization at the
derivative is standard étale over the inner polynomial ring. The three
presentations are: the `Z`-chart monic in `y` (the affine coordinate ring), the
`Z`-chart monic in `x`, and the `Y`-chart after the shear `x = x' + c z`, which is
monic in `z` once `c³ + a₂c² + a₄c + a₆` is a unit. On the spot (c). -/

noncomputable section

open WeierstrassCurve HomogeneousLocalization
open Polynomial (C)

set_option autoImplicit false

namespace ZInQ.Manuscript.RC.ModelTarget

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

section Generic

variable (i : Fin 3) (q : Polynomial (Polynomial R))

theorem adjoinRoot_algebraMap (a : R) :
    algebraMap R (AdjoinRoot q) a = AdjoinRoot.of q (C a) := rfl

/-- The map from a presentation to the chart, sending the inner variable to `u` and the
root to `v`. -/
def presLift (u v : Chart W i)
    (h : q.eval₂ (Polynomial.eval₂RingHom (chartConst W i) u) v = 0) :
    AdjoinRoot q →+* Chart W i :=
  AdjoinRoot.lift (Polynomial.eval₂RingHom (chartConst W i) u) v h

theorem presLift_algebraMap (u v : Chart W i) (h) (a : R) :
    presLift W i q u v h (algebraMap R _ a) = chartConst W i a := by
  rw [adjoinRoot_algebraMap, presLift, AdjoinRoot.lift_of]
  simp

theorem presLift_of_X (u v : Chart W i) (h) :
    presLift W i q u v h (AdjoinRoot.of q Polynomial.X) = u := by
  rw [presLift, AdjoinRoot.lift_of]
  simp

theorem presLift_root (u v : Chart W i) (h) : presLift W i q u v h (AdjoinRoot.root q) = v := by
  rw [presLift, AdjoinRoot.lift_root]

/-- The dehomogenization to a presentation, given by a solution vector. -/
def presDehom (P : Fin 3 → AdjoinRoot q)
    (hP : (W.toProjective.map (algebraMap R (AdjoinRoot q))).Equation P) :
    W.toProjective.CoordinateRing →+* AdjoinRoot q :=
  W.toProjective.evalHom (algebraMap R (AdjoinRoot q)) hP

theorem presDehom_coord (P : Fin 3 → AdjoinRoot q) (hP) (j : Fin 3) :
    presDehom W q P hP (W.toProjective.coord j) = P j :=
  congrFun (W.toProjective.evalHom_comp_coord _ hP) j

theorem presDehom_algebraMap (P : Fin 3 → AdjoinRoot q) (hP) (a : R) :
    presDehom W q P hP (algebraMap R _ a) = algebraMap R _ a :=
  RingHom.congr_fun (W.toProjective.evalHom_comp_algebraMap _ hP) a

/-- A presentation identifies with the chart when the two maps match on the
coordinates and the inner variable and root are recovered. -/
def presEquiv (P : Fin 3 → AdjoinRoot q)
    (hP : (W.toProjective.map (algebraMap R (AdjoinRoot q))).Equation P) (hPi : P i = 1)
    (u v : Chart W i) (h : q.eval₂ (Polynomial.eval₂RingHom (chartConst W i) u) v = 0)
    (hψ : ∀ j, presLift W i q u v h (P j) = ratio W i j)
    (hu : chartLift i (presDehom W q P hP) ((presDehom_coord W q P hP i).trans hPi) u =
      AdjoinRoot.of q Polynomial.X)
    (hv : chartLift i (presDehom W q P hP) ((presDehom_coord W q P hP i).trans hPi) v =
      AdjoinRoot.root q) :
    AdjoinRoot q ≃+* Chart W i :=
  chartEquiv i (presDehom W q P hP) ((presDehom_coord W q P hP i).trans hPi)
    (presLift W i q u v h)
    (fun a => by rw [presDehom_algebraMap, presLift_algebraMap])
    (fun j => by rw [presDehom_coord, hψ])
    (by
      apply AdjoinRoot.ringHom_ext
      · apply Polynomial.ringHom_ext
        · intro a
          simp only [RingHom.comp_apply, RingHom.id_apply]
          rw [← adjoinRoot_algebraMap, presLift_algebraMap, chartLift_const,
            presDehom_algebraMap]
        · simp only [RingHom.comp_apply, RingHom.id_apply]
          rw [presLift_of_X, hu]
      · simp only [RingHom.comp_apply, RingHom.id_apply]
        rw [presLift_root, hv])

theorem presEquiv_apply (P hP hPi u v h hψ hu hv) (b : AdjoinRoot q) :
    presEquiv W i q P hP hPi u v h hψ hu hv b = presLift W i q u v h b := rfl

theorem presEquiv_algebraMap (P hP hPi u v h hψ hu hv) (a : R) :
    presEquiv W i q P hP hPi u v h hψ hu hv (algebraMap R _ a) = chartConst W i a :=
  presLift_algebraMap W i q u v h a

end Generic

section ZChart

/-- The affine relation in the affine coordinate ring. -/
theorem affine_relation :
    (AdjoinRoot.root W.toAffine.polynomial) ^ 2 +
        algebraMap R _ W.a₁ * AdjoinRoot.of _ Polynomial.X * AdjoinRoot.root _ +
        algebraMap R _ W.a₃ * AdjoinRoot.root W.toAffine.polynomial -
      (AdjoinRoot.of _ Polynomial.X ^ 3 +
        algebraMap R _ W.a₂ * AdjoinRoot.of W.toAffine.polynomial Polynomial.X ^ 2 +
        algebraMap R _ W.a₄ * AdjoinRoot.of _ Polynomial.X + algebraMap R _ W.a₆) = 0 := by
  have key : ∀ p : Polynomial (Polynomial R), p = W.toAffine.polynomial →
      AdjoinRoot.mk W.toAffine.polynomial p = 0 := fun p hp => hp ▸ AdjoinRoot.mk_self
  have h := key (Polynomial.X ^ 2 + C (C W.a₁ * Polynomial.X + C W.a₃) * Polynomial.X -
    C (Polynomial.X ^ 3 + C W.a₂ * Polynomial.X ^ 2 + C W.a₄ * Polynomial.X + C W.a₆)) rfl
  simp only [map_sub, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  simp only [adjoinRoot_algebraMap]
  linear_combination h

/-- The point `(x : y : 1)` of the affine coordinate ring. -/
def zyPoint : Fin 3 → W.toAffine.CoordinateRing :=
  ![AdjoinRoot.of _ Polynomial.X, AdjoinRoot.root _, 1]

theorem zyPoint_equation :
    (W.toProjective.map (algebraMap R W.toAffine.CoordinateRing)).Equation (zyPoint W) := by
  rw [Projective.equation_iff]
  simp only [zyPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Projective.map, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    one_pow, mul_one]
  linear_combination affine_relation W

theorem zy_eval :
    W.toAffine.polynomial.eval₂ (Polynomial.eval₂RingHom (chartConst W 2) (ratio W 2 0))
      (ratio W 2 1) = 0 := by
  have h := chart_equation W 2
  simp only [Projective.polynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
    ratio_self] at h
  simp only [Affine.polynomial, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom]
  linear_combination h

/-- The `Z`-chart is the affine coordinate ring. -/
def zyEquiv : W.toAffine.CoordinateRing ≃+* Chart W 2 :=
  presEquiv W 2 W.toAffine.polynomial (zyPoint W) (zyPoint_equation W) rfl
    (ratio W 2 0) (ratio W 2 1) (zy_eval W)
    (fun j => by
      fin_cases j
      · exact presLift_of_X W 2 _ _ _ _
      · exact presLift_root W 2 _ _ _ _
      · exact (map_one _).trans (ratio_self W 2).symm)
    (by rw [chartLift_ratio, presDehom_coord]; rfl)
    (by rw [chartLift_ratio, presDehom_coord]; rfl)

end ZChart


section ZChartX

/-- The `Z`-chart presented as monic in `x` over the polynomial ring in `y`: the outer
variable is `x`, the inner variable is `y`. -/
def zxPoly : Polynomial (Polynomial R) :=
  Polynomial.X ^ 3 + C (C W.a₂) * Polynomial.X ^ 2 + C (C W.a₄ - C W.a₁ * Polynomial.X) * Polynomial.X +
    C (C W.a₆ - Polynomial.X ^ 2 - C W.a₃ * Polynomial.X)

theorem zx_relation :
    (AdjoinRoot.root (zxPoly W)) ^ 3 + algebraMap R _ W.a₂ * AdjoinRoot.root (zxPoly W) ^ 2 +
        (algebraMap R _ W.a₄ - algebraMap R _ W.a₁ * AdjoinRoot.of (zxPoly W) Polynomial.X) *
          AdjoinRoot.root (zxPoly W) +
        (algebraMap R _ W.a₆ - AdjoinRoot.of (zxPoly W) Polynomial.X ^ 2 -
          algebraMap R _ W.a₃ * AdjoinRoot.of (zxPoly W) Polynomial.X) = 0 := by
  have h := AdjoinRoot.mk_self (f := zxPoly W)
  conv_lhs at h => arg 2; rw [zxPoly]
  simp only [map_sub, map_add, map_mul, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at h
  simp only [adjoinRoot_algebraMap]
  linear_combination h

/-- The point `(x : y : 1)` with `x` the root. -/
def zxPoint : Fin 3 → AdjoinRoot (zxPoly W) :=
  ![AdjoinRoot.root _, AdjoinRoot.of _ Polynomial.X, 1]

theorem zxPoint_equation :
    (W.toProjective.map (algebraMap R (AdjoinRoot (zxPoly W)))).Equation (zxPoint W) := by
  rw [Projective.equation_iff]
  simp only [zxPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Projective.map, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    one_pow, mul_one]
  linear_combination -zx_relation W

theorem zx_eval :
    (zxPoly W).eval₂ (Polynomial.eval₂RingHom (chartConst W 2) (ratio W 2 1)) (ratio W 2 0) = 0 := by
  have h := chart_equation W 2
  simp only [Projective.polynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
    ratio_self] at h
  simp only [zxPoly, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.coe_eval₂RingHom]
  linear_combination -h

/-- The `Z`-chart presented as monic in `x`. -/
def zxEquiv : AdjoinRoot (zxPoly W) ≃+* Chart W 2 :=
  presEquiv W 2 (zxPoly W) (zxPoint W) (zxPoint_equation W) rfl
    (ratio W 2 1) (ratio W 2 0) (zx_eval W)
    (fun j => by
      fin_cases j
      · exact presLift_root W 2 _ _ _ _
      · exact presLift_of_X W 2 _ _ _ _
      · exact (map_one _).trans (ratio_self W 2).symm)
    (by rw [chartLift_ratio, presDehom_coord]; rfl)
    (by rw [chartLift_ratio, presDehom_coord]; rfl)

end ZChartX

section YChart

variable (c w : R)

/-- The `Y`-chart after the shear `x = x' + c z`, divided by the `z³`-coefficient
`-(c³ + a₂c² + a₄c + a₆)`, whose inverse is `w`. The outer variable is `z`, the inner
variable is `x'`. -/
def yPoly : Polynomial (Polynomial R) :=
  Polynomial.X ^ 3 +
    C (C w * (C (W.a₁ * c + W.a₃) - C (3 * c ^ 2 + 2 * W.a₂ * c + W.a₄) * Polynomial.X)) *
      Polynomial.X ^ 2 +
    C (C w * (1 + C W.a₁ * Polynomial.X - C (3 * c + W.a₂) * Polynomial.X ^ 2)) * Polynomial.X +
    C (C w * -Polynomial.X ^ 3)

theorem y_relation :
    (AdjoinRoot.root (yPoly W c w)) ^ 3 +
        algebraMap R _ w * (algebraMap R _ (W.a₁ * c + W.a₃) -
          algebraMap R _ (3 * c ^ 2 + 2 * W.a₂ * c + W.a₄) *
            AdjoinRoot.of (yPoly W c w) Polynomial.X) * AdjoinRoot.root (yPoly W c w) ^ 2 +
        algebraMap R _ w * (1 + algebraMap R _ W.a₁ * AdjoinRoot.of (yPoly W c w) Polynomial.X -
          algebraMap R _ (3 * c + W.a₂) * AdjoinRoot.of (yPoly W c w) Polynomial.X ^ 2) *
            AdjoinRoot.root (yPoly W c w) +
        algebraMap R _ w * -AdjoinRoot.of (yPoly W c w) Polynomial.X ^ 3 = 0 := by
  have h := AdjoinRoot.mk_self (f := yPoly W c w)
  conv_lhs at h => arg 2; rw [yPoly]
  simp only [map_sub, map_add, map_mul, map_pow, map_neg, map_one, AdjoinRoot.mk_X,
    AdjoinRoot.mk_C] at h
  simp only [adjoinRoot_algebraMap, map_add, map_mul, map_pow]
  linear_combination h

/-- The point `(x' + c z : 1 : z)`. -/
def yPoint : Fin 3 → AdjoinRoot (yPoly W c w) :=
  ![AdjoinRoot.of _ Polynomial.X + algebraMap R _ c * AdjoinRoot.root _, 1, AdjoinRoot.root _]

variable {c w}

theorem yPoint_equation (hw : w * (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = -1) :
    (W.toProjective.map (algebraMap R (AdjoinRoot (yPoly W c w)))).Equation (yPoint W c w) := by
  rw [Projective.equation_iff]
  simp only [yPoint, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Projective.map, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆,
    one_pow, mul_one, one_mul]
  have hw' := congrArg (algebraMap R (AdjoinRoot (yPoly W c w))) hw
  simp only [map_mul, map_add, map_pow, map_neg, map_one] at hw'
  have hr := y_relation W c w
  simp only [map_mul, map_add, map_pow, map_ofNat] at hr
  set x := AdjoinRoot.of (yPoly W c w) Polynomial.X
  set z := AdjoinRoot.root (yPoly W c w)
  set e := algebraMap R (AdjoinRoot (yPoly W c w)) c ^ 3 +
    algebraMap R _ W.a₂ * algebraMap R _ c ^ 2 + algebraMap R _ W.a₄ * algebraMap R _ c +
      algebraMap R _ W.a₆
  linear_combination (-e) * hr + ((algebraMap R _ W.a₁ * algebraMap R _ c + algebraMap R _ W.a₃ -
      (3 * algebraMap R _ c ^ 2 + 2 * algebraMap R _ W.a₂ * algebraMap R _ c +
        algebraMap R _ W.a₄) * x) * z ^ 2 +
      (1 + algebraMap R _ W.a₁ * x - (3 * algebraMap R _ c + algebraMap R _ W.a₂) * x ^ 2) * z -
        x ^ 3) * hw'

theorem y_eval (hw : w * (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = -1) :
    (yPoly W c w).eval₂ (Polynomial.eval₂RingHom (chartConst W 1)
      (ratio W 1 0 - chartConst W 1 c * ratio W 1 2)) (ratio W 1 2) = 0 := by
  have h := chart_equation W 1
  simp only [Projective.polynomial, MvPolynomial.eval₂_add, MvPolynomial.eval₂_sub,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_pow, MvPolynomial.eval₂_X, MvPolynomial.eval₂_C,
    ratio_self] at h
  have hw' := congrArg (chartConst W 1) hw
  simp only [map_mul, map_add, map_pow, map_neg, map_one] at hw'
  simp only [yPoly, Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, Polynomial.eval₂_neg,
    Polynomial.eval₂_one, Polynomial.coe_eval₂RingHom]
  simp only [map_add, map_mul, map_pow, map_ofNat]
  set k := chartConst W 1
  set u := ratio W 1 0
  set v := ratio W 1 2
  linear_combination k w * h + v ^ 3 * hw'

/-- The `Y`-chart presented as monic in `z` after the shear. -/
def yEquiv (hw : w * (c ^ 3 + W.a₂ * c ^ 2 + W.a₄ * c + W.a₆) = -1) :
    AdjoinRoot (yPoly W c w) ≃+* Chart W 1 :=
  presEquiv W 1 (yPoly W c w) (yPoint W c w) (yPoint_equation W hw) rfl
    (ratio W 1 0 - chartConst W 1 c * ratio W 1 2) (ratio W 1 2) (y_eval W hw)
    (fun j => by
      fin_cases j
      · change presLift W 1 _ _ _ _ (AdjoinRoot.of _ Polynomial.X +
          algebraMap R _ c * AdjoinRoot.root _) = ratio W 1 0
        rw [map_add, map_mul, presLift_of_X, presLift_algebraMap, presLift_root]
        ring
      · exact (map_one _).trans (ratio_self W 1).symm
      · exact presLift_root W 1 _ _ _ _)
    (by
      rw [map_sub, map_mul, chartLift_ratio, chartLift_ratio, chartLift_const, presDehom_coord,
        presDehom_coord, presDehom_algebraMap]
      simp [yPoint])
    (by rw [chartLift_ratio, presDehom_coord]; rfl)

end YChart

#print axioms presEquiv
#print axioms zyEquiv
#print axioms zxEquiv
#print axioms yEquiv

end ZInQ.Manuscript.RC.ModelTarget
