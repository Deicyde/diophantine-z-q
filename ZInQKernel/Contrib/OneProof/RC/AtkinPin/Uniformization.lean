import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange

/-! Compare the established short Weierstrass uniformization with the
coordinates of `CST.weierPt`. This comparison is on-the-spot (c). -/

set_option autoImplicit false

noncomputable section

open WeierstrassCurve ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.AtkinPin

private theorem cast_point_some {A B : WeierstrassCurve ℂ} (h : A = B)
    {x y : ℂ} (hp : A.toAffine.Nonsingular x y) :
    AddEquiv.cast (M := fun V : WeierstrassCurve ℂ => V.toAffine.Point) h (.some x y hp) =
      .some x y (h ▸ hp) := by
  subst B
  rfl

/-- The exact coordinate map used by `phiAn` is additive for the fixed
period lattice. The change of variables has scaling coordinate 1. -/
theorem weierPt_add (E : WeierstrassCurve ℚ) [E.IsElliptic] (Lat : PeriodPair)
    (hLat : IsLatticeOf E Lat) (u v : ℂ) :
    weierPt E Lat (u + v) = weierPt E Lat u + weierPt E Lat v := by
  classical
  let B := E.baseChange ℂ
  let r : ℂ := -B.b₂ / 12
  let C : VariableChange ℂ := ⟨1, r, -B.a₁ / 2, -(B.a₁ * r + B.a₃) / 2⟩
  have h4 : Lat.g₂ = B.c₄ / 12 := by
    simpa only [B, baseChange, map_c₄, eq_ratCast] using hLat.1
  have h6 : Lat.g₃ = B.c₆ / 216 := by
    simpa only [B, baseChange, map_c₆, eq_ratCast] using hLat.2
  have hC : Lat.weierstrassCurve = C • B := by
    ext <;> simp only [PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
      PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄, PeriodPair.weierstrassCurve_a₆,
      variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
      variableChange_a₆, C, r, inv_one, Units.val_one, one_pow, one_mul,
      h4, h6, c₄, c₆, b₂, b₄, b₆] <;> ring
  have hΔ : Lat.DiscriminantNeZero := by
    change Lat.g₂ ^ 3 - 27 * Lat.g₃ ^ 2 ≠ 0
    rw [← Lat.weierstrassCurve_Δ, hC]
    exact (C • B).isUnit_Δ.ne_zero
  let g : Lat.weierstrassCurve.toAffine.Point ≃+ B.toAffine.Point :=
    (AddEquiv.cast (M := fun V : WeierstrassCurve ℂ => V.toAffine.Point) hC).trans
      (Affine.Point.addEquivVariableChange B C)
  have hg (z : ℂ) : weierPt E Lat z = g (Lat.toPoint hΔ z) := by
    by_cases hz : z ∈ Lat.lattice
    · simp [weierPt, hz]
    · rw [Lat.toPoint_of_notMem hΔ hz]
      simp only [g, AddEquiv.trans_apply, cast_point_some,
        Affine.Point.coe_addEquivVariableChange, Affine.Point.equivVariableChange_some]
      have hx : (C.u : ℂ) ^ 2 * Lat.weierstrassP z + C.r =
          Lat.weierstrassP z - (E.b₂ : ℂ) / 12 := by
        simp [C, r, B, baseChange, map_b₂, eq_ratCast, sub_eq_add_neg, neg_div]
      have hy : (C.u : ℂ) ^ 3 * (Lat.derivWeierstrassP z / 2) +
          (C.u : ℂ) ^ 2 * C.s * Lat.weierstrassP z + C.t =
          (Lat.derivWeierstrassP z - (E.a₁ : ℂ) *
            (Lat.weierstrassP z - (E.b₂ : ℂ) / 12) - (E.a₃ : ℂ)) / 2 := by
        simp only [C, r, B, baseChange, map_b₂, map_a₁, map_a₃, eq_ratCast,
          Units.val_one, one_pow, one_mul]
        ring
      have hn := (Affine.variableChange_nonsingular B C _ _).mpr
        (hC ▸ (Affine.equation_iff_nonsingular_of_Δ_ne_zero
          hΔ.weierstrassCurve_Δ_ne_zero).mp (Lat.equation_weierstrassP hz))
      rw [hx, hy] at hn
      change (E.baseChange ℂ).toAffine.Nonsingular _ _ at hn
      rw [weierPt, ite_eq_right hz, dite_eq_left hn]
      congr 1 <;> first | exact hx.symm | exact hy.symm
  rw [hg, hg, hg, (Lat.isUniformization_toPoint hΔ).1, map_add]


end ZInQ.Manuscript.RC.AtkinPin
