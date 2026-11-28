import ZInQKernel.Contrib.OneProof.RC.ModelGeneric7.Reduction

/-! **The order-two Vélu step commutes with reduction** (rc-model-generic7, item 3, R2).

Same setting as `Reduction` (R1′). For a point `(x₀, y₀)` of order two with integral coordinates:

* `veluQuotient2_map_subtype`, `veluQuotient2_map_residue` (curves): the vendored order-two quotient
  `W.veluQuotient2 x₀ y₀` over `A` has generic fibre `(W.map A.subtype).veluQuotient2 x₀ y₀` and
  special fibre `(W.map (residue A)).veluQuotient2 x̄₀ ȳ₀`;
* `veluPointMap2_reduceHom` (points): `reduceHom (veluPointMap2 P) = veluPointMap2 (reduceHom P)`
  for every `P` with `m • P = 0`, `m` invertible in the residue field.

Provenance: on the spot (c); the vendored formulas `velu2X`, `velu2Y`. -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

noncomputable section

namespace ZInQ.Manuscript.RC.ModelGeneric7

open WeierstrassCurve WeierstrassCurve.Affine IsLocalRing
open ZInQ.Contrib.CloudB3RC53.ModularWeil (reduceHom_injOn_torsion eq_zero_of_reduceHom_eq_zero)

variable {L : Type} [Field L] [DecidableEq L] {A : ValuationSubring L}
  [DecidableEq (ResidueField A)]

/-- The order-two quotient over `A` has generic fibre the order-two quotient over `L`. -/
theorem veluQuotient2_map_subtype (W : WeierstrassCurve A) (a b : A) :
    (W.veluQuotient2 a b).map A.subtype = (W.map A.subtype).veluQuotient2 a b := by
  ext <;> simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, veluQuotient2_a₁, veluQuotient2_a₂,
    veluQuotient2_a₃, veluQuotient2_a₄, veluQuotient2_a₆, map_sub, map_mul, map_ofNat, map_b₂,
    map_veluGx] <;> rfl

/-- The order-two quotient over `A` has special fibre the order-two quotient of the reduction. -/
theorem veluQuotient2_map_residue (W : WeierstrassCurve A) (a b : A) :
    (W.veluQuotient2 a b).map (residue A) =
      (W.map (residue A)).veluQuotient2 (residue A a) (residue A b) := by
  ext <;> simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, veluQuotient2_a₁, veluQuotient2_a₂,
    veluQuotient2_a₃, veluQuotient2_a₄, veluQuotient2_a₆, map_sub, map_mul, map_ofNat, map_b₂,
    map_veluGx] <;> rfl

variable {W : WeierstrassCurve A}

/-- **R2 on points: the order-two Vélu point map commutes with reduction on prime-to-residue
torsion.** -/
theorem veluPointMap2_reduceHom [IsAlgClosed L] [IsAlgClosed (ResidueField A)]
    (hΔ : (W.map (residue A)).Δ ≠ 0) {x₀ y₀ : L} (hx₀ : x₀ ∈ A) (hy₀ : y₀ ∈ A)
    (h2 : (2 : L) ≠ 0) (hQ : (W.map A.subtype).toAffine.Equation x₀ y₀)
    (hgy : (W.map A.subtype).veluGy x₀ y₀ = 0)
    (hΔ2 : ((W.map A.subtype).veluQuotient2 x₀ y₀).Δ ≠ 0)
    (h2' : (2 : ResidueField A) ≠ 0)
    (hQ' : (W.map (residue A)).toAffine.Equation (resL (A := A) x₀) (resL (A := A) y₀))
    (hgy' : (W.map (residue A)).veluGy (resL (A := A) x₀) (resL (A := A) y₀) = 0)
    (hΔ2' : ((W.map (residue A)).veluQuotient2 (resL (A := A) x₀) (resL (A := A) y₀)).Δ ≠ 0)
    (V : WeierstrassCurve A) (hΔV : (V.map (residue A)).Δ ≠ 0)
    (hV₁ : V.map A.subtype = (W.map A.subtype).veluQuotient2 x₀ y₀)
    (hV₂ : V.map (residue A) =
      (W.map (residue A)).veluQuotient2 (resL (A := A) x₀) (resL (A := A) y₀))
    {m : ℕ} (hm : (m : ResidueField A) ≠ 0)
    (P : (W.map A.subtype).toAffine.Point) (hP : m • P = 0) :
    reduceHom hΔV (pointCast hV₁.symm (veluPointMap2 h2 hQ hgy hΔ2 P)) =
      pointCast hV₂.symm (veluPointMap2 h2' hQ' hgy' hΔ2' (reduceHom hΔ P)) := by
  have hpt_eq : ∀ {V : WeierstrassCurve (ResidueField A)} {R R' : V.toAffine.Point}, R ≠ 0 →
      R' ≠ 0 → R.coordsOrZero = R'.coordsOrZero → R = R' := by
    intro V R R' hR hR' hc
    exact PtRel.eq ⟨⟨fun e => absurd e hR, fun e => absurd e hR'⟩, hc⟩
  rcases P with _ | ⟨x, y, h⟩
  · exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
  obtain ⟨hxA, hyA⟩ := mem_of_torsion hΔ hm h hP
  have hns : (W.map (residue A)).toAffine.Nonsingular (resL (A := A) x) (resL (A := A) y) := by
    rw [resL_of_mem hxA, resL_of_mem hyA]
    exact Affine.nonsingular_residue W hΔ (x := ⟨x, hxA⟩) (y := ⟨y, hyA⟩) h.1
  have hred : reduceHom hΔ (Point.some x y h) =
      Point.some (resL (A := A) x) (resL (A := A) y) hns :=
    (reducePoint_some_of_mem hΔ h hxA).trans (by congr 1 <;> rw [resL_of_mem])
  rw [hred]
  by_cases hx : x = x₀
  · have hx' : resL (A := A) x = resL (A := A) x₀ := by rw [hx]
    rw [veluPointMap2_some_of_eq h2 hQ hgy hΔ2 h hx, veluPointMap2_some_of_eq h2' hQ' hgy' hΔ2' hns hx']
    exact (congrArg _ (map_zero _)).trans ((map_zero _).trans (map_zero _).symm)
  -- the reduced abscissas differ
  have hQns : (W.map A.subtype).toAffine.Nonsingular x₀ y₀ :=
    (equation_iff_nonsingular_of_Δ_ne_zero (by
      rw [map_Δ]; exact fun h0 => hΔ (by rw [map_Δ, ← resL_of_mem (SetLike.coe_mem W.Δ),
        show ((W.Δ : A) : L) = 0 from h0, resL_of_mem (zero_mem A)]; exact map_zero _))).mp hQ
  have hQ2 : (2 : ℕ) • (Point.some x₀ y₀ hQns : (W.map A.subtype).toAffine.Point) = 0 := by
    rw [two_nsmul, ← eq_neg_iff_add_eq_zero, Point.neg_some]
    congr 1
    rw [negY]; simp only [veluGy] at hgy; linear_combination -hgy
  have h2m : ((2 * m : ℕ) : ResidueField A) ≠ 0 := by push_cast; exact mul_ne_zero h2' hm
  have hPt : (2 * m) • (Point.some x y h : (W.map A.subtype).toAffine.Point) = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp ((addOrderOf_dvd_of_nsmul_eq_zero hP).trans
      (dvd_mul_left m 2))
  have hQt : (2 * m) • (Point.some x₀ y₀ hQns : (W.map A.subtype).toAffine.Point) = 0 :=
    addOrderOf_dvd_iff_nsmul_eq_zero.mp ((addOrderOf_dvd_of_nsmul_eq_zero hQ2).trans
      (dvd_mul_right 2 m))
  have hsep : resL (A := A) x ≠ resL (A := A) x₀ := by
    intro hxx
    have hQns' : (W.map (residue A)).toAffine.Nonsingular (resL (A := A) x₀) (resL (A := A) y₀) := by
      rw [resL_of_mem hx₀, resL_of_mem hy₀]
      exact Affine.nonsingular_residue W hΔ (x := ⟨x₀, hx₀⟩) (y := ⟨y₀, hy₀⟩) hQns.1
    have hredQ : reduceHom hΔ (Point.some x₀ y₀ hQns) =
        Point.some (resL (A := A) x₀) (resL (A := A) y₀) hQns' :=
      (reducePoint_some_of_mem hΔ hQns hx₀).trans (by congr 1 <;> rw [resL_of_mem])
    have hQneg : -(Point.some x₀ y₀ hQns : (W.map A.subtype).toAffine.Point) =
        Point.some x₀ y₀ hQns := neg_eq_iff_add_eq_zero.mpr (by rw [← two_nsmul]; exact hQ2)
    have hnegQ : -reduceHom hΔ (Point.some x₀ y₀ hQns) = reduceHom hΔ (Point.some x₀ y₀ hQns) := by
      rw [← map_neg, hQneg]
    have hR : reduceHom hΔ (Point.some x y h) = reduceHom hΔ (Point.some x₀ y₀ hQns) := by
      rcases Y_eq_of_X_eq hns.1 hQns'.1 hxx with hy | hy
      · rw [hred, hredQ]; simp only [Point.some.injEq]; exact ⟨hxx, hy⟩
      · rw [← hnegQ, hred, hredQ, Point.neg_some]; simp only [Point.some.injEq]; exact ⟨hxx, hy⟩
    exact hx (Point.some.inj (reduceHom_injOn_torsion hΔ h2m hPt hQt hR)).1
  have hsep' : resL (A := A) x - resL (A := A) x₀ ≠ 0 := sub_ne_zero.mpr hsep
  rw [veluPointMap2_some_of_ne h2 hQ hgy hΔ2 h hx, veluPointMap2_some_of_ne h2' hQ' hgy' hΔ2' hns hsep]
  -- the formulas reduce
  have h1 := red_resL (A := A) hx₀
  have h1' := red_resL (A := A) hy₀
  have hxr := red_resL (A := A) hxA
  have hyr := red_resL (A := A) hyA
  have hX : Red A ((W.map A.subtype).velu2X x₀ y₀ x)
      ((W.map (residue A)).velu2X (resL (A := A) x₀) (resL (A := A) y₀) (resL (A := A) x)) := by
    simp only [velu2X]
    exact hxr.add ((red_veluGx W h1 h1').div (hxr.sub h1) hsep')
  have hY : Red A ((W.map A.subtype).velu2Y x₀ y₀ x y)
      ((W.map (residue A)).velu2Y (resL (A := A) x₀) (resL (A := A) y₀) (resL (A := A) x)
        (resL (A := A) y)) := by
    simp only [velu2Y]
    exact hyr.sub (((red_veluGx W h1 h1').mul ((((red_a₁ W).mul (hxr.sub h1)).add hyr).sub h1')).div
      ((hxr.sub h1).pow 2) (pow_ne_zero 2 hsep'))
  obtain ⟨hXA, hXr⟩ := hX
  obtain ⟨hYA, hYr⟩ := hY
  rcases hR : pointCast hV₁.symm (Point.some _ _
      (velu2_map_nonsingular h2 h.1 hQ hgy hx hΔ2)) with _ | ⟨X, Y, hXY⟩
  · exact absurd ((pointCast_injective hV₁.symm) (hR.trans (map_zero _).symm))
      (Point.some_ne_zero _)
  have hcR : (X, Y) = ((W.map A.subtype).velu2X x₀ y₀ x, (W.map A.subtype).velu2Y x₀ y₀ x y) := by
    rw [← (Point.coordsOrZero_some (velu2_map_nonsingular h2 h.1 hQ hgy hx hΔ2)),
      ← (ptRel_pointCast hV₁.symm _).2, hR]; rfl
  simp only [Prod.mk.injEq] at hcR
  obtain ⟨rfl, rfl⟩ := hcR
  rw [show reduceHom hΔV (Point.some _ _ hXY) = _ from reducePoint_some_of_mem hΔV hXY hXA]
  apply hpt_eq (Point.some_ne_zero _)
  · intro h0
    exact Point.some_ne_zero _ ((pointCast_injective hV₂.symm) (h0.trans (map_zero _).symm))
  · rw [(ptRel_pointCast hV₂.symm _).2]
    simp only [Point.coordsOrZero]
    rw [hXr, hYr]

end ZInQ.Manuscript.RC.ModelGeneric7

#print axioms ZInQ.Manuscript.RC.ModelGeneric7.veluQuotient2_map_subtype
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.veluQuotient2_map_residue
#print axioms ZInQ.Manuscript.RC.ModelGeneric7.veluPointMap2_reduceHom
