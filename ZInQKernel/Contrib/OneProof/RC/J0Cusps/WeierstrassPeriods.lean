import ZInQKernel.Contrib.CloudB3RC53.Prints.CST
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint

/-! The period group of the fixed equation, with exactly the point map used by the
interior parametrization. Transport of the proved uniformization: on the spot (c),
tex 1785–1787 and 1825–1828. -/

set_option maxHeartbeats 800000

noncomputable section

open WeierstrassCurve ZInQ.Contrib.CloudB3RC53.CST

namespace ZInQ.Manuscript.RC.J0Cusps

private def shortChange (W : WeierstrassCurve ℂ) : VariableChange ℂ :=
  ⟨1, -W.b₂ / 12, -W.a₁ / 2, -(W.a₃ + (-W.b₂ / 12) * W.a₁) / 2⟩

private theorem shortChange_eq (E : WeierstrassCurve ℚ) (Lat : PeriodPair)
    (hLat : IsLatticeOf E Lat) :
    shortChange (E.baseChange ℂ) • E.baseChange ℂ = Lat.weierstrassCurve := by
  have hc₄ : Lat.g₂ = (E.baseChange ℂ).c₄ / 12 := by
    simpa [baseChange, map_c₄] using hLat.1
  have hc₆ : Lat.g₃ = (E.baseChange ℂ).c₆ / 216 := by
    simpa [baseChange, map_c₆] using hLat.2
  ext <;>
    simp only [PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
      PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄,
      PeriodPair.weierstrassCurve_a₆, variableChange_a₁, variableChange_a₂,
      variableChange_a₃, variableChange_a₄, variableChange_a₆, shortChange,
      inv_one, Units.val_one, one_pow, one_mul, hc₄, hc₆, c₄, c₆, b₂, b₄, b₆] <;> ring

private theorem lattice_discriminant (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) : Lat.DiscriminantNeZero := by
  have h := (E.baseChange ℂ).Δ'.ne_zero
  rw [coe_Δ'] at h
  have hc : Lat.weierstrassCurve.Δ = (E.baseChange ℂ).Δ := by
    rw [← shortChange_eq E Lat hLat, variableChange_Δ]
    simp [shortChange]
  rwa [PeriodPair.DiscriminantNeZero, ← Lat.weierstrassCurve_Δ, hc]

private def shortPointEquiv (E : WeierstrassCurve ℚ) (Lat : PeriodPair)
    (hLat : IsLatticeOf E Lat) :
    Lat.weierstrassCurve.toAffine.Point ≃+ (E.baseChange ℂ).toAffine.Point :=
  (AddEquiv.cast (M := fun W : WeierstrassCurve ℂ => W.toAffine.Point)
    (shortChange_eq E Lat hLat).symm).trans
    (Affine.Point.addEquivVariableChange (E.baseChange ℂ) (shortChange (E.baseChange ℂ)))

theorem weierstrassCoordinates_nonsingular (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) {z : ℂ} (hz : z ∉ Lat.lattice) :
    (E.baseChange ℂ).toAffine.Nonsingular (Lat.weierstrassP z - (E.b₂ : ℂ) / 12)
      ((Lat.derivWeierstrassP z - (E.a₁ : ℂ) * (Lat.weierstrassP z - (E.b₂ : ℂ) / 12) -
        (E.a₃ : ℂ)) / 2) := by
  apply Affine.equation_iff_nonsingular.mp
  have h := Lat.derivWeierstrassP_sq z hz
  rw [hLat.1, hLat.2] at h
  rw [Affine.equation_iff']
  simp only [baseChange, map_a₁, map_a₂, map_a₃, map_a₄, map_a₆, eq_ratCast]
  simp only [c₄, c₆, b₂, b₄, b₆] at h ⊢
  push_cast at h ⊢
  linear_combination h / 4

private theorem shortPointEquiv_toPoint (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (z : ℂ) :
    shortPointEquiv E Lat hLat (Lat.toPoint (lattice_discriminant E Lat hLat) z) =
      weierPt E Lat z := by
  classical
  by_cases hz : z ∈ Lat.lattice
  · rw [Lat.toPoint_of_mem _ hz, map_zero, weierPt, ite_eq_left hz]
  · rw [Lat.toPoint_of_notMem _ hz, shortPointEquiv, AddEquiv.trans_apply,
      AddEquiv.cast_apply, Affine.Point.cast_some (shortChange_eq E Lat hLat).symm,
      Affine.Point.coe_addEquivVariableChange, Affine.Point.equivVariableChange_some]
    simp only [shortChange, Units.val_one, one_pow, one_mul]
    have hx : Lat.weierstrassP z + (-(E.baseChange ℂ).b₂ / 12) =
        Lat.weierstrassP z - (E.b₂ : ℂ) / 12 := by
      simp [baseChange, map_b₂, eq_ratCast, sub_eq_add_neg, neg_div]
    have hy : Lat.derivWeierstrassP z / 2 + -(E.baseChange ℂ).a₁ / 2 * Lat.weierstrassP z +
        -((E.baseChange ℂ).a₃ + (-(E.baseChange ℂ).b₂ / 12) * (E.baseChange ℂ).a₁) / 2 =
        (Lat.derivWeierstrassP z - (E.a₁ : ℂ) * (Lat.weierstrassP z - (E.b₂ : ℂ) / 12) -
          (E.a₃ : ℂ)) / 2 := by
      simp only [baseChange, map_a₁, map_a₃, map_b₂, eq_ratCast]
      ring
    rw [weierPt, ite_eq_right hz, dite_eq_left (weierstrassCoordinates_nonsingular E Lat hLat hz)]
    congr 1

/-- The chosen period quotient is the usual group of Weierstrass points of the
original equation. Its action on a representative is `weierPt` below. -/
def weierstrassPeriodEquiv (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) :
    ℂ ⧸ Lat.lattice.toAddSubgroup ≃+ (E.baseChange ℂ).toAffine.Point := by
  let hΔ := lattice_discriminant E Lat hLat
  let hU := Lat.isUniformization_toPoint hΔ
  let u : ℂ →+ Lat.weierstrassCurve.toAffine.Point :=
    ⟨⟨Lat.toPoint hΔ, Lat.toPoint_zero hΔ⟩, hU.1⟩
  have hk : Lat.lattice.toAddSubgroup = u.ker := by
    ext z
    exact ⟨Lat.toPoint_of_mem hΔ, hU.2.2 z⟩
  exact ((QuotientAddGroup.quotientAddEquivOfEq hk).trans
    (QuotientAddGroup.quotientKerEquivOfSurjective u hU.2.1)).trans
      (shortPointEquiv E Lat hLat)

/-- The group isomorphism realizes the very same chosen period coordinates,
including the lattice class (the point at infinity). -/
theorem weierstrassPeriodEquiv_mk (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (Lat : PeriodPair) (hLat : IsLatticeOf E Lat) (z : ℂ) :
    weierstrassPeriodEquiv E Lat hLat (QuotientAddGroup.mk' Lat.lattice.toAddSubgroup z) =
      weierPt E Lat z := by
  change shortPointEquiv E Lat hLat (Lat.toPoint (lattice_discriminant E Lat hLat) z) = _
  exact shortPointEquiv_toPoint E Lat hLat z


end ZInQ.Manuscript.RC.J0Cusps
