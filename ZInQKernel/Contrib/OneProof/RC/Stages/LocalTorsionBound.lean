import ZInQKernel.Contrib.OneProof.RC.Stages.Multiplier
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.TorsionReduction

/-! Local input for the uniform multiplier, tex 8277–8285. -/

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine IsDedekindDomain IsLocalRing

namespace ZInQ.Manuscript.RC.Stages

/-- A prime-to-residue-characteristic torsion point is killed by the residue
point count. Invoke the existing injectivity theorem on the original point,
after the point count kills its reduction. -/
theorem residue_count_kills {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A) {W : Affine F}
    [IsIntegral (u.valuation F).valuationSubring W]
    [(integralModel (u.valuation F).valuationSubring W).IsElliptic]
    [DecidableEq F] [DecidableEq (ResidueField (u.valuation F).valuationSubring)]
    {n : ℕ} (hn : (n : A) ∉ u.asIdeal) {P : W.Point} (hP : n • P = 0) :
    Nat.card ((integralModel (u.valuation F).valuationSubring W).map
      (residue (u.valuation F).valuationSubring)).toAffine.Point • P = 0 := by
  apply Affine.Point.eq_zero_of_reductionHom_eq_zero_of_nsmul_eq_zero u hn
  · rw [map_nsmul]
    exact card_nsmul_eq_zero'
  · rw [smul_comm n, hP, nsmul_zero]

/-- The local point count can be absorbed into the manuscript's four-count product
as soon as the residue curve has been identified at a degree between 1 and 4. -/
theorem reduction_product_kills {A F : Type*} [CommRing A] [IsDedekindDomain A] [Field F]
    [Algebra A F] [IsFractionRing A F] (u : HeightOneSpectrum A) {W : Affine F}
    [IsIntegral (u.valuation F).valuationSubring W]
    [(integralModel (u.valuation F).valuationSubring W).IsElliptic]
    [DecidableEq F] [DecidableEq (ResidueField (u.valuation F).valuationSubring)]
    (count : ℕ → ℕ) {f : ℕ} (h₁ : 1 ≤ f) (h₄ : f ≤ 4)
    (hcount : count f = Nat.card ((integralModel (u.valuation F).valuationSubring W).map
      (residue (u.valuation F).valuationSubring)).toAffine.Point)
    {n : ℕ} (hn : (n : A) ∉ u.asIdeal) {P : W.Point} (hP : n • P = 0) :
    reductionBound count • P = 0 := by
  obtain ⟨k, hk⟩ := count_dvd_reductionBound count h₁ h₄
  rw [hk, mul_nsmul, hcount, residue_count_kills u hn hP, nsmul_zero]

#print axioms residue_count_kills
#print axioms reduction_product_kills

end ZInQ.Manuscript.RC.Stages
