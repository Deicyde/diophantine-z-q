import ZInQKernel.Model.Descent.RankOne

/-!
# The free index of `R` is odd

Blueprint: `model/descent/odd-free-index.md`.

If `R = (1 + s, 2s) = [m] S + T` with `T ∈ C(K₀)[2]`, then `m` is odd: the Kummer map
`α_C = α_{-δ²}` is a homomorphism, `α_C(R) = ε` has sign vector `(+,-)`, while the classes of
the two-torsion points `1, -δ² ≡ -1, δ, -δ` have equal signs (`δ = 3 - s` is totally
positive), and squares do not change sign vectors.

The statement holds for every `S ∈ C(K₀)`, not only for the generator of the rank-one theorem.
-/

namespace ZInQ

open QuadraticAlgebra K0 Descent WeierstrassCurve WeierstrassCurve.Affine

theorem signVector_delta : signVector delta = (1, 1) :=
  totallyPositive_iff_signVector.mp totallyPositive_delta

/-- The two-torsion classes of `C` have equal signs. -/
theorem kummerC_two_torsion_signs {T : curveC.toAffine.Point} (hT : 2 • T = 0) :
    (sqcInvariant (kummer (-delta ^ 2) T)).2 = (1, 1) ∨
      (sqcInvariant (kummer (-delta ^ 2) T)).2 = (-1, -1) := by
  rcases (curveC_two_torsion T).mp hT with rfl | rfl | rfl | rfl
  · left; exact (show (sqcInvariant 1).2 = (1, 1) by rw [map_one]; rfl)
  · right
    rw [show kummer (-delta ^ 2) cT0 = sqc (-delta ^ 2) from kummer_some_zero _ _,
      show -delta ^ 2 = -1 * delta ^ 2 by ring, sqc_mul_sq _ delta_ne_zero, sqcInvariant_neg_one]
  · left
    rw [show kummer (-delta ^ 2) cTdelta = sqc delta from kummer_some_of_ne _ _ delta_ne_zero,
      sqcInvariant_sqc delta_ne_zero, signVector_delta]
  · right
    rw [show kummer (-delta ^ 2) cTnegdelta = sqc (-delta) from
      kummer_some_of_ne _ _ (neg_ne_zero.mpr delta_ne_zero),
      sqcInvariant_sqc (neg_ne_zero.mpr delta_ne_zero)]
    simp only [signVector, map_neg]
    have h1 := totallyPositive_delta.1
    have h2 := totallyPositive_delta.2
    rw [sign_neg (by linarith), sign_neg (by linarith)]

theorem kummerC_pointR : kummer (-delta ^ 2) pointR = sqc epsilon :=
  kummer_some_of_ne _ _ epsilon_ne_zero

/-- **The free index of `R` is odd**: if `R = [m] S + T` with `T ∈ C(K₀)[2]`, then `m` is odd. -/
theorem odd_free_index (S T : curveC.toAffine.Point) (m : ℤ) (hT : 2 • T = 0)
    (hR : pointR = m • S + T) : Odd m := by
  by_contra hm
  rw [Int.not_odd_iff_even] at hm
  obtain ⟨k, rfl⟩ := hm
  let S' : (shortCurve (-delta ^ 2)).toAffine.Point := S
  let T' : (shortCurve (-delta ^ 2)).toAffine.Point := T
  have hR' : (pointR : (shortCurve (-delta ^ 2)).toAffine.Point) = (k + k) • S' + T' := hR
  have h := congrArg (kummer (-delta ^ 2)) hR'
  have h2 : kummer (-delta ^ 2) ((k + k) • S') = 1 := by
    rw [kummer_zsmul, zpow_add, SqClass.mul_self]
  rw [kummerC_pointR, kummer_add (b := -delta ^ 2), h2, one_mul] at h
  have hs := congrArg (fun c => (sqcInvariant c).2) h
  simp only [sqcInvariant_epsilon] at hs
  rcases kummerC_two_torsion_signs hT with h' | h' <;> rw [h'] at hs <;> revert hs <;> decide

end ZInQ
