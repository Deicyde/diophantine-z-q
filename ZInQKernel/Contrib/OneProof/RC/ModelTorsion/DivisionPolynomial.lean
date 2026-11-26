import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Degree

/-!
# The polynomial of distinct torsion abscissae

Mathlib's squared division polynomial has different multiplicities at the two-torsion
and away from it. The polynomial used for abscissae includes the two-torsion factor
exactly once at even levels.
-/

namespace WeierstrassCurve.ModelTorsion

open Polynomial

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The division polynomial for the abscissae of nonidentity torsion, with the
two-torsion factor included once at even levels. -/
noncomputable def xPolynomial (W : WeierstrassCurve A) (n : ℕ) : A[X] :=
  if Even n then W.preΨ' n * W.Ψ₂Sq else W.preΨ' n

theorem map_xPolynomial (W : WeierstrassCurve A) (f : A →+* B) (n : ℕ) :
    xPolynomial (W.map f) n = (xPolynomial W n).map f := by
  by_cases h : Even n <;> simp [xPolynomial, h, W.map_preΨ', W.map_Ψ₂Sq]

private theorem even_factors_leadingCoeff (W : WeierstrassCurve A) [Nontrivial A]
    {n : ℕ} (hn : IsUnit (n : A)) (h : Even n) :
    IsUnit (4 : A) ∧
      (W.preΨ' n).leadingCoeff * W.Ψ₂Sq.leadingCoeff = 2 * (n : A) ∧ IsUnit (2 * (n : A)) := by
  obtain ⟨m, rfl⟩ := h.two_dvd
  have h₂m : IsUnit ((2 : A) * (m : A)) := by simpa using hn
  have h₂ : IsUnit (2 : A) := isUnit_of_mul_isUnit_left h₂m
  have h₄ : IsUnit (4 : A) := by simpa only [show (2 : A) * 2 = 4 by ring] using h₂.mul h₂
  refine ⟨h₄, ?_, h₂.mul hn⟩
  rw [W.leadingCoeff_preΨ' hn.ne_zero, if_pos (even_two_mul m),
    Nat.mul_div_cancel_left _ two_pos, W.leadingCoeff_Ψ₂Sq h₄.ne_zero]
  push_cast
  ring

/-- At even levels, the leading coefficient is twice the level. -/
theorem leadingCoeff_xPolynomial (W : WeierstrassCurve A) {n : ℕ} (hn : IsUnit (n : A)) :
    (xPolynomial W n).leadingCoeff = if Even n then 2 * (n : A) else n := by
  cases subsingleton_or_nontrivial A with
  | inl _ => exact Subsingleton.elim _ _
  | inr _ =>
    by_cases h : Even n
    · obtain ⟨_, heq, hu⟩ := even_factors_leadingCoeff W hn h
      simp only [xPolynomial, if_pos h]
      rw [leadingCoeff_mul' (heq.symm ▸ hu.ne_zero), heq]
    · simp [xPolynomial, h, W.leadingCoeff_preΨ' hn.ne_zero]

theorem isUnit_leadingCoeff_xPolynomial (W : WeierstrassCurve A) {n : ℕ}
    (hn : IsUnit (n : A)) : IsUnit (xPolynomial W n).leadingCoeff := by
  rw [leadingCoeff_xPolynomial W hn]
  by_cases h : Even n
  · obtain ⟨m, rfl⟩ := h.two_dvd
    have hm : IsUnit ((2 : A) * (m : A)) := by simpa using hn
    exact if_pos (even_two_mul m) ▸ (isUnit_of_mul_isUnit_left hm).mul hn
  · simpa [h] using hn

theorem natDegree_xPolynomial (W : WeierstrassCurve A) [Nontrivial A] {n : ℕ}
    (hn : IsUnit (n : A)) :
    (xPolynomial W n).natDegree = if Even n then (n ^ 2 - 4) / 2 + 3 else (n ^ 2 - 1) / 2 := by
  by_cases h : Even n
  · obtain ⟨h₄, heq, hu⟩ := even_factors_leadingCoeff W hn h
    simp only [xPolynomial, if_pos h, natDegree_mul' (heq.symm ▸ hu.ne_zero),
      W.natDegree_preΨ' hn.ne_zero, W.natDegree_Ψ₂Sq h₄.ne_zero]
  · simp [xPolynomial, h, W.natDegree_preΨ' hn.ne_zero]

#print axioms map_xPolynomial
#print axioms even_factors_leadingCoeff
#print axioms leadingCoeff_xPolynomial
#print axioms isUnit_leadingCoeff_xPolynomial
#print axioms natDegree_xPolynomial

end WeierstrassCurve.ModelTorsion
