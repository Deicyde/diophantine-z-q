import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Grid
import ZInQKernel.Contrib.OneProof.RC.Visibility.WeilIndex

/-! Two pieces of the local computation: annihilator support on a finite
quotient, and the normalized diagonal scalar for the extracted norm form. -/

noncomputable section

namespace ZInQ.Manuscript.RC.OldStageLaw

open scoped BigOperators

variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

theorem pairing_add_left (r t s : Grid a) : pairing (r + t) s = pairing r s * pairing t s := by
  simp only [pairing, Pi.add_apply, add_mul, neg_add, AddChar.map_add_eq_mul,
    Finset.prod_mul_distrib]


/-- Fourier support lies in the annihilator of every translation fixing the
coset weight (tex 8654–8657). -/
theorem finiteFourier_zero_of_translate (w : Grid a → ℂ) (u s : Grid a)
    (hu : ∀ r, w (r + u) = w r) (hs : pairing u s ≠ 1) : finiteFourier w s = 0 := by
  classical
  let f : Grid a → ℂ := fun r => w r * pairing r s
  have h := Equiv.sum_comp (Equiv.addRight u) f
  have h' : (∑ r, f (r + u)) = (∑ r, f r) * pairing u s := by
    simp only [f, hu, pairing_add_left, Finset.sum_mul, mul_assoc]
  change (∑ r, f (r + u)) = (∑ r, f r) at h
  rw [h'] at h
  have hz : (∑ r, f r) * (pairing u s - 1) = 0 := by rw [mul_sub, h, mul_one, sub_self]
  exact mul_eq_zero_of_right _ ((mul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hs))

/-- Fourier-conjugate translation is trivial when its phase is integral on
the entire annihilator. This is the finite form of the lower-unipotent depth
criterion (tex 8658–8663); no finite Weil index is needed for this step. -/
theorem twist_finiteFourier_eq (w : Grid a → ℂ) (H : AddSubgroup (Grid a))
    (htrans : ∀ u ∈ H, ∀ r, w (r + u) = w r) (k : ℤ)
    (hk : ∀ s, (∀ u ∈ H, pairing u s = 1) → ∃ n : ℤ, (k : ℝ) * energy s = n) :
    twist k (finiteFourier w) = finiteFourier w := by
  funext s
  by_cases hs : finiteFourier w s = 0
  · simp [twist, hs]
  have ha (u : Grid a) (hu : u ∈ H) : pairing u s = 1 := by
    by_contra h
    exact hs (finiteFourier_zero_of_translate w u s (htrans u hu) h)
  obtain ⟨n, hn⟩ := hk s ha
  have he : kernel (k : ℂ) (energy s) = 1 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hn
    push_cast at h
    rw [kernel, mul_assoc _ (k : ℂ), h, mul_comm, Complex.exp_int_mul_two_pi_mul_I]
  rw [twist, he, one_mul]

open Visibility

/-- For the prescribed unit scaling, the extracted trace-zero norm form
contributes `(u,m)` relative to the sum of three squares, including at two.
The field, index and Hilbert symbol are the parameters of the existing
`WeilIndexAxioms`; this invokes no construction of the weights. -/
theorem extracted_unit_action {k X : Type*} [Field k] {γ : kˣ → ℂˣ}
    {hs : kˣ → kˣ → ℂˣ} (hW : WeilIndexAxioms γ hs) (a b m u : kˣ)
    (scale : X → X) (φ : X → ℂ) (αu : ℂˣ) (hscale : ∀ x, φ (scale x) = (αu : ℂ) * φ x)
    (x : X) :
    (rQ γ (scaleForm m⁻¹ [a, b, a * b]) u : ℂ) * φ (scale x) =
      (αu : ℂ) * (hs u m : ℂ) * (rQ γ [1, 1, 1] u : ℂ) * φ x := by
  have hl : (scaleForm m⁻¹ [a, b, a * b]).length = 3 := rfl
  have hidx := rQ_div_rQ0 hW hl u
  rw [detForm_scaleForm, show ([a, b, a * b] : List kˣ).length = 3 from rfl,
    hs_extracted_QB hW] at hidx
  have hunit := congrArg (fun y : ℂˣ => y * rQ γ [1, 1, 1] u) hidx
  rw [mul_assoc, inv_mul_cancel, mul_one] at hunit
  rw [hscale, hunit, Units.val_mul]
  ring

/-- On the local cell with unit upper-left entry the lower, diagonal, and
upper factors have parameters `c/a`, `a`, and `b/a` (tex 8925–8931). -/
theorem diagonal_factorization {k : Type*} [Field k] {a b c d : k} (ha : a ≠ 0)
    (hdet : a * d - b * c = 1) :
    (!![1, 0; c / a, 1] : Matrix (Fin 2) (Fin 2) k) * !![a, 0; 0, a⁻¹] *
      !![1, b / a; 0, 1] = !![a, b; c, d] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, ha]
  all_goals field_simp
  all_goals linear_combination -hdet

/-- With the values in tex 8893–8898, the product over odd primes of `m`
is the Jacobi symbol `(d/m)`; the dyadic factor is `(-1/d)`. Their product
is the extracted factor `(m/d)` (tex 8903–8915). -/
theorem extracted_reciprocity (m d : ℕ) (hm : m % 4 = 3) (hd : Odd d) :
    jacobiSym (m : ℤ) d = jacobiSym (-1) d * jacobiSym (d : ℤ) m := by
  rw [jacobiSym.at_neg_one hd]
  rcases Nat.odd_mod_four_iff.mp (Nat.odd_iff.mp hd) with h | h
  · rw [ZMod.χ₄_nat_one_mod_four h, one_mul]
    exact jacobiSym.quadratic_reciprocity_one_mod_four' (Nat.odd_iff.mpr (by omega)) h
  · rw [ZMod.χ₄_nat_three_mod_four h, neg_one_mul]
    exact jacobiSym.quadratic_reciprocity_three_mod_four hm h

#print axioms pairing_add_left
#print axioms finiteFourier_zero_of_translate
#print axioms twist_finiteFourier_eq
#print axioms extracted_unit_action
#print axioms diagonal_factorization
#print axioms extracted_reciprocity

end ZInQ.Manuscript.RC.OldStageLaw
