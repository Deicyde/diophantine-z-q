import Mathlib

/-!
# rv-loc-leaves: two small checks behind the verdicts (a) and (d)

(a) Pan's Frobenius convention. Pan states his theorem with geometric Frobenius; the leaf
`PkgI4.PanFor` uses arithmetic Frobenius (`IsArithFrob`) with an existential eigenform `g` and
twist `ψ`. The conversion is the `2 × 2` identity `tr(M⁻¹) = tr M / det M`, applied to
`M = ψ'(Frob_geom) ρ_g(Frob_geom)`: `tr ρ(Frob_arith) = ψ'(Frob_arith) · a_q χ(q)⁻¹ q^{1−k}`,
and `a_q χ(q)⁻¹ = conj(a_q) = a_q(g^ρ)` (`g^ρ` the conjugate newform, character `χ̄`), while
`q^{1−k}` is the value of the `(1−k)`-th power of the cyclotomic character at `Frob_arith`.

(d) Baba–Granath's branch data. In Elkies' model of `X₆ → X₆/W = P¹_t`
(`y₁² = −t`, `y₂² = 3(t − 1)`, degree 4, Galois group `W ≅ (ℤ/2)²`), with `t = 1 + 27j/16`
(`PkgI1.elkies_t` / `GlueRepo.PR.tq` in Leaves.lean), the fibres over `t = 1` (`j = 0`) and
`t = 0` (`j = −16/27`) have exactly two points, against four over every other finite `t`
(`GlueRepo.PR.fibre_iff`). So the degree-4 map has ramification index `2`, not `4` or `2`-and-`6`;
`(4, 6, 2)` are the orbifold orders of `Γ*` (the ramification of `Y₃ → P¹_j`, whose level-3
group is torsion-free), as the locator audit says.
-/

namespace RvLocLeaves

/-- `tr(M⁻¹) = tr M / det M` for `2 × 2` matrices over a field. -/
theorem trace_inv_fin_two {K : Type*} [Field K] (M : Matrix (Fin 2) (Fin 2) K) :
    M⁻¹.trace = M.trace / M.det := by
  rw [Matrix.inv_def, Matrix.trace_smul, Matrix.adjugate_fin_two, Matrix.trace_fin_two,
    Matrix.trace_fin_two, Ring.inverse_eq_inv']
  simp only [Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one, smul_eq_mul]
  ring

/-- The twisted form used for Pan: if `M = c • G` with `tr G = a`, `det G = d`, `c ≠ 0`, then
`tr(M⁻¹) = c⁻¹ · a / d` (the arithmetic-Frobenius trace of `ψ' ⊗ ρ_g`). -/
theorem trace_inv_smul_fin_two {K : Type*} [Field K] (c : K) (hc : c ≠ 0)
    (G : Matrix (Fin 2) (Fin 2) K) (a d : K) (ha : G.trace = a) (hd : G.det = d) :
    (c • G)⁻¹.trace = c⁻¹ * (a / d) := by
  rw [trace_inv_fin_two, Matrix.trace_smul, Matrix.det_smul, ha, hd]
  simp only [Fintype.card_fin, smul_eq_mul]
  by_cases hd0 : d = 0
  · simp [hd0]
  · field_simp

open Complex

/-- Fibre of Elkies' `X₆ → P¹_t` over `t = 1` (`j = 0`): exactly the two points `(±i, 0)`. -/
theorem fibre_t_one (Y₁ Y₂ : ℂ) :
    (Y₁ ^ 2 = -(1 : ℂ) ∧ Y₂ ^ 2 = 3 * ((1 : ℂ) - 1)) ↔ ((Y₁ = I ∨ Y₁ = -I) ∧ Y₂ = 0) := by
  have e : -(1 : ℂ) = I ^ 2 := by rw [I_sq]
  rw [e, sq_eq_sq_iff_eq_or_eq_neg]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simpa using h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by simp [h2]⟩

/-- Fibre over `t = 0` (`j = −16/27`): exactly the two points `(0, ±i√3)`. -/
theorem fibre_t_zero (Y₁ Y₂ : ℂ) :
    (Y₁ ^ 2 = -(0 : ℂ) ∧ Y₂ ^ 2 = 3 * ((0 : ℂ) - 1)) ↔
      (Y₁ = 0 ∧ (Y₂ = I * (Real.sqrt 3 : ℂ) ∨ Y₂ = -(I * (Real.sqrt 3 : ℂ)))) := by
  have e : (3 : ℂ) * (0 - 1) = (I * (Real.sqrt 3 : ℂ)) ^ 2 := by
    rw [mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
    push_cast; ring
  rw [e, sq_eq_sq_iff_eq_or_eq_neg, neg_zero, sq_eq_zero_iff]

/-- The two points over `t = 1` are distinct, and so are the two over `t = 0`: each fibre over a
branch value has exactly two points, hence ramification index `4 / 2 = 2` in the Galois
degree-4 cover. -/
theorem fibre_points_distinct : (I ≠ -I) ∧ (I * (Real.sqrt 3 : ℂ) ≠ -(I * (Real.sqrt 3 : ℂ))) := by
  have h3 : (Real.sqrt 3 : ℂ) ≠ 0 := by
    rw [ofReal_ne_zero]; exact (Real.sqrt_pos.mpr (by norm_num)).ne'
  constructor
  · intro h
    have : (2 : ℂ) * I = 0 := by linear_combination h
    simp [I_ne_zero] at this
  · intro h
    have : (2 : ℂ) * I * (Real.sqrt 3 : ℂ) = 0 := by linear_combination h
    simp [I_ne_zero, h3] at this

end RvLocLeaves

#print axioms RvLocLeaves.trace_inv_fin_two
#print axioms RvLocLeaves.trace_inv_smul_fin_two
#print axioms RvLocLeaves.fibre_t_one
#print axioms RvLocLeaves.fibre_t_zero
#print axioms RvLocLeaves.fibre_points_distinct
