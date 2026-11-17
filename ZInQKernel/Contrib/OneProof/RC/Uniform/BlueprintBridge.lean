import ZInQKernel.Contrib.CloudB3RC53.Nodes

/-!
# Lane RC16: bridge from height-one regularity to the shared top layer

The shared top layer records the corrected coordinates `ũ_x ∈ Λ[1/2]` by their `t`-coefficients
(`CoordData.u x j`, the `tʲ`-coefficient of `ũ_x`), and the clearing identity
`ClearingIdentity C` asks in its second clause for bounded denominators,
`∃ e : ℕ, ∀ x j, ‖C.u x j‖ ≤ 2^e` ("`ũ_x ∈ Λ[1/2]` (bounded denominators)", tex 5491–5496, 5719–5721).

Height-one regularity (Proposition `ex:limits-uniform-lower-bound`, tex 4976–5195, assembled in
`UniformLowerBound.lean` of this lane) gives `u ∈ Λ[1/2]` for the primitive coordinates; the corrected
coordinates `ũ_x` lie in `Λ[1/2]` by the primitive comparison of `ex:arith-common-coordinate`
(4.7) (lane RC15). This file proves, as `PROVED` algebra, that membership of every `ũ_x` in
`Λ[1/2] = ℤ₂[[t]][1/2]` gives exactly that clause.

Note (interface): the node `BaseRegular C c` (`f_0 ∈ Λ`, `f_0(0) ≠ 0`, `c = v₂ f_0(0)`) is not a
consequence of the height-one regularity of `u`: it concerns `f = 2^a Δ⁴` of (5.9), and `f_0 ∈ Λ`
is proved in `ex:limits-fixed-field-clearing` (tex 5618–5631: `f` is a polynomial in the
differential entries of the remaining complex, whose augmentation is the old complex over `Λ`).
-/

namespace ZInQ.Manuscript.RC.Uniform

open ZInQ.Contrib.CloudB3RC53

/-- The coefficient form of membership in `Λ[1/2] = ℤ₂[[t]][1/2]`: the sequence `c` is the sequence of
`t`-coefficients of `a / 2^m` for some `a ∈ ℤ₂[[t]]` and `m ∈ ℕ`. Kind: definition. -/
def CoeffsInLambdaHalf (c : ℕ → ℚ_[2]) : Prop :=
  ∃ (a : PowerSeries ℤ_[2]) (m : ℕ), ∀ j : ℕ,
    c j * (2 : ℚ_[2]) ^ m = ((PowerSeries.coeff j a : ℤ_[2]) : ℚ_[2])

/-- An element of `Λ[1/2]` has bounded denominators: if `c` is the coefficient sequence of `a / 2^m`,
`a ∈ ℤ₂[[t]]`, then `‖c j‖ ≤ 2^m` for every `j`. Kind: PROVED. -/
theorem norm_le_of_coeffsInLambdaHalf {c : ℕ → ℚ_[2]} (h : CoeffsInLambdaHalf c) :
    ∃ e : ℕ, ∀ j, ‖c j‖ ≤ (2 : ℝ) ^ e := by
  obtain ⟨a, m, ha⟩ := h
  refine ⟨m, fun j => ?_⟩
  have h1 : ‖c j * (2 : ℚ_[2]) ^ m‖ ≤ 1 := by
    rw [ha j, PadicInt.norm_coe]
    exact PadicInt.norm_le_one _
  rw [norm_mul, norm_pow] at h1
  have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ := by
    have := Padic.norm_p (p := 2)
    exact_mod_cast this
  rw [h2, inv_pow] at h1
  have hpos : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
  calc ‖c j‖ = ‖c j‖ * ((2 : ℝ) ^ m)⁻¹ * (2 : ℝ) ^ m := by field_simp
    _ ≤ 1 * (2 : ℝ) ^ m := by gcongr
    _ = (2 : ℝ) ^ m := one_mul _

/-- The bounded-denominator clause of `ClearingIdentity` from height-one regularity: if every
corrected coordinate `ũ_x` (`x ∈ 𝔽₂^b`) lies in `Λ[1/2]`, with `t`-coefficients `C.u x j`, then
`∃ e, ∀ x j, ‖C.u x j‖ ≤ 2^e` (one exponent for the finitely many characters). Kind: PROVED. -/
theorem clearing_boundedDenominators_of_regular {b : ℕ} (C : CoordData b)
    (h : ∀ x, CoeffsInLambdaHalf (C.u x)) :
    ∃ e : ℕ, ∀ x j, ‖C.u x j‖ ≤ (2 : ℝ) ^ e := by
  choose e he using fun x => norm_le_of_coeffsInLambdaHalf (h x)
  refine ⟨Finset.univ.sup e, fun x j => le_trans (he x j) ?_⟩
  exact pow_le_pow_right₀ (by norm_num) (Finset.le_sup (Finset.mem_univ x))

/-- Non-vacuity: the coefficient sequence of `1/2` (that is `a = 1`, `m = 1`) lies in `Λ[1/2]`.
Kind: PROVED. -/
example : CoeffsInLambdaHalf (fun j => if j = 0 then (2 : ℚ_[2])⁻¹ else 0) := by
  refine ⟨1, 1, fun j => ?_⟩
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · simp
  · simp [PowerSeries.coeff_one, Nat.pos_iff_ne_zero.mp hj]

end ZInQ.Manuscript.RC.Uniform
