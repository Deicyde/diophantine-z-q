import ZInQKernel.Contrib.OneProof.T21Proof.Tau

/-!
# t21-proof: the centralizer `K_2^×` of `τ(K)` at `2`

Task t21-proof. At `p = 2`, a nonzero `y ∈ ℍ[ℚ_2]` commuting with `ω_s` lies in `ℚ_2^× R_2^×`
(`Loc2OK`): `y = X + Y ω_s` and, scaling by the coordinate of larger norm, `y = c (x + y' ω_s)` with
`x² + xy' + y'²` a `2`-adic unit (the norm form of the unramified extension `ℚ_2(ω)`).
-/

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false

noncomputable section

namespace ZInQ.Contrib.T21Proof

open scoped Quaternion

theorem sg_sq (b : Fin 2) : (sg b : ℚ) ^ 2 = 1 := by
  fin_cases b <;> simp [sg]

theorem ωq_eq (s : Signs) : ωq s = ⟨1 / 2, (sg s.1 : ℚ) / 2, (sg s.2.1 : ℚ) / 2, (sg s.2.2 : ℚ) / 2⟩ := by
  obtain ⟨b1, b2, b3⟩ := s
  fin_cases b1 <;> fin_cases b2 <;> fin_cases b3 <;>
    · ext <;> simp [ωq, hurZ, hur, ωH, mapH, sg] <;> norm_num

theorem qp_ωq {p : ℕ} [Fact p.Prime] (s : Signs) :
    qp p (ωq s) = ⟨1 / 2, (sg s.1 : ℚ_[p]) / 2, (sg s.2.1 : ℚ_[p]) / 2, (sg s.2.2 : ℚ_[p]) / 2⟩ := by
  rw [ωq_eq]; ext <;> simp [qp]

theorem sgp_sq {p : ℕ} [Fact p.Prime] (b : Fin 2) : (sg b : ℚ_[p]) ^ 2 = 1 := by
  fin_cases b <;> simp [sg]

/-- `ℤ_2`: `1 + t + t²` is a unit. -/
theorem norm_one_add_add_sq (t : ℤ_[2]) : ‖(1 + t + t ^ 2 : ℤ_[2])‖ = 1 := by
  rw [← PadicInt.isUnit_iff]
  by_contra h
  have hm : (1 + t + t ^ 2 : ℤ_[2]) ∈ IsLocalRing.maximalIdeal ℤ_[2] := h
  rw [← PadicInt.ker_toZMod, RingHom.mem_ker] at hm
  have key : ∀ a : ZMod 2, 1 + a + a ^ 2 ≠ 0 := by decide
  apply key (PadicInt.toZMod t)
  rw [← hm]; simp [map_add, map_pow]

theorem norm_one_add_add_sq' {x : ℚ_[2]} (hx : ‖x‖ ≤ 1) : ‖1 + x + x ^ 2‖ = 1 := by
  have := norm_one_add_add_sq (⟨x, hx⟩ : ℤ_[2])
  rw [PadicInt.norm_def] at this
  push_cast at this
  exact this

theorem normSq_add_smul_ω {p : ℕ} [Fact p.Prime] (s : Signs) (x y : ℚ_[p]) :
    Quaternion.normSq (x • (1 : ℍ[ℚ_[p]]) + y • qp p (ωq s)) = x ^ 2 + x * y + y ^ 2 := by
  rw [qp_ωq, Quaternion.normSq_def']
  have h1 := sgp_sq (p := p) s.1
  have h2 := sgp_sq (p := p) s.2.1
  have h3 := sgp_sq (p := p) s.2.2
  simp
  linear_combination (y ^ 2 / 4) * h1 + (y ^ 2 / 4) * h2 + (y ^ 2 / 4) * h3

theorem isHur_qp_hurZ {p : ℕ} [Fact p.Prime] (n : H4 ℤ) : IsHur (Zp p) (qp p (hurZ n)) := by
  rw [qp_hurZ]
  simp only [IsHur, hurZ, hc_hur, mapH, eq_intCast]
  exact ⟨Padic.norm_int_le_one _, Padic.norm_int_le_one _, Padic.norm_int_le_one _,
    Padic.norm_int_le_one _⟩

/-- **The centralizer of `ω_s` at `2`.** -/
theorem loc2OK_of_commute {p : ℕ} [Fact p.Prime] (hp : p = 2) (s : Signs) {y : ℍ[ℚ_[p]]}
    (hy : y ≠ 0) (hc : y * qp p (ωq s) = qp p (ωq s) * y) : Loc2OK (qp p (ωq s)) y := by
  subst hp
  have e := hc
  rw [qp_ωq] at e
  have e1 := congrArg (·.imI) e
  have e2 := congrArg (·.imJ) e
  have e3 := congrArg (·.imK) e
  simp at e1 e2 e3
  have h1 := sgp_sq (p := 2) s.1
  have h2 := sgp_sq (p := 2) s.2.1
  have h3 := sgp_sq (p := 2) s.2.2
  set σ1 := (sg s.1 : ℚ_[2])
  set σ2 := (sg s.2.1 : ℚ_[2])
  set σ3 := (sg s.2.2 : ℚ_[2])
  set b := y.imI * σ1 with hb
  have hJ : y.imJ = b * σ2 := by
    rw [hb]; linear_combination (-σ1) * e3 - y.imJ * h1
  have hK : y.imK = b * σ3 := by
    rw [hb]; linear_combination σ1 * e2 - y.imK * h1
  have hdec : y = (y.re - b) • (1 : ℍ[ℚ_[2]]) + (2 * b) • qp 2 (ωq s) := by
    rw [qp_ωq]
    ext
    · simp; ring
    · simp; rw [hb]; linear_combination (-y.imI) * h1
    · simp; rw [hJ]; ring
    · simp; rw [hK]; ring
  set X := y.re - b
  set Y := 2 * b
  have hXY : X ≠ 0 ∨ Y ≠ 0 := by
    by_contra h
    push_neg at h
    apply hy
    rw [hdec, h.1, h.2, zero_smul, zero_smul, add_zero]
  have hω := isHur_qp_hurZ (p := 2) (ωH s)
  rw [← ωq] at hω
  rcases le_total ‖Y‖ ‖X‖ with hle | hle
  · -- scale by `X`
    have hX : X ≠ 0 := by
      rcases hXY with h | h
      · exact h
      · intro hX0; rw [hX0, norm_zero] at hle; exact h (norm_le_zero_iff.mp hle)
    have hYX : ‖Y / X‖ ≤ 1 := by
      rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _)
    refine ⟨X, hX, (1 : ℚ_[2]) • 1 + (Y / X) • qp 2 (ωq s), ?_, ?_, ?_, ?_⟩
    · rw [hdec, smul_add, smul_smul, smul_smul, mul_one, mul_div_cancel₀ _ hX]
    · exact (isHur_one.smul (by simp [mem_Zp])).add (hω.smul (mem_Zp.mpr hYX))
    · rw [normSq_add_smul_ω, one_pow, one_mul]
      exact norm_one_add_add_sq' hYX
    · exact ⟨1, Y / X, by simp, hYX, 0, isHur_zero, by simp⟩
  · -- scale by `Y`
    have hY : Y ≠ 0 := by
      rcases hXY with h | h
      · intro hY0; rw [hY0, norm_zero] at hle; exact h (norm_le_zero_iff.mp hle)
      · exact h
    have hXY' : ‖X / Y‖ ≤ 1 := by
      rw [norm_div]; exact div_le_one_of_le₀ hle (norm_nonneg _)
    refine ⟨Y, hY, (X / Y) • 1 + (1 : ℚ_[2]) • qp 2 (ωq s), ?_, ?_, ?_, ?_⟩
    · rw [hdec, smul_add, smul_smul, smul_smul, mul_one, mul_div_cancel₀ _ hY]
    · exact (isHur_one.smul (mem_Zp.mpr hXY')).add (hω.smul (by simp [mem_Zp]))
    · rw [normSq_add_smul_ω, one_pow, mul_one]
      have := norm_one_add_add_sq' hXY'
      rwa [show (X / Y) ^ 2 + X / Y + 1 = 1 + X / Y + (X / Y) ^ 2 by ring]
    · exact ⟨X / Y, 1, hXY', by simp, 0, isHur_zero, by simp⟩

end ZInQ.Contrib.T21Proof
