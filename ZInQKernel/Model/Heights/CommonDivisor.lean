import ZInQKernel.Model.Heights.DuplicationForms

/-!
# The common divisor of the duplication forms

Blueprint: `model/heights/duplication-common-divisor.md`.

For coprime `a, b ∈ ℤ[s]` and a greatest common divisor `g` of `F₂(a, b)` and `G₂(a, b)`:
`v_π(g) = 0` for every prime `π` associate to neither `s` nor `δ`, `v_s(g) ≤ 6`, `v_δ(g) ≤ 4`,
and `|N(g)| ≤ 2⁶ · 7⁴ = 392²`. We prove `g ∣ s⁶ δ⁴`, from which all four statements follow.
-/

namespace ZInQ

open QuadraticAlgebra

/-! ### Prime divisors of both forms -/

theorem prime_dvd_of_dvd_two {π : Zs} (hπ : Prime π) (h : π ∣ 2) : Associated π sqrt2Z := by
  rw [two_eq_sqrt2Z_sq] at h
  exact hπ.associated_of_dvd prime_sqrt2Z (hπ.dvd_of_dvd_pow h)

/-- A prime dividing `F₂(a, b)` and `G₂(a, b)` for coprime `a, b` divides `2` or `δ`. -/
theorem prime_dvd_F2_G2 {a b : Zs} (hab : IsCoprime a b) {π : Zs} (hπ : Prime π)
    (hF : π ∣ F2 a b) (hG : π ∣ G2 a b) : π ∣ 2 ∨ π ∣ deltaZ := by
  have hnot : ¬ (π ∣ a ∧ π ∣ b) := fun ⟨ha, hb⟩ =>
    hπ.not_isUnit (hab.isUnit_of_dvd' ha hb)
  have hS : π ∣ a ^ 2 + deltaZ ^ 2 * b ^ 2 := hπ.dvd_of_dvd_pow hF
  -- if `π ∣ a` then `π ∣ δ`
  have ha_case : π ∣ a → π ∣ deltaZ := by
    intro ha
    have h1 : π ∣ deltaZ ^ 2 * b ^ 2 := by
      have := dvd_sub hS (dvd_pow ha two_ne_zero); rwa [add_sub_cancel_left] at this
    rcases hπ.dvd_or_dvd h1 with h2 | h2
    · exact hπ.dvd_of_dvd_pow h2
    · exact absurd ⟨ha, hπ.dvd_of_dvd_pow h2⟩ hnot
  have hb_case : ¬ π ∣ b ∨ π ∣ a := by
    by_cases hb : π ∣ b
    · right
      have h1 : π ∣ a ^ 2 := by
        have := dvd_sub hS (dvd_mul_of_dvd_right (dvd_pow hb two_ne_zero) (deltaZ ^ 2))
        rwa [add_sub_cancel_right] at this
      exact hπ.dvd_of_dvd_pow h1
    · left; exact hb
  unfold G2 dupG at hG
  rcases hπ.dvd_or_dvd hG with h | h
  · rcases hπ.dvd_or_dvd h with h | h
    · rcases hπ.dvd_or_dvd h with h | h
      · left
        have : (4 : Zs) = 2 * 2 := by norm_num
        rw [this] at h
        rcases hπ.dvd_or_dvd h with h | h <;> exact h
      · exact Or.inr (ha_case h)
    · rcases hb_case with hb | ha
      · exact absurd h hb
      · exact Or.inr (ha_case ha)
  · have h2 : π ∣ 2 * a ^ 2 := by
      have := dvd_add hS h; rw [show a ^ 2 + deltaZ ^ 2 * b ^ 2 + (a ^ 2 - deltaZ ^ 2 * b ^ 2)
        = 2 * a ^ 2 by ring] at this; exact this
    rcases hπ.dvd_or_dvd h2 with h | h
    · exact Or.inl h
    · exact Or.inr (ha_case (hπ.dvd_of_dvd_pow h))

/-! ### The local bounds at `s` and `δ` -/

/-- `s⁷ ∤ F₂(a, b)` for coprime `a, b`. -/
theorem not_sqrt2Z_pow_seven_dvd_F2 {a b : Zs} (hab : IsCoprime a b) :
    ¬ sqrt2Z ^ 7 ∣ F2 a b := by
  have hnot : ¬ (sqrt2Z ∣ a ∧ sqrt2Z ∣ b) := fun ⟨ha, hb⟩ =>
    prime_sqrt2Z.not_isUnit (hab.isUnit_of_dvd' ha hb)
  have hsd := not_sqrt2Z_dvd_deltaZ
  -- if `s ∤ a² + δ² b²` then `s ∤ F₂`
  have key : ¬ sqrt2Z ∣ a ^ 2 + deltaZ ^ 2 * b ^ 2 → ¬ sqrt2Z ^ 7 ∣ F2 a b := by
    intro h h7
    exact h (prime_sqrt2Z.dvd_of_dvd_pow (dvd_trans (dvd_pow_self sqrt2Z (by norm_num)) h7))
  by_cases ha : sqrt2Z ∣ a
  · have hb : ¬ sqrt2Z ∣ b := fun hb => hnot ⟨ha, hb⟩
    apply key
    intro h
    have h1 : sqrt2Z ∣ deltaZ ^ 2 * b ^ 2 := by
      have := dvd_sub h (dvd_pow ha two_ne_zero); rwa [add_sub_cancel_left] at this
    rcases prime_sqrt2Z.dvd_or_dvd h1 with h2 | h2
    · exact hsd (prime_sqrt2Z.dvd_of_dvd_pow h2)
    · exact hb (prime_sqrt2Z.dvd_of_dvd_pow h2)
  · by_cases hb : sqrt2Z ∣ b
    · apply key
      intro h
      have h1 : sqrt2Z ∣ a ^ 2 := by
        have := dvd_sub h (dvd_mul_of_dvd_right (dvd_pow hb two_ne_zero) (deltaZ ^ 2))
        rwa [add_sub_cancel_right] at this
      exact ha (prime_sqrt2Z.dvd_of_dvd_pow h1)
    · -- neither: `v_s(a² + δ² b²) ∈ {2, 3}`
      have hv := val_s_sq_add_delta_sq ha hb
      set S := a ^ 2 + deltaZ ^ 2 * b ^ 2 with hSdef
      have hS0 : S ≠ 0 := by
        rintro h0; rw [h0, map_zero, vp_zero] at hv; omega
      have hF0 : F2 a b ≠ 0 := by
        rw [F2, dupF]; exact pow_ne_zero _ hS0
      intro h7
      have := (le_vp_iff_pow_dvd prime_sqrt2Z hF0 7).mpr h7
      rw [F2, dupF, ← hSdef, map_pow, vp_pow prime_sqrt2Z] at this
      omega

theorem residueSeven_deltaZ : residueSeven deltaZ = 0 := by
  rw [residueSeven_apply]; simp [deltaZ]

theorem deltaZ_dvd_iff (z : Zs) : deltaZ ∣ z ↔ residueSeven z = 0 := by
  rw [← associated_genDZ_deltaZ.dvd_iff_dvd_left, genDZ_dvd_iff]

theorem zmod_seven_sum_sq : ∀ x y : ZMod 7, x ^ 2 + y ^ 2 = 0 → y = 0 := by decide

/-- `δ⁵ ∤ F₂(a, b)` for coprime `a, b`. -/
theorem not_deltaZ_pow_five_dvd_F2 {a b : Zs} (hab : IsCoprime a b) :
    ¬ deltaZ ^ 5 ∣ F2 a b := by
  have hnot : ¬ (deltaZ ∣ a ∧ deltaZ ∣ b) := fun ⟨ha, hb⟩ =>
    prime_deltaZ.not_isUnit (hab.isUnit_of_dvd' ha hb)
  by_cases ha : deltaZ ∣ a
  · have hb : ¬ deltaZ ∣ b := fun hb => hnot ⟨ha, hb⟩
    obtain ⟨a', rfl⟩ := ha
    have hF : F2 (deltaZ * a') b = deltaZ ^ 4 * (a' ^ 2 + b ^ 2) ^ 2 := by
      rw [F2, dupF]; ring
    rw [hF, pow_succ]
    intro h
    have h1 : deltaZ ∣ (a' ^ 2 + b ^ 2) ^ 2 :=
      (mul_dvd_mul_iff_left (pow_ne_zero 4 prime_deltaZ.ne_zero)).mp h
    have h2 := prime_deltaZ.dvd_of_dvd_pow h1
    rw [deltaZ_dvd_iff, map_add, map_pow, map_pow] at h2
    exact hb ((deltaZ_dvd_iff b).mpr (zmod_seven_sum_sq _ _ h2))
  · intro h
    have h1 : deltaZ ∣ a ^ 2 + deltaZ ^ 2 * b ^ 2 :=
      prime_deltaZ.dvd_of_dvd_pow (dvd_trans (dvd_pow_self deltaZ (by norm_num)) h)
    have h2 : deltaZ ∣ a ^ 2 := by
      have := dvd_sub h1 (dvd_mul_of_dvd_left (dvd_pow_self deltaZ two_ne_zero) (b ^ 2))
      rwa [add_sub_cancel_right] at this
    exact ha (prime_deltaZ.dvd_of_dvd_pow h2)

/-! ### Elements whose prime factors are `s` and `δ` -/

theorem associated_of_prime_factors (x : Zs) :
    x ≠ 0 → (∀ π, Prime π → π ∣ x → Associated π sqrt2Z ∨ Associated π deltaZ) →
      ∃ i j : ℕ, Associated x (sqrt2Z ^ i * deltaZ ^ j) := by
  induction x using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => intro h; exact absurd rfl h
  | h₂ x hx => intro _ _; exact ⟨0, 0, by simpa using (associated_one_iff_isUnit.mpr hx)⟩
  | h₃ x p hx hp ih =>
    intro hpx hfac
    have hx0 : x ≠ 0 := right_ne_zero_of_mul hpx
    obtain ⟨i, j, hij⟩ := ih hx0 fun π hπ hd => hfac π hπ (dvd_mul_of_dvd_right hd p)
    rcases hfac p hp (dvd_mul_right p x) with h | h
    · exact ⟨i + 1, j, by
        have := h.mul_mul hij
        rw [show sqrt2Z ^ (i + 1) * deltaZ ^ j = sqrt2Z * (sqrt2Z ^ i * deltaZ ^ j) by ring]
        exact this⟩
    · exact ⟨i, j + 1, by
        have := h.mul_mul hij
        rw [show sqrt2Z ^ i * deltaZ ^ (j + 1) = deltaZ * (sqrt2Z ^ i * deltaZ ^ j) by ring]
        exact this⟩

/-- `g ∣ s⁶ δ⁴` for a greatest common divisor `g` of `F₂(a, b)`, `G₂(a, b)`, `a, b` coprime. -/
theorem gcd_F2_G2_dvd {a b : Zs} (hab : IsCoprime a b) {g : Zs} (hgF : g ∣ F2 a b)
    (hgG : g ∣ G2 a b) (hF0 : F2 a b ≠ 0 ∨ G2 a b ≠ 0) : g ∣ sqrt2Z ^ 6 * deltaZ ^ 4 := by
  have hg0 : g ≠ 0 := by
    rintro rfl
    rcases hF0 with h | h
    · exact h (zero_dvd_iff.mp hgF)
    · exact h (zero_dvd_iff.mp hgG)
  obtain ⟨i, j, hij⟩ := associated_of_prime_factors g hg0 fun π hπ hd => by
    rcases prime_dvd_F2_G2 hab hπ (dvd_trans hd hgF) (dvd_trans hd hgG) with h | h
    · exact Or.inl (prime_dvd_of_dvd_two hπ h)
    · exact Or.inr (hπ.associated_of_dvd prime_deltaZ h)
  have hi : i ≤ 6 := by
    by_contra hi
    apply not_sqrt2Z_pow_seven_dvd_F2 hab
    refine dvd_trans ?_ hgF
    refine dvd_trans ?_ hij.symm.dvd
    exact dvd_mul_of_dvd_left (pow_dvd_pow _ (by omega)) _
  have hj : j ≤ 4 := by
    by_contra hj
    apply not_deltaZ_pow_five_dvd_F2 hab
    refine dvd_trans ?_ hgF
    refine dvd_trans ?_ hij.symm.dvd
    exact dvd_mul_of_dvd_right (pow_dvd_pow _ (by omega)) _
  exact hij.dvd.trans (mul_dvd_mul (pow_dvd_pow _ hi) (pow_dvd_pow _ hj))

/-- `|N(s⁶ δ⁴)| = 2⁶ · 7⁴ = 392²`. -/
theorem natAbs_norm_sqrt2Z_pow_mul_deltaZ_pow :
    (QuadraticAlgebra.norm (sqrt2Z ^ 6 * deltaZ ^ 4)).natAbs = 392 ^ 2 := by
  rw [map_mul, map_pow, map_pow, norm_sqrt2Z, Zs.norm_eq]
  simp [deltaZ]

/-- Valuations of an element dividing `s⁶ δ⁴`. -/
theorem vp_le_of_dvd {π : Zs} (hπ : Prime π) {g m : Zs} (hg : g ≠ 0) (hm : m ≠ 0)
    (h : g ∣ m) : vp π (Zs.toK0 g) ≤ vp π (Zs.toK0 m) := by
  obtain ⟨c, rfl⟩ := h
  have hc : c ≠ 0 := right_ne_zero_of_mul hm
  rw [map_mul, vp_mul hπ (toK0_ne_zero hg) (toK0_ne_zero hc)]
  have := vp_nonneg hπ c
  omega

/-- **The common divisor of the duplication forms.** Let `a, b ∈ ℤ[s]` be coprime and let `g` be a
greatest common divisor of `F₂(a, b)` and `G₂(a, b)`, not both zero. Then `v_π(g) = 0` for every
prime `π` associate to neither `s` nor `δ`, `v_s(g) ≤ 6`, `v_δ(g) ≤ 4`, and
`|N(g)| ≤ 2⁶ · 7⁴ = 392²`. -/
theorem duplication_common_divisor {a b : Zs} (hab : IsCoprime a b) {g : Zs}
    (hgF : g ∣ F2 a b) (hgG : g ∣ G2 a b) (_hg : ∀ d, d ∣ F2 a b → d ∣ G2 a b → d ∣ g)
    (hF0 : F2 a b ≠ 0 ∨ G2 a b ≠ 0) :
    (∀ π, Prime π → ¬ Associated π sqrt2Z → ¬ Associated π deltaZ → vp π (Zs.toK0 g) = 0) ∧
      vp sqrt2Z (Zs.toK0 g) ≤ 6 ∧ vp deltaZ (Zs.toK0 g) ≤ 4 ∧
      (QuadraticAlgebra.norm g).natAbs ≤ 392 ^ 2 := by
  have hdvd := gcd_F2_G2_dvd hab hgF hgG hF0
  have hm0 : sqrt2Z ^ 6 * deltaZ ^ 4 ≠ 0 :=
    mul_ne_zero (pow_ne_zero 6 prime_sqrt2Z.ne_zero) (pow_ne_zero 4 prime_deltaZ.ne_zero)
  have hg0 : g ≠ 0 := by rintro rfl; exact hm0 (zero_dvd_iff.mp hdvd)
  have hval : ∀ π, Prime π → vp π (Zs.toK0 g) ≤ 6 * vp π sqrt2 + 4 * vp π delta := by
    intro π hπ
    have := vp_le_of_dvd hπ hg0 hm0 hdvd
    rwa [map_mul, map_pow, map_pow, toK0_sqrt2Z, toK0_deltaZ,
      vp_mul hπ (pow_ne_zero 6 sqrt2_ne_zero) (pow_ne_zero 4 delta_ne_zero),
      vp_pow hπ, vp_pow hπ] at this
  refine ⟨fun π hπ h1 h2 => ?_, ?_, ?_, ?_⟩
  · have hs : vp π sqrt2 = 0 := by
      rw [← toK0_sqrt2Z, vp_eq_zero_iff hπ prime_sqrt2Z.ne_zero]
      exact fun h => h1 (hπ.associated_of_dvd prime_sqrt2Z h)
    have hd : vp π delta = 0 := by
      rw [← toK0_deltaZ, vp_eq_zero_iff hπ prime_deltaZ.ne_zero]
      exact fun h => h2 (hπ.associated_of_dvd prime_deltaZ h)
    have := hval π hπ
    have := vp_nonneg hπ g
    rw [hs, hd] at *
    omega
  · have := hval sqrt2Z prime_sqrt2Z
    rw [vS_sqrt2, vS_delta] at this; omega
  · have := hval deltaZ prime_deltaZ
    have hs : vp deltaZ sqrt2 = 0 := by rw [← vp_genDZ_eq_vp_deltaZ]; exact vp_genDZ_sqrt2
    rw [← toK0_deltaZ, vp_self prime_deltaZ, hs] at this; omega
  · rw [← natAbs_norm_sqrt2Z_pow_mul_deltaZ_pow]
    obtain ⟨c, hc⟩ := hdvd
    rw [hc, map_mul, Int.natAbs_mul]
    have hc0 : c ≠ 0 := by rintro rfl; rw [mul_zero] at hc; exact hm0 hc
    exact Nat.le_mul_of_pos_right _ (Int.natAbs_pos.mpr (Zs.norm_ne_zero hc0))

end ZInQ
