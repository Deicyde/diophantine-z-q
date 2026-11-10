import ZInQKernel.RouteK.Selmer.PadicSquare
import ZInQKernel.RouteK.Selmer.CharSum

/-!
# Odd primes not dividing `d`

File 7 of `docs/research/nt-prop0.md` §4.1, the lemmas of §2.3 for an odd prime `p ∤ d`:

* Lemma G1, `loc_padic_good_even`: if `Loc ℚ_[p] d a b` then `v_p(a)` and `v_p(b)` are even (no
  class is ramified at `p`). The proof compares `‖x‖` with `‖d‖ = 1` and shows that `a` and `b`
  lie in the square classes of units; with `‖x‖ = 1`, at most one of `x ∓ d` is a non-unit since
  their difference `2d` is a unit.
* Lemma G2, `loc_padic_good_of_units`: if `p ∤ ab` then `Loc ℚ_[p] d a b`. Over `𝔽_p` this is
  `exists_xi` (`CharSum.lean`); the residue `ξ` is lifted to an integer `x`, taken to be exactly
  `0`, `d` or `-d` when `ξ ∈ {0, ±d̄}`, and the three quotients are squares by SQ(a).
* `loc_padic_good_iff`: for squarefree `a`, `b`, `Loc ℚ_[p] d a b ↔ p ∤ a ∧ p ∤ b`.
-/

namespace ZInQ.RouteK.Selmer

variable {p : ℕ} [hp : Fact p.Prime]

/-- A `p`-adic number in the square class of a unit has even valuation. -/
theorem even_valuation_of_sqEq_unit {A u : ℚ_[p]} (hu : ‖u‖ = 1) (h : SqEq A u) :
    Even A.valuation := by
  obtain ⟨s, hs, rfl⟩ := h
  have hu0 : u ≠ 0 := by intro h0; rw [h0, norm_zero] at hu; exact zero_ne_one hu
  have hv : u.valuation = 0 := by
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
    have e := Padic.norm_eq_zpow_neg_valuation hu0
    rw [hu] at e
    have := zpow_right_injective₀ (by linarith) hp1.ne' (e.symm.trans (zpow_zero _).symm)
    simpa using this
  rw [Padic.valuation_mul hu0 (pow_ne_zero _ hs), Padic.valuation_pow, hv]
  exact ⟨s.valuation, by push_cast; ring⟩

/-- **Lemma G1** (nt-prop0 §2.3): at an odd prime `p ∤ d`, a locally soluble pair `(a, b)` has
`v_p(a)` and `v_p(b)` even. -/
theorem loc_padic_good_even (hp2 : p ≠ 2) {d : ℕ} (hpd : ¬p ∣ d) {a b : ℤ} (ha : a ≠ 0)
    (hb : b ≠ 0) (h : Loc ℚ_[p] d a b) : Even (padicValInt p a) ∧ Even (padicValInt p b) := by
  set D : ℚ_[p] := (d : ℚ_[p])
  set A : ℚ_[p] := (a : ℚ_[p])
  set B : ℚ_[p] := (b : ℚ_[p])
  have hD : ‖D‖ = 1 := by
    have := padic_norm_intCast_eq_one (p := p) (c := d) (fun h' => hpd (by exact_mod_cast h'))
    simpa [D] using this
  have hD0 : D ≠ 0 := by intro h0; rw [h0, norm_zero] at hD; exact zero_ne_one hD
  have h2 : (2 : ℚ_[p]) ≠ 0 := two_ne_zero
  have hA0 : A ≠ 0 := Int.cast_ne_zero.mpr ha
  have hB0 : B ≠ 0 := Int.cast_ne_zero.mpr hb
  have hn2 := padic_norm_two (p := p) hp2
  have hm1 : ‖(-1 : ℚ_[p])‖ = 1 := by rw [norm_neg, norm_one]
  -- it suffices to put `a` and `b` in the square classes of units
  suffices key : ∃ u w : ℚ_[p], ‖u‖ = 1 ∧ ‖w‖ = 1 ∧ SqEq A u ∧ SqEq B w by
    obtain ⟨u, w, hu, hw, hAu, hBw⟩ := key
    have e₁ := even_valuation_of_sqEq_unit hu hAu
    have e₂ := even_valuation_of_sqEq_unit hw hBw
    rw [Padic.valuation_intCast] at e₁ e₂
    exact ⟨Int.even_coe_nat _ |>.mp e₁, Int.even_coe_nat _ |>.mp e₂⟩
  rcases h with ⟨hsa, hsb⟩ | ⟨x, h₁, h₂, h₃⟩
  · exact ⟨1, 1, norm_one, norm_one, (sqEq_iff_isSquare_mul hA0 one_ne_zero).mpr (by simpa),
      (sqEq_iff_isSquare_mul hB0 one_ne_zero).mpr (by simpa)⟩
  rcases loc_torsion h2 hD0 hA0 hB0 h₁ h₂ h₃ with ⟨-, ha', hb'⟩ | ⟨-, ha', hb'⟩ | ⟨-, ha', hb'⟩ |
    ⟨hx0, hxd, hxd', hxa, hxb, hxab, -⟩
  · exact ⟨-1, -D, hm1, by rw [norm_neg, hD], ha', hb'⟩
  · exact ⟨D, 2, hD, hn2, ha', hb'⟩
  · exact ⟨-D, -2 * D, by rw [norm_neg, hD], by rw [norm_mul, norm_neg, hn2, hD, one_mul],
      ha', hb'⟩
  rcases lt_trichotomy ‖x‖ ‖D‖ with hlt | heq | hgt
  · -- `‖x‖ < 1`: `x − d ≡ −d`, `x + d ≡ d`, so `(a, b) ≡ (−1, −d)`
    have e₂ : SqEq (x - D) (-D) := by
      rw [show x - D = -D + x by ring]; exact sqEq_add_of_norm_lt hp2 (by rwa [norm_neg])
    have e₃ : SqEq (x + D) D := by
      rw [add_comm]; exact sqEq_add_of_norm_lt hp2 hlt
    have hb' : SqEq B (-D) := hxb.symm.trans e₂
    have hab : SqEq (A * B) D := hxab.symm.trans e₃
    have ha' : SqEq A (D * -D) := sqEq_of_mul_sqEq hab hb' (neg_ne_zero.mpr hD0)
    exact ⟨D * -D, -D, by rw [norm_mul, norm_neg, hD, one_mul], by rw [norm_neg, hD], ha', hb'⟩
  · -- `‖x‖ = 1`: `a ≡ x`, and one of `x ∓ d` is a unit
    have hx1 : ‖x‖ = 1 := heq.trans hD
    have hle : ∀ c : ℚ_[p], ‖c‖ = 1 → ‖x + c‖ ≤ 1 := fun c hc =>
      (Padic.nonarchimedean _ _).trans (by rw [hx1, hc, max_self])
    have hsub : ‖x - D‖ ≤ 1 := by rw [sub_eq_add_neg]; exact hle _ (by rw [norm_neg, hD])
    by_cases hm : ‖x - D‖ < 1
    · have hp1 : ‖x + D‖ = 1 := by
        refine le_antisymm (hle _ hD) (not_lt.mp fun hlt' => ?_)
        have h2D : ‖2 * D‖ = 1 := by rw [norm_mul, hn2, hD, one_mul]
        have := Padic.nonarchimedean (x + D) (-(x - D))
        rw [show x + D + -(x - D) = 2 * D by ring, h2D, norm_neg] at this
        exact absurd this (not_le.mpr (max_lt hlt' hm))
      have hba : SqEq (B * A) (x + D) := by rw [mul_comm]; exact hxab.symm
      have hb' : SqEq B ((x + D) * x) := sqEq_of_mul_sqEq hba hxa.symm hx0
      exact ⟨x, (x + D) * x, hx1, by rw [norm_mul, hp1, hx1, one_mul], hxa.symm, hb'⟩
    · exact ⟨x, x - D, hx1, le_antisymm hsub (not_lt.mp hm), hxa.symm, hxb.symm⟩
  · -- `‖x‖ > 1`: `x ± d ≡ x`, so `(a, b) ≡ (1, 1)`
    have e₂ : SqEq (x - D) x := by
      rw [sub_eq_add_neg]; exact sqEq_add_of_norm_lt hp2 (by rwa [norm_neg])
    have e₃ : SqEq (x + D) x := sqEq_add_of_norm_lt hp2 hgt
    have hb' : SqEq B x := hxb.symm.trans e₂
    have hab : SqEq (A * B) x := hxab.symm.trans e₃
    have ha' : SqEq A 1 := by
      have := sqEq_of_mul_sqEq hab hb' hx0
      exact (this.trans ⟨1, one_ne_zero, by ring⟩ : SqEq A (1 * x ^ 2)).of_mul_sq hx0
    exact ⟨1, 1, norm_one, norm_one, ha', hb'.trans (hxa.trans ha')⟩

/-- SQ(a) for a quotient of integers, from the residue of the quotient: if `p ∤ n`, and `m = 0`
or `p ∤ m`, and `m̄ / n̄` is a square in `𝔽_p`, then `m / n` is a square in `ℚ_p`. -/
theorem isSquare_padic_div_of_zmod (hp2 : p ≠ 2) {m n : ℤ} (hn : ¬(p : ℤ) ∣ n)
    (hm : m = 0 ∨ ¬(p : ℤ) ∣ m) (h : IsSquare ((m : ZMod p) / (n : ZMod p))) :
    IsSquare ((m : ℚ_[p]) / (n : ℚ_[p])) := by
  rcases hm with rfl | hm
  · exact ⟨0, by simp⟩
  refine isSquare_intCast_div_of_residue hp2 hm hn ?_
  obtain ⟨r, hr⟩ := h
  have hn0 : (n : ZMod p) ≠ 0 := by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have e : (m : ZMod p) = r * r * n := by rw [← hr]; field_simp
  exact ⟨r * n, by push_cast; rw [e]; ring⟩

/-- A squarefree integer with even `p`-adic valuation is prime to `p`. -/
theorem not_dvd_of_squarefree_of_even_padicValInt {a : ℤ} (ha : Squarefree a)
    (he : Even (padicValInt p a)) : ¬(p : ℤ) ∣ a := by
  intro hdvd
  have h1 : 1 ≤ padicValInt p a :=
    ((padicValInt_dvd_iff 1 a).mp (by simpa using hdvd)).resolve_left ha.ne_zero
  obtain ⟨k, hk⟩ := he
  have h2 : (p : ℤ) ^ 2 ∣ a := (padicValInt_dvd_iff 2 a).mpr (Or.inr (by omega))
  exact (Nat.prime_iff_prime_int.mp hp.out).not_isUnit (ha _ (by simpa [sq] using h2))

/-- **Lemma G2** (nt-prop0 §2.3): at an odd prime `p ∤ d`, every pair `(a, b)` of integers prime
to `p` is locally soluble. -/
theorem loc_padic_good_of_units (hp2 : p ≠ 2) {d : ℕ} (hpd : ¬p ∣ d) {a b : ℤ}
    (ha : ¬(p : ℤ) ∣ a) (hb : ¬(p : ℤ) ∣ b) : Loc ℚ_[p] d a b := by
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpd' : ¬(p : ℤ) ∣ (d : ℤ) := fun h => hpd (by exact_mod_cast h)
  have h2 : ¬(p : ℤ) ∣ 2 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp this)
  have hab : ¬(p : ℤ) ∣ a * b := fun h => (hpZ.dvd_or_dvd h).elim ha hb
  have h2d : ¬(p : ℤ) ∣ 2 * d := fun h => (hpZ.dvd_or_dvd h).elim h2 hpd'
  have nz : ∀ {c : ℤ}, ¬(p : ℤ) ∣ c → (c : ZMod p) ≠ 0 := fun hc h0 =>
    hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0)
  have ndvd : ∀ {c : ℤ}, (c : ZMod p) ≠ 0 → ¬(p : ℤ) ∣ c := fun hc h0 =>
    hc ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h0)
  rcases exists_xi hp2 (nz hpd') (nz ha) (nz hb) with ⟨hsa, hsb⟩ | ⟨ξ, h₁, h₂, h₃⟩
  · exact Or.inl ⟨isSquare_intCast_of_residue hp2 ha hsa, isSquare_intCast_of_residue hp2 hb hsb⟩
  -- an integer lift `x` of `ξ`, equal to `0`, `d` or `-d` when `ξ` is `0`, `d̄` or `-d̄`
  obtain ⟨x, hxξ, hx₀, hx₁, hx₂⟩ : ∃ x : ℤ, (x : ZMod p) = ξ ∧ (x = 0 ∨ ¬(p : ℤ) ∣ x) ∧
      (x - d = 0 ∨ ¬(p : ℤ) ∣ (x - d)) ∧ (x + d = 0 ∨ ¬(p : ℤ) ∣ (x + d)) := by
    by_cases e0 : ξ = 0
    · refine ⟨0, by rw [e0, Int.cast_zero], Or.inl rfl, Or.inr ?_, Or.inr ?_⟩
      · rwa [zero_sub, dvd_neg]
      · rwa [zero_add]
    by_cases e1 : ξ = ((d : ℤ) : ZMod p)
    · refine ⟨d, e1.symm, Or.inr hpd', Or.inl (sub_self _), Or.inr ?_⟩
      rwa [← two_mul]
    by_cases e2 : ξ = -((d : ℤ) : ZMod p)
    · refine ⟨-d, by rw [e2, Int.cast_neg], Or.inr (by rwa [dvd_neg]), Or.inr ?_,
        Or.inl (neg_add_cancel _)⟩
      rwa [show -(d : ℤ) - d = -(2 * d) by ring, dvd_neg]
    refine ⟨(ξ.cast : ℤ), ZMod.intCast_zmod_cast ξ, Or.inr (ndvd ?_), Or.inr (ndvd ?_),
      Or.inr (ndvd ?_)⟩
    · rwa [ZMod.intCast_zmod_cast]
    · rw [Int.cast_sub, ZMod.intCast_zmod_cast]; exact sub_ne_zero.mpr e1
    · rw [Int.cast_add, ZMod.intCast_zmod_cast]
      exact fun h => e2 (eq_neg_of_add_eq_zero_left h)
  right
  refine ⟨x, ?_, ?_, ?_⟩
  · have := isSquare_padic_div_of_zmod hp2 ha hx₀ (by rwa [hxξ])
    exact_mod_cast this
  · have := isSquare_padic_div_of_zmod hp2 hb hx₁ (by rwa [Int.cast_sub, hxξ])
    exact_mod_cast this
  · have := isSquare_padic_div_of_zmod hp2 hab hx₂ (by rwa [Int.cast_add, Int.cast_mul, hxξ])
    exact_mod_cast this

/-- nt-prop0 §2.3, the form the assembly uses: at an odd prime `p ∤ d`, a pair of squarefree
integers is locally soluble iff neither is divisible by `p`. -/
theorem loc_padic_good_iff (hp2 : p ≠ 2) {d : ℕ} (hpd : ¬p ∣ d) {a b : ℤ} (ha : Squarefree a)
    (hb : Squarefree b) : Loc ℚ_[p] d a b ↔ ¬(p : ℤ) ∣ a ∧ ¬(p : ℤ) ∣ b := by
  refine ⟨fun h => ?_, fun h => loc_padic_good_of_units hp2 hpd h.1 h.2⟩
  obtain ⟨ea, eb⟩ := loc_padic_good_even hp2 hpd ha.ne_zero hb.ne_zero h
  exact ⟨not_dvd_of_squarefree_of_even_padicValInt ha ea,
    not_dvd_of_squarefree_of_even_padicValInt hb eb⟩

end ZInQ.RouteK.Selmer
