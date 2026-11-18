import ZInQKernel.Contrib.PoleRC.Matrix
import ZInQKernel.Contrib.PoleRC.LinAlg

/-!
# Reciprocity identities for the matrix `K` and the forcing of the local equations

For positive squarefree `ℓ ≡ 11 (mod 12)` with prime support `q₁, …, q_k`:

* `kmat_transpose`: `Kᵀ = K + ssᵗ + diag(s)` (quadratic reciprocity);
* `kmat_mulVec_one`: `K1 = 0`;
* `sgn_dot_one`: `sᵗ1 = 1` (`ℓ ≡ 3 (mod 4)`);
* `lam_dot_one`: `λᵗ1 = 0` (`(3/ℓ) = 1`, from reciprocity with `3`);
* `kmat_forces`: under `MatrixConditions ℓ β`, every solution of the local equations at the
  `q_i`, at two and at three has `v = σ1`, `δ = σ`, `Ku = 0` (`diophantine_zq.tex` line 1068).
-/

namespace ZInQ.Manuscript.PoleRC

open Matrix

variable {ℓ : ℕ}

theorem supp_prime (i : Supp ℓ) : (i : ℕ).Prime := (Nat.mem_primeFactors.mp i.2).1

theorem supp_dvd (i : Supp ℓ) : (i : ℕ) ∣ ℓ := (Nat.mem_primeFactors.mp i.2).2.1

theorem supp_mod_two (h : ℓ % 2 = 1) (i : Supp ℓ) : (i : ℕ) % 2 = 1 := by
  rcases (supp_prime i).eq_two_or_odd with h2 | h2
  · have := supp_dvd i; rw [h2] at this; omega
  · exact h2

theorem supp_ne_three (h : ℓ % 3 ≠ 0) (i : Supp ℓ) : (i : ℕ) ≠ 3 := by
  intro h3; have := supp_dvd i; rw [h3] at this; omega

theorem lsym_congr {a b : ℤ} {q r : ℕ} (h : IsSquare (a : ZMod q) ↔ IsSquare (b : ZMod r)) :
    lsym a q = lsym b r := by
  unfold lsym
  by_cases hb : IsSquare (b : ZMod r)
  · rw [if_pos (h.mpr hb), if_pos hb]
  · rw [if_neg (fun h' => hb (h.mp h')), if_neg hb]

theorem lsym_congr_not {a b : ℤ} {q r : ℕ} (h : IsSquare (a : ZMod q) ↔ ¬ IsSquare (b : ZMod r)) :
    lsym a q = lsym b r + 1 := by
  unfold lsym
  by_cases hb : IsSquare (b : ZMod r)
  · rw [if_neg (fun h' => h.mp h' hb), if_pos hb]; rfl
  · rw [if_pos (h.mpr hb), if_neg hb]; decide

theorem lsym_of_isSquare {a : ℤ} {q : ℕ} (h : IsSquare (a : ZMod q)) : lsym a q = 0 := by
  unfold lsym; rw [if_pos h]

theorem lsym_of_not_isSquare {a : ℤ} {q : ℕ} (h : ¬ IsSquare (a : ZMod q)) : lsym a q = 1 := by
  unfold lsym; rw [if_neg h]

theorem lsym_neg_one (q : ℕ) [Fact q.Prime] : lsym (-1) q = if q % 4 = 3 then 1 else 0 := by
  have h := ZMod.exists_sq_eq_neg_one_iff (p := q)
  by_cases h3 : q % 4 = 3
  · rw [if_pos h3]
    exact lsym_of_not_isSquare (by push_cast; rw [h]; exact not_not.mpr h3)
  · rw [if_neg h3]
    exact lsym_of_isSquare (by push_cast; rw [h]; exact h3)

/-- **Quadratic reciprocity, additive form**: `[p/q] = [q/p] + s_p s_q`. -/
theorem lsym_recip (p q : ℕ) [Fact p.Prime] [Fact q.Prime] (hp : p % 2 = 1) (hq : q % 2 = 1)
    (hpq : p ≠ q) : lsym (p : ℤ) q = lsym (q : ℤ) p + lsym (-1) p * lsym (-1) q := by
  rw [lsym_neg_one, lsym_neg_one]
  have hp4 : p % 4 = 1 ∨ p % 4 = 3 := by omega
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  rcases hp4 with hp4 | hp4
  · have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := p) (q := q) hp4 (by omega)
    rw [if_neg (by omega), zero_mul, add_zero]
    exact lsym_congr (by simpa using this.symm)
  · rcases hq4 with hq4 | hq4
    · have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := q) (q := p) hq4 (by omega)
      rw [if_neg (show ¬ q % 4 = 3 by omega), mul_zero, add_zero]
      exact lsym_congr (by simpa using this)
    · have := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := q) (q := p) hq4 hp4
        (Ne.symm hpq)
      rw [if_pos hp4, if_pos hq4, mul_one]
      exact lsym_congr_not (by simpa using this)

theorem zmod2_mul_self_add (x : ZMod 2) : x * x + x = 0 := by
  fin_cases x <;> decide

/-- **`Kᵀ = K + ssᵗ + diag(s)`** for odd `ℓ`. -/
theorem kmat_transpose (h2 : ℓ % 2 = 1) :
    (Kmat ℓ)ᵀ = Kmat ℓ + vecMulVec (sgn ℓ) (sgn ℓ) + diagonal (sgn ℓ) := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp only [transpose_apply, Matrix.add_apply, vecMulVec_apply, diagonal_apply_eq]
    rw [add_assoc, zmod2_mul_self_add, add_zero]
  · have hp := Fact.mk (supp_prime i)
    have hq := Fact.mk (supp_prime j)
    have hij' : (i : ℕ) ≠ j := fun h => hij (Subtype.ext h)
    simp only [transpose_apply, Matrix.add_apply, vecMulVec_apply, diagonal_apply_ne _ hij,
      add_zero]
    simp only [Kmat, sgn]
    rw [if_neg (Ne.symm hij), if_neg hij]
    exact lsym_recip i j (supp_mod_two h2 i) (supp_mod_two h2 j) hij'

/-- **`K1 = 0`.** -/
theorem kmat_mulVec_one : Kmat ℓ *ᵥ 1 = 0 := by
  funext i
  simp only [mulVec, dotProduct, Pi.one_apply, mul_one, Pi.zero_apply]
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  have : ∀ j ∈ Finset.univ.erase i, Kmat ℓ i j = lsym (j : ℕ) i := fun j hj => by
    simp [Kmat, Ne.symm (Finset.ne_of_mem_erase hj)]
  rw [Finset.sum_congr rfl this]
  simp only [Kmat, if_pos rfl]
  exact zmod2_add_self _

/-- The number of primes `≡ r (mod k)` dividing a squarefree `ℓ` has the parity of the
exponent of `−1` in `ℓ` modulo `k`, when every prime factor is `≡ ±1`. Here: modulo `4`. -/
theorem card_filter_mod_four_odd (hsf : Squarefree ℓ) (h4 : ℓ % 4 = 3) :
    Odd (ℓ.primeFactors.filter (fun q => q % 4 = 3)).card := by
  have hprod : ∏ q ∈ ℓ.primeFactors, q = ℓ := Nat.prod_primeFactors_of_squarefree hsf
  have h2 : ℓ % 2 = 1 := by omega
  have hq : ∀ q ∈ ℓ.primeFactors, (q : ZMod 4) = if q % 4 = 3 then -1 else 1 := by
    intro q hq
    have hqp := (Nat.mem_primeFactors.mp hq).1
    have hqd := (Nat.mem_primeFactors.mp hq).2.1
    have hq2 : q % 2 = 1 := by
      rcases hqp.eq_two_or_odd with h | h
      · rw [h] at hqd; omega
      · exact h
    rw [← ZMod.natCast_mod q 4]
    have : q % 4 = 1 ∨ q % 4 = 3 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have hZ : (ℓ : ZMod 4) = (-1) ^ (ℓ.primeFactors.filter (fun q => q % 4 = 3)).card := by
    conv_lhs => rw [← hprod]
    push_cast
    rw [Finset.prod_congr rfl hq, Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_const]
  have hl : (ℓ : ZMod 4) = -1 := by
    rw [← ZMod.natCast_mod ℓ 4, h4]; decide
  rw [hl] at hZ
  rcases Nat.even_or_odd (ℓ.primeFactors.filter (fun q => q % 4 = 3)).card with he | ho
  · rw [he.neg_one_pow] at hZ; exact absurd hZ (by decide)
  · exact ho

/-- The same modulo `3`. -/
theorem card_filter_mod_three_odd (hsf : Squarefree ℓ) (h3 : ℓ % 3 = 2) :
    Odd (ℓ.primeFactors.filter (fun q => q % 3 = 2)).card := by
  have hprod : ∏ q ∈ ℓ.primeFactors, q = ℓ := Nat.prod_primeFactors_of_squarefree hsf
  have hq : ∀ q ∈ ℓ.primeFactors, (q : ZMod 3) = if q % 3 = 2 then -1 else 1 := by
    intro q hq
    have hqd := (Nat.mem_primeFactors.mp hq).2.1
    have hq3 : q % 3 ≠ 0 := by
      intro h; have : 3 ∣ ℓ := (Nat.dvd_of_mod_eq_zero h).trans hqd; omega
    rw [← ZMod.natCast_mod q 3]
    have : q % 3 = 1 ∨ q % 3 = 2 := by omega
    rcases this with h | h <;> rw [h] <;> decide
  have hZ : (ℓ : ZMod 3) = (-1) ^ (ℓ.primeFactors.filter (fun q => q % 3 = 2)).card := by
    conv_lhs => rw [← hprod]
    push_cast
    rw [Finset.prod_congr rfl hq, Finset.prod_ite, Finset.prod_const_one, mul_one,
      Finset.prod_const]
  have hl : (ℓ : ZMod 3) = -1 := by
    rw [← ZMod.natCast_mod ℓ 3, h3]; decide
  rw [hl] at hZ
  rcases Nat.even_or_odd (ℓ.primeFactors.filter (fun q => q % 3 = 2)).card with he | ho
  · rw [he.neg_one_pow] at hZ; exact absurd hZ (by decide)
  · exact ho

theorem sum_supp_eq (f : ℕ → ZMod 2) : ∑ i : Supp ℓ, f i = ∑ q ∈ ℓ.primeFactors, f q :=
  Finset.sum_coe_sort ℓ.primeFactors f

/-- **`sᵗ1 = 1`** for squarefree `ℓ ≡ 3 (mod 4)`. -/
theorem sgn_dot_one (hsf : Squarefree ℓ) (h4 : ℓ % 4 = 3) : sgn ℓ ⬝ᵥ 1 = 1 := by
  classical
  have h : ∀ i : Supp ℓ, sgn ℓ i * (1 : Supp ℓ → ZMod 2) i =
      if (i : ℕ) % 4 = 3 then (1 : ZMod 2) else 0 := by
    intro i
    have := Fact.mk (supp_prime i)
    rw [Pi.one_apply, mul_one, sgn, lsym_neg_one]
  rw [dotProduct, Finset.sum_congr rfl (fun i _ => h i),
    sum_supp_eq (fun q => if q % 4 = 3 then (1 : ZMod 2) else 0), Finset.sum_boole]
  exact ZMod.natCast_eq_one_iff_odd.mpr (card_filter_mod_four_odd hsf h4)

theorem isSquare_zmod3_iff (q : ℕ) (hq : q % 3 ≠ 0) : IsSquare (q : ZMod 3) ↔ q % 3 = 1 := by
  rw [← ZMod.natCast_mod q 3]
  have : q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases this with h | h <;> rw [h]
  · exact ⟨fun _ => rfl, fun _ => ⟨1, rfl⟩⟩
  · refine ⟨fun ⟨r, hr⟩ => ?_, fun h => absurd h (by norm_num)⟩
    fin_cases r <;> revert hr <;> decide

/-- `[3/q] = [q ≡ 2 (mod 3)] + [q ≡ 3 (mod 4)]` for odd primes `q ≠ 3`. -/
theorem lsym_three (q : ℕ) [hq : Fact q.Prime] (h2 : q % 2 = 1) (h3 : q ≠ 3) :
    lsym 3 q = (if q % 3 = 2 then 1 else 0) + (if q % 4 = 3 then 1 else 0) := by
  have hq3 : q % 3 ≠ 0 := by
    intro h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hq.out).mp (Nat.dvd_of_mod_eq_zero h)
    exact h3 this.symm
  have := Fact.mk Nat.prime_three
  have hq4 : q % 4 = 1 ∨ q % 4 = 3 := by omega
  have hq3' : q % 3 = 1 ∨ q % 3 = 2 := by omega
  have hz := isSquare_zmod3_iff q hq3
  rcases hq4 with hq4 | hq4
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_one (p := q) (q := 3) hq4 (by norm_num)
    rw [hz] at h
    rw [if_neg (show ¬ q % 4 = 3 by omega), add_zero]
    rcases hq3' with h' | h'
    · rw [if_neg (by omega)]
      exact lsym_of_isSquare (by simpa using h.mpr h')
    · rw [if_pos h']
      exact lsym_of_not_isSquare (by simpa [h'] using h)
  · have h := ZMod.exists_sq_eq_prime_iff_of_mod_four_eq_three (p := q) (q := 3) hq4
      (by norm_num) h3
    rw [hz] at h
    rw [if_pos hq4]
    rcases hq3' with h' | h'
    · rw [if_neg (by omega), zero_add]
      exact lsym_of_not_isSquare (by simpa [h'] using h)
    · rw [if_pos h']
      exact (lsym_of_isSquare (by simpa [h'] using h)).trans (by decide)

/-- **`λᵗ1 = 0`** for squarefree `ℓ ≡ 11 (mod 12)`. -/
theorem lam_dot_one (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) : lam ℓ ⬝ᵥ 1 = 0 := by
  classical
  have h : ∀ i : Supp ℓ, lam ℓ i * (1 : Supp ℓ → ZMod 2) i =
      (if (i : ℕ) % 3 = 2 then (1 : ZMod 2) else 0) + (if (i : ℕ) % 4 = 3 then 1 else 0) := by
    intro i
    have := Fact.mk (supp_prime i)
    simp only [lam, Pi.one_apply, mul_one]
    exact lsym_three i (supp_mod_two (by omega) i) (supp_ne_three (by omega) i)
  rw [dotProduct, Finset.sum_congr rfl (fun i _ => h i),
    sum_supp_eq (fun q => (if q % 3 = 2 then (1 : ZMod 2) else 0) + (if q % 4 = 3 then 1 else 0)),
    Finset.sum_add_distrib,
    Finset.sum_boole, Finset.sum_boole]
  rw [ZMod.natCast_eq_one_iff_odd.mpr (card_filter_mod_three_odd hsf (by omega)),
    ZMod.natCast_eq_one_iff_odd.mpr (card_filter_mod_four_odd hsf (by omega))]
  decide

/-- **The matrix conditions force the local equations** (line 1068, both signs of the second
coordinate, with the equation at two). -/
theorem kmat_forces {β : ℕ} (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11)
    (hM : MatrixConditions ℓ β) (u v : Supp ℓ → ZMod 2) (δ σ : ZMod 2)
    (E1 : Kmat ℓ *ᵥ u + lam ℓ * v = δ • lam ℓ) (E2 : Kmat ℓ *ᵥ v + sgn ℓ * v = σ • sgn ℓ)
    (E3 : sgn ℓ ⬝ᵥ v = σ) (E4 : (lam ℓ + sgn ℓ) ⬝ᵥ v = σ) :
    v = σ • 1 ∧ δ = σ ∧ Kmat ℓ *ᵥ u = 0 :=
  dimThree_linear_algebra (Kmat ℓ) (sgn ℓ) (lam ℓ) (oneB ℓ β) (kmat_transpose (by omega))
    kmat_mulVec_one (sgn_dot_one hsf (by omega)) (lam_dot_one hsf h12) hM.2.2.2.1 hM.2.2.2.2
    u v δ σ E1 E2 E3 E4

end ZInQ.Manuscript.PoleRC
