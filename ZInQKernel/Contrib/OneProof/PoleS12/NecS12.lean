import ZInQKernel.Contrib.OneProof.PoleS12.TwoAdic

/-!
# The necessary local conditions of a Selmer class, following S12

ELLIOT (supplement S12, `par:descent`, lines 381–433). Round 1's `NecAt ℓ` asks at `2` for
`a` odd and `b ≡ 1 (mod 4)`. S12 needs only even valuations at `2` (proved in `TwoAdic.lean`);
the congruence `b ≡ 1 (mod 4)` then follows from the conditions at the primes of `ℓ`: summing the
equation `(K + D_s)v = σs` against `1` gives `sᵗv = σ` (S12 L416–418: "left multiplying `Nv = 0`
by `1ᵗ` gives `sᵗv = 0`"), which is `b ≡ 1 (mod 4)`.

`necAt_S12 : NecAt ℓ` for positive squarefree `ℓ ≡ 11 (mod 12)`, with no hypothesis: every
local condition is proved (`two_adic_odd`, `localThree_nec`, `localGood_nec`, `localBad_nec`).
-/

namespace ZInQ.Manuscript.PoleS12

open Matrix ZInQ.Manuscript.PoleRC

variable {ℓ : ℕ}

/-- `1ᵗK = 0` (S12 L285–288, from `K + Kᵗ = ssᵗ + D_s` and `sᵗ1 = 1`). -/
theorem one_vecMul_kmat (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) :
    (1 : Supp ℓ → ZMod 2) ᵥ* Kmat ℓ = 0 := by
  have hT : ∀ x, (Kmat ℓ)ᵀ *ᵥ x = Kmat ℓ *ᵥ x + (sgn ℓ ⬝ᵥ x) • sgn ℓ + sgn ℓ * x := by
    intro x
    rw [kmat_transpose (by omega), Matrix.add_mulVec, Matrix.add_mulVec, vecMulVec_mulVec]
    funext i
    simp [Matrix.mulVec_diagonal, mul_comm]
  rw [← Matrix.mulVec_transpose, hT, kmat_mulVec_one, sgn_dot_one hsf (by omega)]
  funext i; simp [zmod2_add_self]

/-- **`sᵗv = σ` from `(K + D_s)v = σs`** (S12 L416–418). -/
theorem e3_of_e2 (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) {v : Supp ℓ → ZMod 2} {σ : ZMod 2}
    (E2 : Kmat ℓ *ᵥ v + sgn ℓ * v = σ • sgn ℓ) : sgn ℓ ⬝ᵥ v = σ := by
  have h := congrArg (fun w => (1 : Supp ℓ → ZMod 2) ⬝ᵥ w) E2
  simp only [dotProduct_add, Matrix.dotProduct_mulVec, one_vecMul_kmat hsf h12,
    zero_dotProduct, zero_add, dotProduct_smul, smul_eq_mul] at h
  rw [show (1 : Supp ℓ → ZMod 2) ⬝ᵥ sgn ℓ = 1 by
    rw [dotProduct_comm]; exact sgn_dot_one hsf (by omega), mul_one] at h
  rw [← h, dotProduct, dotProduct]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- **`b ≡ 1 (mod 4)` from `sᵗv = σ`** (the converse of round 1's `e3_of_mod4`). -/
theorem mod4_of_e3 (h12 : ℓ % 12 = 11) {b : ℤ} (hb : Squarefree b)
    (hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors) (E3 : sgn ℓ ⬝ᵥ ind ℓ b = sg b) :
    b % 4 = 1 := by
  classical
  have hT : ∀ p ∈ b.natAbs.primeFactors, p % 2 = 1 := fun p hp =>
    supp_mod_two (ℓ := ℓ) (by omega) ⟨p, hsb hp⟩
  have hZ := intCast_eq_sign_mul (ZMod 4) b
  rw [natAbs_eq_prod hb, prod_zmod4 _ hT] at hZ
  have hdot : sgn ℓ ⬝ᵥ ind ℓ b = ((b.natAbs.primeFactors.filter (fun p => p % 4 = 3)).card :
      ZMod 2) := by
    rw [dotProduct, ← dot_ind_eq_card (fun p => p % 4 = 3) hsb]
    refine Finset.sum_congr rfl fun i _ => ?_
    have := Fact.mk (supp_prime i)
    rw [sgn, lsym_neg_one]
  rw [hdot, sg_eq_cast] at E3
  set c := (b.natAbs.primeFactors.filter (fun p => p % 4 = 3)).card
  set σ : ℕ := if b < 0 then 1 else 0 with hσ
  have hpar : Even (σ + c) := by
    have h0 : ((σ + c : ℕ) : ZMod 2) = 0 := by
      push_cast; rw [E3]; exact zmod2_add_self _
    exact (ZMod.natCast_eq_zero_iff_even).mp h0
  have hb1 : (b : ZMod 4) = 1 := by
    rw [hZ, show ((if b < 0 then -1 else 1 : ZMod 4)) = (-1) ^ σ by
      rw [hσ]; split_ifs <;> simp, ← pow_add, hpar.neg_one_pow]
  have := (ZMod.intCast_eq_intCast_iff' b 1 4).mp (by rw [hb1]; simp)
  simpa using this

/-- **The necessary conditions at every place, all proved** (S12 L337–433, ELLIOT (supplement)):
round 1's `NecAt ℓ` for positive squarefree `ℓ ≡ 11 (mod 12)`. -/
theorem necAt_S12 (hsf : Squarefree ℓ) (h12 : ℓ % 12 = 11) : NecAt ℓ := by
  intro a b hab
  have hab' := hab
  obtain ⟨ha, hb, hR, hp⟩ := hab
  simp only at ha hb hR hp
  have hℓ : 0 < ℓ := by omega
  obtain ⟨ha2, hb2⟩ := two_adic_odd (ℓ := ℓ) (by omega) ha hb (hp 2)
  have hb3 : b % 3 = 1 := localThree_nec (ℓ := ℓ) (by omega) ha hb (hp 3)
  have hgood : ∀ p : ℕ, p.Prime → ¬ p ∣ 6 * ℓ → ¬ (p : ℤ) ∣ a ∧ ¬ (p : ℤ) ∣ b := by
    intro p hpp hnd
    have := Fact.mk hpp
    exact localGood_nec hnd ha hb (hp p)
  have hbad : ∀ i : Supp ℓ, ∃ e₁ e₂ : ZMod 2, qcls i a = e₁ • qcls i ℓ + e₂ • qcls i 3 ∧
      qcls i b = e₂ • qcls i (-(ℓ : ℤ)) := by
    intro i
    have := Fact.mk (supp_prime i)
    exact localBad_nec hsf h12 (supp_dvd i)
      (by have := supp_mod_two (ℓ := ℓ) (by omega) i; omega) (supp_ne_three (by omega) i)
      ha hb (hp i)
  refine ⟨⟨ha2, ?_⟩, hb3, hgood, hbad⟩
  -- `b ≡ 1 (mod 4)` from the conditions at the primes of `ℓ`
  have ha0 : 0 < a := (localReal ℓ a b hℓ ha.ne_zero hb.ne_zero).mp hR
  have hsupp : ∀ x : ℤ, x % 2 = 1 → (∀ p : ℕ, p.Prime → ¬ p ∣ 6 * ℓ → ¬ (p : ℤ) ∣ x) →
      x.natAbs.primeFactors ⊆ insert 3 ℓ.primeFactors := by
    intro x hx2 hxg p hpx
    have hpp := (Nat.mem_primeFactors.mp hpx).1
    have hpd : (p : ℤ) ∣ x := Int.natCast_dvd.mpr (Nat.mem_primeFactors.mp hpx).2.1
    by_cases h6 : p ∣ 6 * ℓ
    · rcases prime_dvd_six_mul hpp h6 with h | h | h
      · subst h; omega
      · subst h; exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (Nat.mem_primeFactors.mpr ⟨hpp, h, by omega⟩)
    · exact absurd hpd (hxg p hpp h6)
  have hsa := hsupp a ha2 (fun p hpp hnd => (hgood p hpp hnd).1)
  have hsb : b.natAbs.primeFactors ⊆ ℓ.primeFactors := by
    intro p hpx
    rcases Finset.mem_insert.mp (hsupp b hb2 (fun p hpp hnd => (hgood p hpp hnd).2) hpx)
      with h | h
    · subst h
      have : (3 : ℤ) ∣ b := Int.natCast_dvd.mpr (Nat.mem_primeFactors.mp hpx).2.1
      omega
    · exact h
  obtain ⟨-, E2⟩ := eqs_of_localBad hsf h12 ha hb ha0 hsa hsb hbad
  exact mod4_of_e3 h12 hb hsb (e3_of_e2 hsf h12 E2)

end ZInQ.Manuscript.PoleS12
