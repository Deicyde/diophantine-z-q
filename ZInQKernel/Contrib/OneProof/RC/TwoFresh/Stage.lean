import ZInQKernel.Contrib.OneProof.RC.Odd.Statements

/-!
# The odd-stage divisibility at a two-fresh index

Tex 9741–9744, using (O.9) and (O.11) and the budget of tex 10208–10233.
The bound is proved after the budget and truncation are fixed, at any stage valid
for them. It is independent of the eventual choice of a positive index.
-/

namespace ZInQ.Manuscript.RC.TwoFresh

open ZInQ.Manuscript.RC.Odd

/-- Two distinct fresh primes occur to odd exponent in the tested index,
outside the added primes. In particular the index is off the unary support
(tex 9558–9559, 9620–9622, 9741–9743). -/
theorem fresh_squarefree_weight {U : Finset ℕ} {n q₁ q₂ : ℕ} (hn : n ≠ 0)
    (hp₁ : q₁.Prime) (hp₂ : q₂.Prime) (hne : q₁ ≠ q₂)
    (hU₁ : q₁ ∉ U) (hU₂ : q₂ ∉ U) (hn₁ : ¬ q₁ ∣ n) (hn₂ : ¬ q₂ ∣ n) :
    2 ≤ (oddPart (q₂ * (q₁ * n)) \ U).card ∧ ¬ oddPart (q₂ * (q₁ * n)) ⊆ U := by
  have h₂ : ¬ q₂ ∣ q₁ * n := fun hd =>
    hne.symm ((Nat.prime_dvd_prime_iff_eq hp₂ hp₁).mp ((hp₂.dvd_mul.mp hd).resolve_right hn₂))
  have e : oddPart (q₂ * (q₁ * n)) = insert q₂ (insert q₁ (oddPart n)) := by
    rw [oddPart_mul_prime hp₂ (mul_ne_zero hp₁.ne_zero hn) h₂, oddPart_mul_prime hp₁ hn hn₁]
  have h₁' : q₁ ∈ oddPart (q₂ * (q₁ * n)) := by rw [e]; simp
  have h₂' : q₂ ∈ oddPart (q₂ * (q₁ * n)) := by rw [e]; simp
  exact ⟨Finset.one_lt_card.mpr ⟨q₁, Finset.mem_sdiff.mpr ⟨h₁', hU₁⟩,
    q₂, Finset.mem_sdiff.mpr ⟨h₂', hU₂⟩, hne⟩, fun h => hU₁ (h h₁')⟩

/-- The off-unary test excludes every exponent of a unary correction
(tex 9620–9622, 9742–9743). -/
theorem ne_unary_of_oddPart {U J : Finset ℕ} {n k : ℕ} (hn : n ≠ 0)
    (hJ : J ⊆ U) (hprime : ∀ p ∈ J, Nat.Prime p) (hoff : ¬ oddPart n ⊆ U) :
    n ≠ (∏ p ∈ J, p) * k ^ 2 := by
  intro h
  have hk : k ≠ 0 := by rintro rfl; exact hn (by simpa using h)
  have hprod : (∏ p ∈ J, p) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp => (hprime p hp).ne_zero
  apply hoff
  rw [h, oddPart_mul_sq hprod hk]
  unfold oddPart
  exact (Finset.filter_subset _ _).trans ((Nat.primeFactors_prod hprime).le.trans hJ)

/-- The actual source coefficients reduced at precision `M`. -/
abbrev stageReduction (O : Type*) [CommRing O] (M : ℕ) : O →+* StageRing O M :=
  Ideal.Quotient.mk _

variable {O : Type*} [CommRing O]

/-- Coefficient reduction commutes with the added-prime operators
(on-the-spot, provenance (c)). -/
private theorem map_TL {O' : Type*} [CommRing O'] (f : O →+* O')
    (η a : ℕ → O) (U : List ℕ) (n : ℕ) :
    f (TL η U a n) = TL (fun p => f (η p)) U (fun k => f (a k)) n := by
  induction U generalizing n with
  | nil => rfl
  | cons p U ih =>
    simp only [TL_cons, Odd.Top, map_sub, map_mul, ← divCoeff_map, ih]

/-- Divisibility at precision `M` lifts to divisibility by any tested power
with exponent at most `M` (on-the-spot, provenance (c)). -/
private theorem dvd_of_stage_dvd {M k : ℕ} {x : O} (hk : k ≤ M)
    (h : (2 : StageRing O M) ^ k ∣ stageReduction O M x) : (2 : O) ^ k ∣ x := by
  obtain ⟨y, hy⟩ := h
  obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
  have hdiff : stageReduction O M (x - (2 : O) ^ k * z) = 0 := by
    simp only [map_sub, map_mul, map_pow, map_ofNat]
    exact sub_eq_zero.mpr hy
  have hM : (2 : O) ^ M ∣ x - (2 : O) ^ k * z :=
    Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hdiff)
  exact (dvd_iff_dvd_of_dvd_sub (two_pow_dvd_of_le hk hM)).mpr
    (dvd_mul_right ((2 : O) ^ k) z)

/-- At weight at least two outside the added primes, the normalized `B_U`
coefficient is four times an integral element, and the same coefficient divided
by two is twice that element. The precision used to lift (O.9) is supplied by
`OddStageSource.precision` (tex 9741–9744, 10226–10233). -/
theorem fresh_normalizations {K : Type*} [Field K] [CharZero K] [Algebra O K]
    {WU R M : ℕ} {δ : ℤ} {η a : ℕ → O} {Good adm : ℕ → Prop} {ap : ℕ → ℤ}
    (hstage : OddStageSource O WU R M δ (fun p => stageReduction O M (η p)) Good adm ap
      (fun n => stageReduction O M (a n))) (hR : 2 ≤ R)
    (U : List ℕ) (hnd : U.Nodup) (hU : ∀ p ∈ U, Good p) (hWU : U.length ≤ WU)
    (n : ℕ) (hweight : 2 ≤ (oddPart n \ U.toFinset).card) :
    ∃ c : O, (2 : K) ^ (-(δ + (U.length : ℤ))) * algebraMap O K (TL η U a n) =
        algebraMap O K ((2 : O) ^ 2 * c) ∧
      (2 : K) ^ (-(δ + (U.length : ℤ) + 1)) * algebraMap O K (TL η U a n) =
        algebraMap O K (2 * c) := by
  let d : ℤ := δ + U.length
  let k := (d + 2).toNat
  have hk : k ≤ M := by
    have := hstage.precision hR hWU
    dsimp [k, d]
    omega
  have hpow := O9_odd_stage hstage U hnd hU hWU n
  rw [← map_TL] at hpow
  have hle : k ≤ (δ + U.length + min (R : ℤ) (oddPart n \ U.toFinset).card).toNat := by
    dsimp [k, d]
    omega
  obtain ⟨b, hb⟩ := dvd_of_stage_dvd hk (two_pow_dvd_of_le hle hpow)
  let l := ((k : ℤ) - d - 2).toNat
  have hkl : (k : ℤ) = d + 2 + l := by dsimp [l, k]; omega
  have htwo : (2 : K) ≠ 0 := by norm_num
  have scale (i : ℤ) (j : ℕ) (hij : i + j = 2) :
      (2 : K) ^ (-(d + i)) * algebraMap O K (TL η U a n) =
        algebraMap O K ((2 : O) ^ j * ((2 : O) ^ l * b)) := by
    rw [hb]
    simp only [map_mul, map_pow, map_ofNat, ← mul_assoc, ← zpow_natCast (2 : K),
      ← zpow_add₀ htwo]
    rw [show -(d + i) + (k : ℤ) = (j : ℤ) + l by omega]
  exact ⟨(2 : O) ^ l * b, by simpa only [add_zero] using scale 0 2 (by norm_num),
    by simpa only [pow_one] using scale 1 1 (by norm_num)⟩


end ZInQ.Manuscript.RC.TwoFresh
