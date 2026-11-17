import ZInQKernel.Contrib.OneProof.TYZLemma28Sym
import ZInQKernel.Contrib.OneProof.TYZThm21At31
import ZInQKernel.Contrib.OneProof.TYZTestVectorExists
import ZInQKernel.Contrib.OneProof.LegendreThreeSquares
import ZInQKernel.Contrib.OneProof.JonesPall
import ZInQKernel.Contrib.OneProof.TYZThm11Integral

/-!
# TYZ Theorem 1.1 (integrality, `h11`) and Lemma 2.9 (`hL29`) from TYZ Theorem 2.1 and `𝓛(1)² = 1`

Task tyz-genus; report `docs/research/tyz-genus.md`. TYZ = Tian–Yuan–Zhang, arXiv:1411.4728v1 (source not on the
host; line numbers quoted from the project notes).

* `TYZThm21PairsC`: TYZ Theorem 2.1 for every pair (h29-proof's `TYZThm21Pairs`) with the sign choices `ℓ` of `𝓛`
  complex (`ℓ(m)² = 𝓛(m)²`, `ℓ : ℕ → ℂ`) instead of integer. TYZ's `𝓛(m)` is a real number (L338–353), and a complex
  `ℓ` with `ℓ² = 𝓛²` is `±𝓛`, whose sign is absorbed by `ε`: this is the print. Unlike the integer form it is not
  vacuous when Theorem 1.1 is not assumed (complex sign choices always exist), so it can prove Theorem 1.1.
* `tyzThm21Pairs_of_C`: it implies `TYZThm21Pairs`.
* `tyzThm11Integral_of_thm21C`: `h11 = TYZThm11Integral` from `TYZThm21PairsC` and `TYZLcalOne` (`𝓛(1)² = 1`, TYZ
  L1082, asserted there; Tunnell 1983 at `n = 1`), by TYZ's induction (L1081–1088): Lemma 2.9 (from Theorem 2.1 and
  the proved Lemma 2.8) at `n ≠ 3`, and Theorem 2.1 at `(3, 1)` with `f_3(1) = ±3` (t21-proof) at `n = 3`.

No `sorry`, no `axiom`.
-/

set_option linter.style.longLine false

noncomputable section

namespace ZInQ.Contrib.TYZGenusFold

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b ZInQ.Contrib.TYZDecomp
open ZInQ.Contrib.TYZDecomp.H29Split ZInQ.Contrib.TYZDecomp.H29Genus NumberField
open ZInQ.Contrib.TYZGenus.TYZ35 (gchar divSet)
open scoped Quaternion

/-- `ℓ` is a complex sign choice of TYZ's `𝓛` on the squarefree classes `1, 3 (mod 8)`. -/
def IsLcalSignC (ℓ : ℕ → ℂ) : Prop :=
  ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ℓ m ^ 2 = lcalSq m

/-- **TYZ Theorem 2.1 (L554–559) for every decomposition, odd classes, complex sign choices.** As
`H29Genus.TYZThm21Pairs` (same quadratic periods, same two clauses, same restrictions: odd classes, `n > 1`; the
first clause only for pairs with no factor `≡ 1 (mod 8)`), with `ℓ : ℕ → ℂ`, `ℓ(m)² = 𝓛(m)²`. -/
def TYZThm21PairsC : Prop :=
  ∀ (n : ℕ) [NeZero n], Squarefree n → 1 < n → (n % 8 = 1 ∨ n % 8 = 3) →
    ∀ τ : QNeg n →ₐ[ℚ] ℍ[ℚ], AdmissibleTau n τ → ∀ f : ℍ[AQ] → ℤ, IsTestVector n τ f →
      ∀ ℓ : ℕ → ℂ, IsLcalSignC ℓ → ∀ d₁ d₂ : ℕ, d₁ * d₂ = n →
        (d₁ % 8 ≠ 1 → d₂ % 8 ≠ 1 → quadPeriod n τ f d₂ = 0) ∧
        (d₂ % 8 = 1 → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
          (quadPeriod n τ f d₂ : ℂ) = ε * 2 ^ (n.primeFactors.card - 1) *
            ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) * (ℓ d₁ * ℓ d₂))

/-- The complex form implies the integer form. -/
theorem tyzThm21Pairs_of_C (h : TYZThm21PairsC) : TYZThm21Pairs := by
  intro n _ hsq h1 hcl τ hτ f hf ℓ hℓ d₁ d₂ hd
  obtain ⟨hA, hB⟩ := h n hsq h1 hcl τ hτ f hf (fun m => (ℓ m : ℂ)) (fun m hm hc => hℓ m hm hc) d₁ d₂ hd
  refine ⟨hA, fun h8 => ?_⟩
  obtain ⟨ε, hε, heq⟩ := hB h8
  refine ⟨ε, hε, ?_⟩
  have h2 : ((quadPeriod n τ f d₂ : ℤ) : ℂ) = ((ε * 2 ^ (n.primeFactors.card - 1) *
      ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℤ) * (ℓ d₁ * ℓ d₂) : ℤ) : ℂ) := by
    rw [heq]; simp only [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]
  exact_mod_cast h2

/-- Choosing the signs (complex). -/
theorem sum_formulaC {n : ℕ} (s : Finset ℕ) (P : ℕ → ℤ) (c : ℂ) (ℓ : ℕ → ℂ)
    (hF : ∀ e ∈ s, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (P e : ℂ) = ε * c * (ℓ (n / e) * ℓ e)) :
    ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧
      ((∑ e ∈ s, P e : ℤ) : ℂ) = c * ∑ e ∈ s, (ε e : ℂ) * (ℓ (n / e) * ℓ e) := by
  classical
  choose! ε hε hP using hF
  refine ⟨fun d => if d ∈ s then ε d else 1, fun d => ?_, ?_⟩
  · by_cases h : d ∈ s
    · simp only [h, if_true]; exact hε d h
    · simp only [h, if_false]; left; trivial
  · rw [Finset.mul_sum]
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [he, if_true]
    rw [hP e he]; ring

/-- **TYZ's proof of Lemma 2.9** (L1068–1077) for complex sign choices: from Theorem 2.1 for every pair and the
proved Lemma 2.8, `w_K Σ ε 𝓛(d₁)𝓛(d₂) = Q(n)`. -/
theorem lemma29_coreC (h21 : TYZThm21PairsC) {n : ℕ} [NeZero n]
    (hsq : Squarefree n) (h1 : 1 < n) (hcl : n % 8 = 1 ∨ n % 8 = 3) {τ : QNeg n →ₐ[ℚ] ℍ[ℚ]}
    (hτ : AdmissibleTau n τ) {f : ℍ[AQ] → ℤ} (hf : IsTestVector n τ f) {ℓ : ℕ → ℂ}
    (hℓ : IsLcalSignC ℓ) :
    ∃ ε : ℕ → ℤ, (∀ d, ε d = 1 ∨ ε d = -1) ∧
      ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) *
        ∑ d ∈ pairIdx n, (ε d : ℂ) * (ℓ (n / d) * ℓ d) = (genusPeriodTV n τ f : ℂ) := by
  set k := n.primeFactors.card with hkdef
  set w : ℂ := ((NumberField.Units.torsionOrder (QNeg n) / 2 : ℕ) : ℂ) with hwdef
  have hn : Odd n := Nat.odd_iff.mpr (by omega)
  have hk : 1 ≤ k := Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr h1)
  have hdm : ∀ e ∈ n.divisors, n / e * e = n := fun e he =>
    Nat.div_mul_cancel (Nat.dvd_of_mem_divisors he)
  have hV : ∀ e ∈ n.divisors, (n / e) % 8 ≠ 1 → e % 8 ≠ 1 → quadPeriod n τ f e = 0 := fun e he h h' =>
    (h21 n hsq h1 hcl τ hτ f hf ℓ hℓ (n / e) e (hdm e he)).1 h h'
  have hsum : ∑ e ∈ n.divisors, quadPeriod n τ f e = 2 * ∑ e ∈ pairIdx n, quadPeriod n τ f e := by
    rcases hcl with h | h
    · exact sum_divisors_one h hsq h1 (quadPeriod n τ f) hV fun e he he1 =>
        (tyzLemma28Sym n hsq h1 h τ hτ f hf (n / e) e (hdm e he) he1).symm
    · exact sum_divisors_three h (quadPeriod n τ f) hV fun e he =>
        quadPeriod_div (by omega) hsq h1 τ f (Nat.dvd_of_mem_divisors he)
  have hF : ∀ e ∈ pairIdx n, ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧
      (quadPeriod n τ f e : ℂ) = ε * (2 ^ (k - 1) * w) * (ℓ (n / e) * ℓ e) := by
    intro e he
    have hmem := Finset.mem_filter.mp he
    obtain ⟨ε, hε, heq⟩ :=
      (h21 n hsq h1 hcl τ hτ f hf ℓ hℓ (n / e) e (hdm e hmem.1)).2 hmem.2.1
    exact ⟨ε, hε, by rw [heq]; ring⟩
  obtain ⟨ε, hε, hP⟩ := sum_formulaC (n := n) _ (quadPeriod n τ f) _ ℓ hF
  refine ⟨ε, hε, ?_⟩
  have hPQ := sum_quadPeriod hn hsq h1 τ f
  rw [hsum] at hPQ
  have hPQc : (2 : ℂ) * ((∑ e ∈ pairIdx n, quadPeriod n τ f e : ℤ) : ℂ) =
      2 ^ k * (genusPeriodTV n τ f : ℂ) := by exact_mod_cast hPQ
  rw [hP] at hPQc
  have h2k : (2 : ℂ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [h2k] at hPQc
  have hne : (2 : ℂ) * 2 ^ (k - 1) ≠ 0 := mul_ne_zero two_ne_zero (pow_ne_zero _ two_ne_zero)
  apply mul_left_cancel₀ hne
  linear_combination hPQc

/-- The quadratic period at `d₂ = 1` is the plain class sum (`χ_{n,1} = 1`). -/
theorem quadPeriod_one {n : ℕ} [NeZero n] (τ : QNeg n →ₐ[ℚ] ℍ[ℚ]) (f : ℍ[AQ] → ℤ) :
    quadPeriod n τ f 1 =
      ∑ t : ClassGroup (𝓞 (QNeg n)), f ((tauHatU n τ (clLift n t) : ℍ[AQ]ˣ) : ℍ[AQ]) := by
  classical
  unfold quadPeriod
  have hT : divSet n 1 = ∅ := by
    ext ⟨q, hq⟩
    simp only [ZInQ.Contrib.TYZGenus.TYZ35.divSet, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.notMem_empty, iff_false, Nat.dvd_one]
    exact (Nat.prime_of_mem_primeFactors hq).one_lt.ne'
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [hT]
  simp [ZInQ.Contrib.TYZGenus.TYZ35.gchar]

theorem eq_one_or_neg_one_of_sq {a : ℂ} (h : a ^ 2 = 1) : a = 1 ∨ a = -1 := by
  rw [sq] at h; exact mul_self_eq_one_iff.mp h

/-- **TYZ Theorem 1.1 (integrality, `h11`) from TYZ Theorem 2.1 and `𝓛(1)² = 1`.** -/
theorem tyzThm11Integral_of_thm21C (h21 : TYZThm21PairsC) (hL1 : TYZLcalOne) : TYZThm11Integral := by
  let ℓ : ℕ → ℂ := fun m => lcalSq m ^ ((2 : ℕ)⁻¹ : ℂ)
  have hℓ : IsLcalSignC ℓ := fun m _ _ => Complex.cpow_nat_inv_pow _ two_ne_zero
  have hτe := tyzTauExists_of_legendreJonesPall (legendreJonesPall_of
    ZInQ.Contrib.OneProof.LegendreThreeSquares.legendreThreeSquares_proof
    ZInQ.Contrib.OneProof.JonesPall.jonesPall_proof)
  have hfx := ZInQ.Contrib.HfxProof.tyzTestVectorExists
  have h1 : ℓ 1 = 1 ∨ ℓ 1 = -1 :=
    eq_one_or_neg_one_of_sq ((hℓ 1 squarefree_one (Or.inl rfl)).trans hL1)
  have h1sq : ℓ 1 * ℓ 1 = 1 := by rcases h1 with h | h <;> rw [h] <;> norm_num
  have key : ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ∃ z : ℤ, ℓ m = z := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro hsq hcl
    by_cases hm1 : m = 1
    · subst hm1
      rcases h1 with h | h
      · exact ⟨1, by rw [h]; norm_num⟩
      · exact ⟨-1, by rw [h]; norm_num⟩
    have hm0 : m ≠ 0 := hsq.ne_zero
    have h1m : 1 < m := by omega
    have : NeZero m := ⟨hm0⟩
    obtain ⟨τ, hτ⟩ := hτe m hsq hcl
    obtain ⟨f, hf, -⟩ := hfx m hsq h1m hcl τ hτ
    by_cases hm3 : m = 3
    · subst hm3
      obtain ⟨-, hB⟩ := h21 3 hsq h1m hcl τ hτ f hf ℓ hℓ 3 1 rfl
      obtain ⟨ε, hε, heq⟩ := hB rfl
      rw [quadPeriod_one, ZInQ.Contrib.T21Proof.classSum_eq hf.1,
        ZInQ.Contrib.T21Proof.torsionOrder_three] at heq
      have hp : (3 : ℕ).primeFactors.card = 1 := by
        rw [Nat.Prime.primeFactors Nat.prime_three, Finset.card_singleton]
      rw [hp] at heq
      have hεsq : (ε : ℂ) ^ 2 = 1 := by rcases hε with rfl | rfl <;> norm_num
      have hX : ℓ 3 * ℓ 1 = (ε : ℂ) * ((f 1 : ℤ) : ℂ) / 3 := by
        linear_combination (-(ε : ℂ) / 3) * heq + (-(ℓ 3 * ℓ 1)) * hεsq
      have h31 : ℓ 3 * ℓ 1 = 1 ∨ ℓ 3 * ℓ 1 = -1 := by
        rw [hX]
        rcases ZInQ.Contrib.T21Proof.testVector_one hτ hf with hv | hv <;> rw [hv] <;>
          rcases hε with rfl | rfl <;> norm_num
      have e3 : ℓ 3 = (ℓ 3 * ℓ 1) * ℓ 1 := by rw [mul_assoc, h1sq, mul_one]
      rcases h31 with h | h <;> rcases h1 with h' | h'
      · exact ⟨1, by rw [e3, h, h']; norm_num⟩
      · exact ⟨-1, by rw [e3, h, h']; norm_num⟩
      · exact ⟨-1, by rw [e3, h, h']; norm_num⟩
      · exact ⟨1, by rw [e3, h, h']; norm_num⟩
    obtain ⟨ε, hε, heq⟩ := lemma29_coreC h21 hsq h1m hcl hτ hf hℓ
    rw [torsionOrder_qNeg_eq_two hsq h1m hm3] at heq
    norm_num at heq
    rw [← Finset.add_sum_erase _ _ (ZInQ.Contrib.TYZDecomp.H11Reduce.one_mem_pairIdx hm0 h1m)] at heq
    obtain ⟨S, hS⟩ : ∃ S : ℤ,
        ∑ d ∈ (pairIdx m).erase 1, (ε d : ℂ) * (ℓ (m / d) * ℓ d) = S := by
      classical
      have hint : ∀ d ∈ (pairIdx m).erase 1, ∃ z : ℤ, (ε d : ℂ) * (ℓ (m / d) * ℓ d) = z := by
        intro d hd
        rw [Finset.mem_erase] at hd
        obtain ⟨hd1, hd⟩ := hd
        simp only [pairIdx, Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨hdm, -⟩, hd8, hdd⟩ := hd
        have hd0 : d ≠ 0 := by rintro rfl; simp at hd8
        have hdle : d ≤ m := Nat.le_of_dvd (by omega) hdm
        have hdlt : d < m := by
          rcases hcl with h | h
          · have := hdd h
            nlinarith
          · rcases hdle.lt_or_eq with h' | h'
            · exact h'
            · omega
        have hqlt : m / d < m := Nat.div_lt_self (by omega) (by omega)
        have hq8 : m / d % 8 = m % 8 := by
          apply mod8_eq_of_dvd (Nat.div_dvd_of_dvd hdm)
          rw [Nat.div_div_self hdm hm0]; exact hd8
        obtain ⟨z₁, h₁⟩ := ih d hdlt (hsq.squarefree_of_dvd hdm) (Or.inl hd8)
        obtain ⟨z₂, h₂⟩ := ih (m / d) hqlt (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hdm))
          (by omega)
        exact ⟨ε d * (z₂ * z₁), by rw [h₁, h₂]; push_cast; ring⟩
      revert hint
      refine Finset.induction_on ((pairIdx m).erase 1) (fun _ => ⟨0, by simp⟩) ?_
      intro a s ha ihs h
      obtain ⟨z₁, h₁⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨z₂, h₂⟩ := ihs fun d hd => h d (Finset.mem_insert_of_mem hd)
      exact ⟨z₁ + z₂, by rw [Finset.sum_insert ha, h₁, h₂]; push_cast; ring⟩
    rw [Nat.div_one, hS] at heq
    have em : ℓ m = (ℓ m * ℓ 1) * ℓ 1 := by rw [mul_assoc, h1sq, mul_one]
    have hm1' : ℓ m * ℓ 1 = (ε 1 : ℂ) * ((genusPeriodTV m τ f : ℂ) - S) := by
      rcases hε 1 with h | h <;> rw [h] at heq ⊢ <;> push_cast at heq ⊢
      · linear_combination heq
      · linear_combination -heq
    rcases h1 with h' | h'
    · exact ⟨ε 1 * (genusPeriodTV m τ f - S), by rw [em, hm1', h']; push_cast; ring⟩
    · exact ⟨-(ε 1 * (genusPeriodTV m τ f - S)), by rw [em, hm1', h']; push_cast; ring⟩
  intro m hsq hcl
  obtain ⟨z, hz⟩ := key m hsq hcl
  exact ⟨z, by rw [← hz]; exact hℓ m hsq hcl⟩

/-- **`hL29` from the complex form of TYZ Theorem 2.1** (through the integer form). -/
theorem tyzLemma29PrintedNe3_of_thm21C (h21 : TYZThm21PairsC) : TYZLemma29PrintedNe3 :=
  tyzLemma29PrintedNe3_of_thm21Pairs (tyzThm21Pairs_of_C h21)

end ZInQ.Contrib.TYZGenusFold
