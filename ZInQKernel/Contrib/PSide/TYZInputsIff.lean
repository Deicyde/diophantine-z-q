import ZInQKernel.RouteK.PropN

/-!
# P5: `TYZInputs` is equivalent to reading A of TYZ Theorem 3.5(2)

`PropN.TYZInputs` (`ZInQKernel/Hypotheses/TYZInputs.lean`) encodes the results of Tian–Yuan–Zhang
that Proposition N uses; `RouteK/PropN.lean` proves `tyzThm35ReadingA_of_tyzInputs`. This file
proves the converse assembly announced there (`rv-pn-encoding` F1, fix item 5):

* `tyzInputs_iff`: `TYZInputs` holds iff every squarefree `n ≡ 5 (mod 8)` has a continuation of
  `L(C_n, s)` of order at most `1` at `s = 1`, or both genus sums `T5aCl n`, `T5bCl n` vanish;
* `tyzInputs_iff_readingA`: `TYZInputs ↔ TYZThm35ReadingA ∧ ∀ n, (∃ continuation) ∨ (T5a = T5b = 0)`
  (no hypothesis);
* `tyzInputs_iff_readingA_of_hecke`: under Hecke's continuation (`HeckeContinuation`),
  `TYZInputs ↔ TYZThm35ReadingA`; and `tyzInputs_of_readingA`.

The backward direction chooses `L m = Λ(m)` (the parity function `Lam`, lifted to `{0, 1}`) on the
classes `1, 3 (mod 8)`, `L m = 1` or `0` on the class `5` according to whether a continuation of
order `≤ 1` exists, and `L m = 0` otherwise. `L 1 = 1` and `LemmaTwoEight L` follow from
`lemmaN1_core`; the genus data come from `Witness.genusData_nonempty` when `L n ≠ 0` and from
`Witness.genusData_nonempty_of_parities` (with `matching`) when `L n = 0`.

So `TYZInputs` is neither weaker nor stronger than reading A (given Hecke's continuation): the
encoding is not vacuous relative to reading A, and its trust rests on reading A itself.
-/

namespace ZInQ.Contrib.PSide

open ZInQ.Literature ZInQ.PropN ZInQ.RouteK.Rank5b

/-- The right-hand side of `tyzInputs_iff` at one `n`: a continuation of order at most one, or
both genus sums vanish. -/
def ReadingAAt (n : ℕ) : Prop :=
  (∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F ∧ analyticOrderAt F 1 ≤ 1) ∨
    (T5aCl n = 0 ∧ T5bCl n = 0)

/-- The parity sums of `finalStep`, for `L` agreeing with `Λ` modulo `2` on classes `1, 3`, are
the genus sums `T5aCl n`, `T5bCl n` (`matching`). -/
theorem parity_sums_eq {L : ℕ → ℤ} {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n)
    (hL : ∀ m : ℕ, Squarefree m → (m % 8 = 1 ∨ m % 8 = 3) → ((L m : ℤ) : ZMod 2) = Lam m) :
    (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 5), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2)) =
      T5aCl n ∧
    (((∑ e ∈ n.divisors.filter (fun e => e % 8 = 7), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2)) =
      T5bCl n := by
  obtain ⟨m5, m7⟩ := matching hn hsq
  have key : ∀ c : ℕ, (c = 5 ∨ c = 7) →
      (((∑ e ∈ n.divisors.filter (fun e => e % 8 = c), L (n / e) * (gNat e : ℤ) : ℤ) : ZMod 2)) =
      ∑ e ∈ n.divisors.filter (fun e => e % 8 = c), Lam (n / e) * (gNat e : ZMod 2) := by
    intro c hc
    push_cast
    refine Finset.sum_congr rfl fun e he => ?_
    simp only [Finset.mem_filter, Nat.mem_divisors] at he
    obtain ⟨⟨hen, -⟩, he8⟩ := he
    have hq : n / e % 8 = 1 ∨ n / e % 8 = 3 := by
      rw [div_mod8_of hen hn he8 (by omega)]; rcases hc with rfl | rfl <;> norm_num
    rw [hL (n / e) (hsq.squarefree_of_dvd (Nat.div_dvd_of_dvd hen)) hq]
  exact ⟨(key 5 (Or.inl rfl)).trans m5, (key 7 (Or.inr rfl)).trans m7⟩

/-- **`TYZInputs` in closed form** (`rv-pn-encoding` F1, item 5): the TYZ inputs of Proposition N
hold iff every squarefree `n ≡ 5 (mod 8)` has a continuation of `L(C_n, s)` of order at most one
at `s = 1`, or both genus sums `T_5a(n)`, `T_5b(n)` are even. -/
theorem tyzInputs_iff :
    TYZInputs ↔ ∀ n : ℕ, n % 8 = 5 → Squarefree n → ReadingAAt n := by
  constructor
  · rintro ⟨L, hL1, h28, hI7, hG⟩ n hn hsq
    by_cases hLn : L n = 0
    · obtain ⟨G⟩ := hG n hn hsq
      exact Or.inr (genusSums_eq_zero hL1 h28 hn hsq G hLn)
    · exact Or.inl (hI7 n hn hsq hLn)
  · intro H
    classical
    let C : ℕ → Prop := fun m =>
      ∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(m : ℚ) ^ 2)) F ∧ analyticOrderAt F 1 ≤ 1
    let L : ℕ → ℤ := fun m =>
      if m % 8 = 1 ∨ m % 8 = 3 then ((Lam m).val : ℤ) else if m % 8 = 5 ∧ C m then 1 else 0
    have hLam : ∀ m : ℕ, (m % 8 = 1 ∨ m % 8 = 3) → ((L m : ℤ) : ZMod 2) = Lam m := by
      intro m hm
      simp only [L, hm, ↓reduceIte, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hL5 : ∀ m : ℕ, m % 8 = 5 → L m = if C m then 1 else 0 := by
      intro m hm
      simp only [L, hm, true_and]
      norm_num
    obtain ⟨c1, c2, c3⟩ := lemmaN1_core
    have hL1 : L 1 = 1 := by
      simp only [L, Nat.one_mod, true_or, ↓reduceIte, c1, ZMod.val_one, Nat.cast_one]
    have h28 : LemmaTwoEight L := by
      constructor
      · intro m hsq hm1 hm
        rw [← c2 m hsq hm1 hm]
        push_cast
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨hdm, -⟩, hd8, -⟩ := hd
        have hq8 : m / d % 8 = 1 := by rw [div_mod8_of hdm hm hd8 (Or.inl rfl)]
        rw [hLam d (Or.inl hd8), hLam (m / d) (Or.inl hq8)]
      · intro m hsq hm
        rw [← c3 m hsq hm]
        push_cast
        refine Finset.sum_congr rfl fun d hd => ?_
        simp only [Finset.mem_filter, Nat.mem_divisors] at hd
        obtain ⟨⟨hdm, -⟩, hd8⟩ := hd
        have hq8 : m / d % 8 = 3 := by rw [div_mod8_of hdm hm hd8 (Or.inl rfl)]
        rw [hLam d (Or.inl hd8), hLam (m / d) (Or.inr hq8)]
    refine ⟨L, hL1, h28, fun n hn _ hLn => ?_, fun n hn hsq => ?_⟩
    · rw [hL5 n hn] at hLn
      by_contra hc
      exact hLn (by simp only [C] at *; simp [hc])
    · by_cases hc : C n
      · exact Witness.genusData_nonempty L n (by simp [hL5 n hn, hc])
      · have hLn : L n = 0 := by simp [hL5 n hn, hc]
        rcases H n hn hsq with h | ⟨ha, hb⟩
        · exact absurd h hc
        have hpar := parity_sums_eq hn hsq (L := L) fun m _ hm => hLam m hm
        exact Witness.genusData_nonempty_of_parities L n hn hsq hL1 hLn
          (hpar.1.trans ha) (hpar.2.trans hb)

/-- **`TYZInputs` is reading A plus "a continuation exists or the genus sums vanish"**, with no
hypothesis: `TYZInputs ↔ TYZThm35ReadingA ∧ ∀ n, (∃ continuation) ∨ (T5a = T5b = 0)`. -/
theorem tyzInputs_iff_readingA :
    TYZInputs ↔ TYZThm35ReadingA ∧ ∀ n : ℕ, n % 8 = 5 → Squarefree n →
      (∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F) ∨
        (T5aCl n = 0 ∧ T5bCl n = 0) := by
  rw [tyzInputs_iff]
  constructor
  · intro H
    refine ⟨fun d hd hsq F hF h2 => ?_, fun n hn hsq => ?_⟩
    · rcases H d hd hsq with ⟨G, hG, hle⟩ | h
      · rw [hG.eq hF] at hle
        exact absurd (hle.trans_lt (by norm_num)) (not_lt.mpr h2)
      · exact h
    · rcases H n hn hsq with ⟨G, hG, -⟩ | h
      · exact Or.inl ⟨G, hG⟩
      · exact Or.inr h
  · rintro ⟨hA, hE⟩ n hn hsq
    rcases hE n hn hsq with ⟨F, hF⟩ | h
    · by_cases hle : analyticOrderAt F 1 ≤ 1
      · exact Or.inl ⟨F, hF, hle⟩
      · exact Or.inr (hA n hn hsq F hF (two_le_of_not_le_one hle))
    · exact Or.inr h

/-- **Under Hecke's continuation, `TYZInputs` is exactly reading A of TYZ Theorem 3.5(2).** -/
theorem tyzInputs_iff_readingA_of_hecke (hH : HeckeContinuation) :
    TYZInputs ↔ TYZThm35ReadingA := by
  rw [tyzInputs_iff_readingA]
  exact ⟨fun h => h.1, fun hA => ⟨hA, fun n hn _ => Or.inl (hH n (by omega))⟩⟩

/-- `TYZInputs` from reading A and Hecke's continuation (`rv-pn-encoding` F1, item 6). -/
theorem tyzInputs_of_readingA (hA : TYZThm35ReadingA) (hH : HeckeContinuation) : TYZInputs :=
  (tyzInputs_iff_readingA_of_hecke hH).mpr hA

end ZInQ.Contrib.PSide
