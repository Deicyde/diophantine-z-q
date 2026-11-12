import ZInQKernel.Compiler.Precision.HeightConstant

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt from
`scratch/glue-descent/Constants.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-descent: the constants of B2-B3 (N5 L674-677, L711-716)

Against the repository's own definitions (`ZInQKernel/Hypotheses/Height.lean`): `heightD = D`,
`heightE0 = E₀`, `heightQ R = Q_R = R^{R E₀}`, `contactSupport S u = M_S(u)`.

* `prod_odd_le`: `∏_{p ∈ T, p ≠ 2} (p - 1) ≤ R^R · M` for `T = S ∪ supp M`
  (N5 L676: `m ≤ 2 ∏_{p∈T, p≠2}(p-1) ≤ 2R^R M`);
* `degree_le_QM`: if `d ≤ D` and `m ≤ 2 ∏_{p ∈ T, p ≠ 2}(p-1)` then `2md ≤ Q_R · M`
  (N5 L713-716: `[L':ℚ] ≤ 2md ≤ 4DR^RM ≤ QM`).

The huge constants are never evaluated: only `1 ≤ D ≤ R`, `10¹² ≤ R` and `10 ≤ E₀` are used.
-/

namespace GlueDescent

open ZInQ

/-- `T = S ∪ supp M_S(u)`, the ramification set of `L` (N5 L528). -/
noncomputable def ramSet (S : Finset ℕ) (u : ℚ) : Finset ℕ :=
  S ∪ (contactSupport S u).primeFactors

theorem contactSupport_pos (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  apply Finset.prod_pos
  intro p hp
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

theorem heightD_pos : 0 < heightD := by
  rw [ZInQ.Compiler.Precision.heightD_eq]
  exact Nat.mul_pos (Nat.factorial_pos 324) (by positivity)

theorem ten_le_heightE0 : 10 ≤ heightE0 := by
  rw [ZInQ.Compiler.Precision.heightE0_eq]
  have h1 : 0 < heightD * heightG0 := Nat.mul_pos heightD_pos (by unfold heightG0; norm_num)
  exact Nat.le_mul_of_pos_right 10 (pow_pos h1 2)

/-- `∏_{p ∈ S} (p - 1) ≤ R^R` when `S` consists of primes `≤ R` and `R ≥ 1`. -/
theorem prod_S_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ) (hR1 : 1 ≤ R)
    (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) : ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) ≤ R ^ R := by
  have hcard : (S.card : ℝ) ≤ R := by
    have hsub : S ⊆ Finset.Icc 1 ⌊R⌋₊ := by
      intro p hp
      rw [Finset.mem_Icc]
      exact ⟨(hS p hp).one_lt.le, Nat.le_floor (hRS p hp)⟩
    have := Finset.card_le_card hsub
    rw [Nat.card_Icc, Nat.add_sub_cancel] at this
    calc (S.card : ℝ) ≤ ⌊R⌋₊ := by exact_mod_cast this
      _ ≤ R := Nat.floor_le (by linarith)
  calc ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) = ∏ p ∈ S, (((p - 1 : ℕ)) : ℝ) := by
          push_cast [Nat.cast_prod]; rfl
    _ ≤ ∏ _p ∈ S, R := by
        apply Finset.prod_le_prod₀ (fun _ _ => by positivity)
        intro p hp
        have := hRS p hp
        have h1 : ((p - 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
        linarith
    _ = R ^ S.card := Finset.prod_const R
    _ = R ^ (S.card : ℝ) := (Real.rpow_natCast R S.card).symm
    _ ≤ R ^ R := Real.rpow_le_rpow_of_exponent_le hR1 hcard

/-- Auxiliary form of `prod_odd_le` for an arbitrary positive `M`. -/
theorem prod_odd_le_aux (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ) (hR1 : 1 ≤ R)
    (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (M : ℕ) (hM : 0 < M) :
    ((∏ p ∈ (S ∪ M.primeFactors).filter (· ≠ 2), (p - 1) : ℕ) : ℝ) ≤ R ^ R * M := by
  -- drop the filter: the factors are ≥ 1 on primes
  have hT : ∀ p ∈ S ∪ M.primeFactors, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  have h1 : (∏ p ∈ (S ∪ M.primeFactors).filter (· ≠ 2), (p - 1)) ≤ ∏ p ∈ S ∪ M.primeFactors, (p - 1)
      := by
    apply Finset.prod_le_prod_of_subset_of_one_le (Finset.filter_subset _ _)
    intro p hp _
    have := (hT p hp).two_le
    omega
  -- union bound
  have h2 : (∏ p ∈ S ∪ M.primeFactors, (p - 1)) ≤
      (∏ p ∈ S, (p - 1)) * ∏ p ∈ M.primeFactors, (p - 1) := by
    rw [← Finset.prod_union_inter]
    apply Nat.le_mul_of_pos_right
    apply Finset.prod_pos
    intro p hp
    have := (hS p (Finset.mem_inter.mp hp).1).two_le
    omega
  have h3 : (∏ p ∈ M.primeFactors, (p - 1)) ≤ M :=
    calc (∏ p ∈ M.primeFactors, (p - 1)) ≤ ∏ p ∈ M.primeFactors, p :=
          Finset.prod_le_prod (fun p _ => Nat.sub_le p 1)
      _ ≤ M := Nat.le_of_dvd hM (Nat.prod_primeFactors_dvd M)
  have hS' := prod_S_le S hS R hR1 hRS
  have hall : (∏ p ∈ (S ∪ M.primeFactors).filter (· ≠ 2), (p - 1)) ≤
      (∏ p ∈ S, (p - 1)) * M := le_trans h1 (le_trans h2 (Nat.mul_le_mul_left _ h3))
  calc ((∏ p ∈ (S ∪ M.primeFactors).filter (· ≠ 2), (p - 1) : ℕ) : ℝ)
      ≤ (((∏ p ∈ S, (p - 1)) * M : ℕ) : ℝ) := by exact_mod_cast hall
    _ = ((∏ p ∈ S, (p - 1) : ℕ) : ℝ) * M := by push_cast; ring
    _ ≤ R ^ R * M := by
        apply mul_le_mul_of_nonneg_right hS' (by positivity)

/-- **B2's order bound, arithmetic part** (N5 L676): `∏_{p ∈ T, p ≠ 2} (p - 1) ≤ R^R · M`. -/
theorem prod_odd_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ) (hR1 : 1 ≤ R)
    (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (u : ℚ) :
    ((∏ p ∈ (ramSet S u).filter (· ≠ 2), (p - 1) : ℕ) : ℝ) ≤ R ^ R * contactSupport S u :=
  prod_odd_le_aux S hS R hR1 hRS _ (contactSupport_pos S u)

/-- **B3, `[L':ℚ] ≤ QM`** (N5 L711-716). For an admissible `(S, R)` (the hypotheses of
`SixContactEstimate`), `d ≤ D` and `m ≤ 2 ∏_{p ∈ T, p ≠ 2}(p - 1)`, one has
`2 m d ≤ Q_R · M_S(u)`. -/
theorem degree_le_QM (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ) (hRD : (heightD : ℝ) ≤ R)
    (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R) (u : ℚ) (d m : ℕ)
    (hd : d ≤ heightD) (hm : m ≤ 2 * ∏ p ∈ (ramSet S u).filter (· ≠ 2), (p - 1)) :
    (2 * m * d : ℝ) ≤ heightQ R * contactSupport S u := by
  have hR4 : (4 : ℝ) ≤ R := le_trans (by norm_num) hR12
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hR0 : (0 : ℝ) < R := by linarith
  have hP := prod_odd_le S hS R hR1 hRS u
  have hM : (0 : ℝ) ≤ (contactSupport S u : ℝ) := Nat.cast_nonneg _
  generalize (contactSupport S u : ℝ) = M at hP hM ⊢
  have hm' : (m : ℝ) ≤ 2 * (R ^ R * M) := by
    have : (m : ℝ) ≤ 2 * ((∏ p ∈ (ramSet S u).filter (· ≠ 2), (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast hm
    linarith
  have hd' : (d : ℝ) ≤ R := le_trans (by exact_mod_cast hd) hRD
  have hRR : (0 : ℝ) ≤ R ^ R := by positivity
  -- 2 m d ≤ 4 R^R M R ≤ R^R R^2 M = R^(R+2) M
  have step1 : (2 * m * d : ℝ) ≤ R ^ (R + 2) * M := by
    have hmd : (m : ℝ) * d ≤ 2 * (R ^ R * M) * R :=
      mul_le_mul hm' hd' (by positivity) (by positivity)
    rw [Real.rpow_add hR0, show (R ^ (2 : ℝ)) = R ^ 2 by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]]
    have h4R : 4 * R ≤ R * R := mul_le_mul_of_nonneg_right hR4 hR0.le
    have hX : (0 : ℝ) ≤ R ^ R * M := mul_nonneg hRR hM
    calc (2 * m * d : ℝ) = 2 * ((m : ℝ) * d) := by ring
      _ ≤ 2 * (2 * (R ^ R * M) * R) := by linarith
      _ = (R ^ R * M) * (4 * R) := by ring
      _ ≤ (R ^ R * M) * (R * R) := mul_le_mul_of_nonneg_left h4R hX
      _ = R ^ R * R ^ 2 * M := by ring
  -- R + 2 ≤ R E₀
  have hE : (10 : ℝ) ≤ heightE0 := by exact_mod_cast ten_le_heightE0
  have step2 : R ^ (R + 2) ≤ heightQ R := by
    unfold heightQ
    apply Real.rpow_le_rpow_of_exponent_le hR1
    generalize (heightE0 : ℝ) = E at hE ⊢
    have : R * 10 ≤ R * E := mul_le_mul_of_nonneg_left hE hR0.le
    linarith
  calc (2 * m * d : ℝ) ≤ R ^ (R + 2) * M := step1
    _ ≤ heightQ R * M := mul_le_mul_of_nonneg_right step2 hM

end GlueDescent
