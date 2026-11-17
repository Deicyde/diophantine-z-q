import ZInQKernel.Contrib.OneProof.RC.KSplit.Coefficients

/-!
# Lane RC3: the no-seed trace interface is satisfiable (non-vacuity of `NoSeedTraceData`)

`NoSeedTraceData O p a_p` (`Coefficients.lean`) bundles the `ELLIOT`/`PRINT` inputs of Elliot's
App G calculation at one prime (tex 10319–10481). Its theorem `NoSeedTraceData.cong_eight` says
these inputs force `a_p ≡ p + 1 (mod 8)`. To show that the interface is not vacuous (its fields
are not jointly contradictory), this file builds an instance at `p = 5`, `a_p = 6 = p + 1` over the
coefficient ring `ℤ ⊂ ℚ`:

* the `q`-expansion `a(5^{2r}) = 5^r`, `a(n) = 0` for every other `n` (this is the shell sequence
  `b_r` of `(E.12)` with `a_p = p + 1`, supported on the powers `p^{2r}`), with `η = 1`,
  `ψ(5) = (−1/5) = 1`, support `S = 1`;
* `H` is integral, `(G.4a)`, `(G.4b)` and `a(pp') = 0 ∈ 8𝒪` hold, `d(φ)` acts by `1` on the three
  blocks, `t(φ)f` is given by the trace identity, and the good Hecke formula at `p' = 2` holds.

`noSeedTraceData_example` is the instance (`PROVED`); `cong_eight` then returns the true
congruence `8 ∣ 6 − 5 − 1`. The instance witnesses only that the interface's conditions on
`q`-expansions are jointly satisfiable; it is not asserted to be the expansion of an actual
half-integral-weight form.
-/

namespace ZInQ.Manuscript.RC.KSplit

open Finset

/-- `5` is prime. -/
theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨by norm_num⟩

attribute [local instance] fact_prime_five

/-! ### The sequence `a(5^{2r}) = 5^r` -/

/-- `a(n) = 5^r` if `n = 5^{2r}`, and `0` otherwise. -/
noncomputable def toyA (n : ℕ) : ℚ := by
  classical
  exact if h : ∃ r, n = 5 ^ (2 * r) then (5 : ℚ) ^ (Nat.find h) else 0

theorem pow_five_injective : Function.Injective (fun r : ℕ => 5 ^ r) :=
  Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num))

theorem toyA_pow (r : ℕ) : toyA (5 ^ (2 * r)) = 5 ^ r := by
  classical
  have h : ∃ s, 5 ^ (2 * r) = 5 ^ (2 * s) := ⟨r, rfl⟩
  unfold toyA
  rw [dite_eq_left h]
  have hs := Nat.find_spec h
  have : 2 * r = 2 * Nat.find h := pow_five_injective hs
  rw [show Nat.find h = r by omega]

theorem toyA_of_not {n : ℕ} (h : ¬ ∃ r, n = 5 ^ (2 * r)) : toyA n = 0 := by
  classical
  unfold toyA
  rw [dite_eq_right h]

theorem toyA_five_mul_odd (s : ℕ) : toyA (5 * 5 ^ (2 * s + 1)) = 5 ^ (s + 1) := by
  rw [show 5 * 5 ^ (2 * s + 1) = 5 ^ (2 * (s + 1)) by ring, toyA_pow]

/-- `n = 5^{2r}` is not of the form `5^{2s+1}`. -/
theorem even_ne_odd_pow (r s : ℕ) : 5 ^ (2 * r) ≠ 5 ^ (2 * s + 1) := fun h => by
  have : 2 * r = 2 * s + 1 := pow_five_injective h
  omega

/-! ### The recurrence `(E.12)` at `p = 5` -/

theorem legendreSym_five_neg_one : legendreSym 5 (-1) = 1 := by
  rw [legendreSym.at_neg_one (by norm_num)]
  exact ZMod.χ₄_nat_one_mod_four (by norm_num)

theorem toyA_one : toyA 1 = 1 := by simpa using toyA_pow 0

theorem toy_shellRecurrence : ShellRecurrence toyA 1 1 6 5 := by
  intro n
  classical
  by_cases hA : ∃ r, n = 5 ^ (2 * r)
  · obtain ⟨r, rfl⟩ := hA
    rcases r with _ | r
    · -- `n = 1`
      simp only [Nat.mul_zero, pow_zero, Nat.cast_one]
      rw [show (5 : ℕ) ^ 2 * 1 = 5 ^ (2 * 1) by norm_num, toyA_pow, toyA_one,
        legendreSym_five_neg_one]
      have : ¬ (5 : ℕ) ^ 2 ∣ 1 := by norm_num
      rw [ite_eq_right this]
      norm_num
    · -- `n = 5^{2(r+1)}`
      have hleg : legendreSym 5 (-((5 ^ (2 * (r + 1)) : ℕ) : ℤ)) = 0 := by
        have h5 : (5 : ZMod 5) = 0 := rfl
        rw [legendreSym.eq_zero_iff]; push_cast
        rw [show (2 * (r + 1)) = (2 * r + 1) + 1 by ring, pow_succ, h5]; simp
      have hdvd : (5 : ℕ) ^ 2 ∣ 5 ^ (2 * (r + 1)) := pow_dvd_pow 5 (by omega)
      rw [hleg, ite_eq_left hdvd,
        show 5 ^ (2 * (r + 1)) / 5 ^ 2 = 5 ^ (2 * r) by
          rw [show 2 * (r + 1) = 2 + 2 * r by ring, pow_add,
            Nat.mul_div_cancel_left _ (by norm_num)],
        show (5 : ℕ) ^ 2 * 5 ^ (2 * (r + 1)) = 5 ^ (2 * (r + 2)) by ring,
        toyA_pow, toyA_pow, toyA_pow]
      push_cast; ring
  · -- `n` is not an even power of `5`: all three terms vanish
    have h1 : ¬ ∃ s, (5 : ℕ) ^ 2 * n = 5 ^ (2 * s) := by
      rintro ⟨s, hs⟩
      rcases s with _ | s
      · have : (5 : ℕ) ^ 2 * n ≠ 1 := by
          intro h; have := Nat.eq_one_of_mul_eq_one_right h; norm_num at this
        exact this (by rw [hs]; simp)
      · apply hA
        refine ⟨s, ?_⟩
        have : (5 : ℕ) ^ 2 * n = 5 ^ 2 * 5 ^ (2 * s) := by rw [hs]; ring
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    rw [toyA_of_not h1, toyA_of_not hA]
    by_cases hd : (5 : ℕ) ^ 2 ∣ n
    · rw [ite_eq_left hd]
      have h2 : ¬ ∃ s, n / 5 ^ 2 = 5 ^ (2 * s) := by
        rintro ⟨s, hs⟩
        apply hA
        refine ⟨s + 1, ?_⟩
        rw [← Nat.mul_div_cancel' hd, hs]; ring
      rw [toyA_of_not h2]; ring
    · rw [ite_eq_right hd]; ring

/-! ### `B`, `H` and their integrality -/

/-- `B[n] = 2 · 5^s` at `n = 5^{2s+1}` and `0` otherwise. -/
theorem toyB_odd (s : ℕ) : Bp toyA 1 5 (5 ^ (2 * s + 1)) = 2 * 5 ^ s := by
  unfold Bp
  rw [toyA_five_mul_odd, ite_eq_left (dvd_pow_self 5 (by omega)),
    show 5 ^ (2 * s + 1) / 5 = 5 ^ (2 * s) by rw [pow_succ, Nat.mul_div_cancel _ (by norm_num)],
    toyA_pow]
  ring

theorem toyB_of_not {n : ℕ} (h : ¬ ∃ s, n = 5 ^ (2 * s + 1)) : Bp toyA 1 5 n = 0 := by
  unfold Bp
  have h1 : ¬ ∃ r, 5 * n = 5 ^ (2 * r) := by
    rintro ⟨r, hr⟩
    rcases r with _ | r
    · have : 5 * n ≠ 1 := by
        intro h'; have := Nat.eq_one_of_mul_eq_one_right h'; norm_num at this
      exact this (by rw [hr]; simp)
    · apply h
      refine ⟨r, ?_⟩
      have : 5 * n = 5 * 5 ^ (2 * r + 1) := by rw [hr]; ring
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
  rw [toyA_of_not h1]
  by_cases hd : 5 ∣ n
  · rw [ite_eq_left hd]
    have h2 : ¬ ∃ r, n / 5 = 5 ^ (2 * r) := by
      rintro ⟨r, hr⟩
      apply h
      exact ⟨r, by rw [← Nat.mul_div_cancel' hd, hr]; ring⟩
    rw [toyA_of_not h2]; ring
  · rw [ite_eq_right hd]; ring

theorem toyB_one : Bp toyA 1 5 1 = 0 :=
  toyB_of_not fun ⟨s, hs⟩ => by
    have : 1 < 5 ^ (2 * s + 1) := Nat.one_lt_pow (by omega) (by norm_num)
    omega

theorem toyB_five : Bp toyA 1 5 5 = 2 := by
  have := toyB_odd 0
  simpa using this

/-- The coefficient ring `ℤ ⊂ ℚ`. -/
abbrev toyO : Subring ℚ := ⊥

theorem mem_toyO_intCast (z : ℤ) : (z : ℚ) ∈ toyO := intCast_mem _ z

theorem toyB_half_mem (n : ℕ) : Bp toyA 1 5 n / 2 ∈ toyO := by
  classical
  by_cases h : ∃ s, n = 5 ^ (2 * s + 1)
  · obtain ⟨s, rfl⟩ := h
    rw [toyB_odd, show (2 : ℚ) * 5 ^ s / 2 = ((5 ^ s : ℤ) : ℚ) by push_cast; ring]
    exact mem_toyO_intCast _
  · rw [toyB_of_not h, zero_div]; exact toyO.zero_mem

theorem toyH_eq (n : ℕ) : Hp toyA (fun _ => 1) 1 5 n =
    Bp toyA 1 5 n / 2 - unaryTheta (fun _ => (1 : ℚ)) 1 5 n := by
  unfold Hp
  rw [toyB_one, toyB_five]
  ring

theorem toyH_mem (n : ℕ) : Hp toyA (fun _ => 1) 1 5 n ∈ toyO := by
  rw [toyH_eq]
  exact toyO.sub_mem (toyB_half_mem n) (unaryTheta_mem (fun _ => toyO.one_mem) 1 5 n)

theorem two_inv_not_mem_toyO : (2 : ℚ)⁻¹ ∉ toyO := by
  rintro ⟨z, hz⟩
  have h : (2 : ℚ) * z = 1 := by
    simp only [Int.coe_castRingHom] at hz
    rw [hz]; norm_num
  have : (2 * z : ℤ) = 1 := by exact_mod_cast h
  omega

/-! ### The instance -/

/-- **The no-seed trace interface is satisfiable** (`PROVED`): an instance of
`NoSeedTraceData` at `p = 5`, `a_p = 6`, over `ℤ ⊂ ℚ`. -/
noncomputable def noSeedTraceData_example : NoSeedTraceData toyO 5 6 := by
  let η : ℕ → ℚ := fun _ => 1
  let B := Bp toyA (η 5) 5
  let df : ℕ → ℚ := fun n => (1 * thetaMul B n - 1 * B 1 * thetaMul (unaryTheta η 1 1) n -
    1 * B 5 * thetaMul (unaryTheta η 1 5) n) / 2
  have hrec : ShellRecurrence toyA (η 5) ((legendreSym 5 (-1) : ℤ) : ℚ) 6 5 := by
    rw [legendreSym_five_neg_one]; exact toy_shellRecurrence
  have hψ : ((legendreSym 5 (-1) : ℤ) : ℚ) = η 5 * ((legendreSym 5 (-1) : ℤ) : ℚ) := by
    simp [η]
  have hH : ∀ n, Hp toyA η 1 5 n ∈ toyO := toyH_mem
  have hdf : DphiBlocks df toyA η 1 5 1 1 1 := fun n => rfl
  have hG4a : InTwoO toyO (Bp toyA (η 5) 5 1) := by
    rw [show Bp toyA (η 5) 5 1 = 0 from toyB_one]; exact InTwoO.zero
  have hG4b : ∀ j ∈ Icc 1 (Nat.sqrt 5), InTwoO toyO (Bp toyA (η 5) 5 (5 - j ^ 2)) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hj2 : j ^ 2 ≤ 5 := by have := Nat.le_sqrt.mp hj.2; rwa [sq]
    have hnot : ¬ ∃ s, 5 - j ^ 2 = 5 ^ (2 * s + 1) := by
      rintro ⟨s, hs⟩
      have h5 : 5 ≤ 5 ^ (2 * s + 1) := Nat.le_self_pow (by omega) 5
      have : 0 < j ^ 2 := pow_pos (by omega) 2
      omega
    rw [show Bp toyA (η 5) 5 (5 - j ^ 2) = 0 from toyB_of_not hnot]; exact InTwoO.zero
  have hdfp : InTwoO toyO (df 5) :=
    dphi_p_inTwoO_of_G4ab fact_prime_five.out rfl (fun _ => toyO.one_mem) hdf toyO.one_mem
      toyO.one_mem rfl hG4a hG4b
  have hH3 : Hp toyA η 1 5 (5 ^ 3) = 0 := by
    rw [Hp_p_cube hrec toyA_one hψ (by norm_num)]; norm_num
  have hH2 : Hp toyA η 1 5 (5 ^ 2 * 2) = 0 := by
    rw [Hp_p_sq_mul hrec Nat.prime_two (by norm_num)]
    have : ¬ ∃ r, 5 * 2 = 5 ^ (2 * r) := by
      rintro ⟨r, hr⟩
      rcases r with _ | r
      · norm_num at hr
      · have : 5 ^ 2 ≤ 5 ^ (2 * (r + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    rw [toyA_of_not this]; ring
  have hHecke : InTwoO toyO ((thetaMul (Hp toyA η 1 5) (5 ^ 3) + df 5) -
      thetaMul (Hp toyA η 1 5) (5 ^ 2 * 2)) := by
    have e : (thetaMul (Hp toyA η 1 5) (5 ^ 3) + df 5) - thetaMul (Hp toyA η 1 5) (5 ^ 2 * 2) =
        (thetaMul (Hp toyA η 1 5) (5 ^ 3) - Hp toyA η 1 5 (5 ^ 3)) + df 5 -
          (thetaMul (Hp toyA η 1 5) (5 ^ 2 * 2) - Hp toyA η 1 5 (5 ^ 2 * 2)) := by
      rw [hH3, hH2]; ring
    rw [e]
    exact ((thetaMul_sub_self_inTwoO hH _).add hdfp).sub (thetaMul_sub_self_inTwoO hH _)
  have hpp' : ∃ y ∈ toyO, toyA (5 * 2) = 8 * y := by
    refine ⟨0, toyO.zero_mem, ?_⟩
    have : ¬ ∃ r, 5 * 2 = 5 ^ (2 * r) := by
      rintro ⟨r, hr⟩
      rcases r with _ | r
      · norm_num at hr
      · have : 5 ^ 2 ≤ 5 ^ (2 * (r + 1)) := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
    rw [toyA_of_not this]; ring
  exact {
    a := toyA
    η := η
    ψp := ((legendreSym 5 (-1) : ℤ) : ℚ)
    S := 1
    ha1 := toyA_one
    hrec := hrec
    hψ := hψ
    hη1 := rfl
    hηO := fun _ => toyO.one_mem
    hηinv := by simp [η]
    hη0 := one_ne_zero
    hpS := Nat.coprime_one_right 5
    hhalf := two_inv_not_mem_toyO
    hH := hH
    p' := 2
    hp' := Nat.prime_two
    hp'p := by norm_num
    tf := fun _ => thetaMul (Hp toyA η 1 5) (5 ^ 3) + df 5
    df := df
    htrace := rfl
    hHecke := hHecke
    δB := 1
    δ1 := 1
    δp := 1
    hδB := toyO.one_mem
    hδ1 := toyO.one_mem
    hδBp := rfl
    hdf := hdf
    hG4a := hG4a
    hG4b := hG4b
    hpp' := hpp' }

/-- The instance's conclusion is the true congruence `8 ∣ 6 − 5 − 1` (`PROVED`). -/
theorem noSeedTraceData_example_cong : (8 : ℤ) ∣ 6 - (5 : ℕ) - 1 :=
  noSeedTraceData_example.cong_eight (by norm_num) (by norm_num)

end ZInQ.Manuscript.RC.KSplit
