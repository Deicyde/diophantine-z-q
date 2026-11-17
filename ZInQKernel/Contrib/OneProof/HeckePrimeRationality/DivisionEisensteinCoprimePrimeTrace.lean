import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinAffineZero

/-!
# Lower Eisenstein trace closure for a coprime new prime

The nonzero p-residue points of a complete N-fibre are linked by proved
integral Gamma(N) moves. The unique zero point is a scaled lower generator.
Subtracting that point from the actual complete-fibre distribution gives a
lower series combination with denominator p² - 1.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators Matrix MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

open EisensteinWeightTwo DivisionEisensteinLevelMaps

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- A nonzero p-residue fibre point has the same actual trace as the initial
nonzero row, by a proved principal-congruence motion. -/
theorem normalizedTrace_coprime_fiber_point (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hcop : Nat.Coprime p N) (a b : ℤ)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) (r s : Fin p)
    (hpoint : ((a + (N : ℤ) * (r : ℕ) : ℤ) : ZMod p) ≠ 0 ∨
      ((b + (N : ℤ) * (s : ℕ) : ℤ) : ZMod p) ≠ 0) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (divisionEisensteinMF (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
        ![a + (N : ℤ) * (r : ℕ),b + (N : ℤ) * (s : ℕ)]) =
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (divisionEisensteinMF (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) ![a,b]) := by
  have hc : (a : ZMod N) = ((a + (N : ℤ) * (r : ℕ) : ℤ) : ZMod N) := by simp
  have hd : (b : ZMod N) = ((b + (N : ℤ) * (s : ℕ) : ℤ) : ZMod N) := by simp
  obtain ⟨γ, hγ, h0, h1⟩ := exists_Gamma_coprime_fiber_move p N hcop a b
    (a + (N : ℤ) * (r : ℕ)) (b + (N : ℤ) * (s : ℕ)) hab hpoint hc hd
  have hv : ![(![a,b] ᵥ* γ.1) 0,(![a,b] ᵥ* γ.1) 1] = (![a,b] ᵥ* γ.1) := by
    ext i; fin_cases i <;> rfl
  have he := divisionMF_eq_of_congr (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
    _ _ (a + (N : ℤ) * (r : ℕ)) (b + (N : ℤ) * (s : ℕ)) h0 h1
  rw [hv] at he
  rw [← he]
  exact normalizedTrace_generator_SL N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) ![a,b] γ hγ

/-- The p²-1 scalar denominator really is nonzero for every prime. -/
theorem prime_square_sub_one_ne_zero (p : ℕ) [Fact p.Prime] : (p : ℂ) ^ 2 - 1 ≠ 0 := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hr : (p : ℝ) ^ 2 - 1 ≠ 0 := by
    have hpr : (2 : ℝ) ≤ p := by exact_mod_cast hp
    nlinarith
  exact_mod_cast hr

/-- A primitive upper generator has an explicitly produced lower series
combination; the auxiliary labels are outputs, not wanted membership inputs. -/
theorem normalizedTrace_coprime_primitive_formula (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hcop : Nat.Coprime p N) (a b : ℤ)
    (hab : (a : ZMod p) ≠ 0 ∨ (b : ZMod p) ≠ 0) :
    ∃ c d : ℤ,
      normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
        (divisionEisensteinMF (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) ![a,b]) =
      (((p : ℂ) ^ 2 - 1)⁻¹) •
        ((p : ℂ) ^ 2 • divisionEisensteinMF N hN ![a,b] - divisionEisensteinMF N hN ![c,d]) := by
  classical
  have hp : 0 < p := (Fact.out : p.Prime).pos
  obtain ⟨R, hR, hRu⟩ := exists_unique_affine_zero p N hcop a
  obtain ⟨S, hS, hSu⟩ := exists_unique_affine_zero p N hcop b
  obtain ⟨c, hc⟩ := hR
  obtain ⟨d, hd⟩ := hS
  let T := normalizedTrace N (p * N) (Nat.mul_pos hp hN)
  let F := divisionEisensteinMF (p * N) (Nat.mul_pos hp hN) ![a,b]
  let E := divisionEisensteinMF N hN ![c,d]
  let G := divisionEisensteinMF N hN ![a,b]
  have hfun (Q : Fin p × Fin p) : T (divisionEisensteinMF (p * N) (Nat.mul_pos hp hN)
      ![a + (N : ℤ) * (Q.1 : ℕ),b + (N : ℤ) * (Q.2 : ℕ)]) =
      T F + (if Q = (R,S) then E - T F else 0) := by
    by_cases hQ : Q = (R,S)
    · subst Q
      simp only [Prod.fst, Prod.snd, hc, hd, T, E, ↓reduceIte,
        series_scaled_label p N hp hN c d, normalizedTrace_restriction (Nat.mul_pos hp hN) (dvd_mul_left N p)]
      abel
    · have hpoint : ((a + (N : ℤ) * (Q.1 : ℕ) : ℤ) : ZMod p) ≠ 0 ∨
          ((b + (N : ℤ) * (Q.2 : ℕ) : ℤ) : ZMod p) ≠ 0 := by
        by_contra hn
        push_neg at hn
        have hr := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hn.1
        have hs := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hn.2
        exact hQ (Prod.ext (hRu Q.1 hr) (hSu Q.2 hs))
      simp only [hQ, ↓reduceIte, add_zero]
      exact normalizedTrace_coprime_fiber_point p N hN hcop a b hab Q.1 Q.2 hpoint
  have hsum : T (completeFiber p N hp hN a b) = (p : ℂ) ^ 2 • T F + (E - T F) := by
    rw [completeFiber, ← Fintype.sum_prod_type' (fun r s : Fin p =>
      divisionEisensteinMF (p * N) (Nat.mul_pos hp hN)
        ![a + (N : ℤ) * (r : ℕ),b + (N : ℤ) * (s : ℕ)]), map_sum]
    simp only [hfun, Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
      ← Nat.cast_smul_eq_nsmul ℂ, Nat.cast_mul, ← pow_two]
    simp
  have he : ((p : ℂ) ^ 2 - 1) • T F = (p : ℂ) ^ 2 • G - E := by
    apply _root_.ModularForm.ext
    intro τ
    have heq := congrArg (fun f : _root_.ModularForm (ΓP N) 2 => f τ) hsum
    rw [normalizedTrace_completeFiber p N hp hN a b] at heq
    simp only [smul_apply, smul_eq_mul, add_apply, sub_apply, G] at heq ⊢
    linear_combination -heq
  have hinv := congrArg (fun f : _root_.ModularForm (ΓP N) 2 => ((p : ℂ) ^ 2 - 1)⁻¹ • f) he
  simp only [smul_smul, inv_mul_cancel₀ (prime_square_sub_one_ne_zero p), one_smul] at hinv
  exact ⟨c, d, hinv⟩

/-- The arbitrary-label lower generator trace lemma for a coprime prime extension. -/
theorem arbitrary_generator_trace_coprime_prime_mem (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hcop : Nat.Coprime p N) (a : Fin 2 → ℤ) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)
      (divisionEisensteinMF (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) a) ∈ seriesSpan N hN := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  have hv : ![a 0,a 1] = a := by ext i; fin_cases i <;> rfl
  by_cases hz : (a 0 : ZMod p) = 0 ∧ (a 1 : ZMod p) = 0
  · obtain ⟨c, hc⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 0) p).mp hz.1
    obtain ⟨d, hd⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd (a 1) p).mp hz.2
    rw [← hv, hc, hd, series_scaled_label p N hp hN c d,
      normalizedTrace_restriction (Nat.mul_pos hp hN) (dvd_mul_left N p)]
    exact generator_mem_seriesSpan N hN ![c,d]
  · have hab : (a 0 : ZMod p) ≠ 0 ∨ (a 1 : ZMod p) ≠ 0 := by tauto
    obtain ⟨c, d, he⟩ := normalizedTrace_coprime_primitive_formula p N hN hcop (a 0) (a 1) hab
    rw [← hv, he]
    apply Submodule.smul_mem
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (generator_mem_seriesSpan N hN ![a 0,a 1]))
      (generator_mem_seriesSpan N hN ![c,d])

/-- All upper series-span members have actual lower trace closure in a coprime prime extension. -/
theorem trace_seriesSpan_coprime_prime (p N : ℕ) [Fact p.Prime]
    (hN : 0 < N) (hcop : Nat.Coprime p N)
    {f : _root_.ModularForm (ΓP (p * N)) 2}
    (hf : f ∈ seriesSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)) :
    normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) f ∈ seriesSpan N hN := by
  have hle : seriesSpan (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN) ≤
      (seriesSpan N hN).comap (normalizedTrace N (p * N) (Nat.mul_pos (Fact.out : p.Prime).pos hN)) := by
    apply Submodule.span_le.mpr
    rintro f ⟨a, rfl⟩
    exact arbitrary_generator_trace_coprime_prime_mem p N hN hcop a
  exact hle hf

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
