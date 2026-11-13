/-
Copyright the authors of Vilin97/Autoformalization (green-tao/), Apache License 2.0;
see ThirdParty/GreenTao/LICENSE.

Adapted from `Submission/Primes/WTrick.lean`, `Submission/Primes/Extraction.lean` and
`Submission/Primes/WTrickDensity.lean` (lines 145–341) at commit
0dc67d87416c19690dd641a178ada32cca95c651.
Modified 2026 for the diophantine-z-q project: generalized from the set of primes to a subset `A`
of the primes (the weight is multiplied by the indicator of `A`; the residue pigeonhole runs over
the elements of `A` only).
-/
import Submission.Primes.Extraction
import Submission.Primes.WTrickDensity

/-!
# The W-tricked weight of a set of primes

`wTrickedSetWeight A α W b = 1_A(W n + b) · wTrickedPrimeWeight α W b`: its basic bounds, the
extraction of a progression in `A` from positive off-diagonal mass, and the residue pigeonhole
over the elements of `A` in the quarter interval `(X/4, X]`, `X = W ⌊N/8⌋`.
-/

namespace ZInQ.GreenTaoDense

open Submission.GreenTao Finset Real
open scoped BigOperators

open Classical in
/-- The W-tricked prime weight restricted to the residues `n` with `W n + b ∈ A`. -/
noncomputable def wTrickedSetWeight {N : ℕ} [NeZero N] (A : Set ℕ) (α : ℝ) (W b : ℕ)
    (n : ZMod N) : ℝ :=
  if wTrickedValue W b n ∈ A then wTrickedPrimeWeight α W b n else 0

section

variable {N : ℕ} [NeZero N] {A : Set ℕ} {α : ℝ}

theorem wTrickedSetWeight_nonneg (hα : 0 ≤ α) (W b : ℕ) (n : ZMod N) :
    0 ≤ wTrickedSetWeight A α W b n := by
  unfold wTrickedSetWeight
  split_ifs
  · exact wTrickedPrimeWeight_nonneg hα W b n
  · exact le_rfl

theorem wTrickedSetWeight_le (hα : 0 ≤ α) (W b : ℕ) (n : ZMod N) :
    wTrickedSetWeight A α W b n ≤ wTrickedPrimeWeight α W b n := by
  unfold wTrickedSetWeight
  split_ifs
  · exact le_rfl
  · exact wTrickedPrimeWeight_nonneg hα W b n

theorem wTrickedSetWeight_pos_iff (hα : 0 < α) {W : ℕ} (hW : 0 < W) (b : ℕ) (n : ZMod N) :
    0 < wTrickedSetWeight A α W b n ↔
      (n.val ∈ greenTaoInterval N ∧ Nat.Prime (wTrickedValue W b n)) ∧
        wTrickedValue W b n ∈ A := by
  unfold wTrickedSetWeight
  split_ifs with h
  · rw [wTrickedPrimeWeight_pos_iff hα hW]
    tauto
  · simp [h]

end

/-- **Extraction.** Positive off-diagonal mass of the `A`-weight gives a `k`-term progression in
`A`. Adapted from `containsAP_primes_of_wTricked_offDiagMass_pos`. -/
theorem containsAP_of_wTrickedSetWeight_offDiagMass_pos {A : Set ℕ} {k N : ℕ} [NeZero N]
    (hk : 2 ≤ k) {α : ℝ} (hα : 0 < α) {W : ℕ} (hW : 0 < W) (b : ℕ)
    (hmass : 0 < cyclicAPOffDiagMass k N (wTrickedSetWeight A α W b)) :
    ContainsAP A k := by
  have hf : ∀ x : ZMod N, 0 ≤ wTrickedSetWeight A α W b x :=
    wTrickedSetWeight_nonneg hα.le W b
  obtain ⟨a, d, hd, hpositive⟩ := exists_cyclicAP_of_offDiagMass_pos hf hmass
  have hpreimage : ContainsAP {n : ℕ | W * n + b ∈ A} k := by
    apply containsAP_of_cyclicAPVal_shortInterval a d hd hk
      ((N / 64 : ℕ) : ℤ) ((N / 4 : ℕ) : ℤ)
    · intro j hj
      let jf : Fin k := ⟨j, hj⟩
      have hsupport :=
        ((wTrickedSetWeight_pos_iff hα hW b (cyclicAPTerm a d jf)).mp (hpositive jf)).1
      have hb := mem_greenTaoInterval.mp hsupport.1
      have hbInt :
          ((N / 64 : ℕ) : ℤ) ≤ ((cyclicAPTerm a d jf).val : ℤ) ∧
            ((cyclicAPTerm a d jf).val : ℤ) ≤ ((N / 4 : ℕ) : ℤ) := by
        exact_mod_cast hb
      change ((N / 64 : ℕ) : ℤ) ≤ cyclicAPVal a d j ∧
        (cyclicAPVal a d j : ℤ) ≤ ((N / 4 : ℕ) : ℤ)
      simpa only [cyclicAPVal, cyclicAPTerm, jf] using hbInt
    · exact greenTaoInterval_twice_width_lt (NeZero.pos N)
    · intro j hj
      let jf : Fin k := ⟨j, hj⟩
      have hmem :=
        ((wTrickedSetWeight_pos_iff hα hW b (cyclicAPTerm a d jf)).mp (hpositive jf)).2
      simpa [wTrickedValue, cyclicAPVal, cyclicAPTerm, jf] using hmem
  exact hpreimage.affine hW

/-! ## Density selection for `A` -/

section Density

open Classical

/-- The elements of `A` among the primes of `(X/4, X]` in the class `b` mod `W`,
`X = W ⌊N/8⌋`. -/
noncomputable def quarterIntervalSetClass (A : Set ℕ) (W N b : ℕ) : Finset ℕ :=
  (quarterIntervalResidueClass W N b).filter (· ∈ A)

variable {A : Set ℕ} {W N b : ℕ} [NeZero N] {α : ℝ}

theorem wTrickedSetWeight_untrickPrimeZMod (α : ℝ) (hW : 0 < W) {p : ℕ}
    (hp : p ∈ quarterIntervalSetClass A W N b) :
    wTrickedSetWeight A α W b (untrickPrimeZMod N W b p) =
      α * ((W.totient : ℝ) / W) * log p := by
  rw [quarterIntervalSetClass, mem_filter] at hp
  have hA : wTrickedValue W b (untrickPrimeZMod N W b p) ∈ A := by
    rw [wTrickedValue_untrickPrimeZMod hW hp.1]; exact hp.2
  unfold wTrickedSetWeight
  split_ifs
  exact wTrickedPrimeWeight_untrickPrimeZMod α hW hp.1

theorem setClass_log_mass_div_card_le_mean (hα : 0 ≤ α) (hW : 0 < W) :
    (α * ((W.totient : ℝ) / W) * ∑ p ∈ quarterIntervalSetClass A W N b, log p) / N ≤
      mean (wTrickedSetWeight A α W b : ZMod N → ℝ) := by
  have hinj : Set.InjOn (untrickPrimeZMod N W b) (quarterIntervalSetClass A W N b) :=
    (untrickPrimeZMod_injOn hW).mono (fun p hp => (mem_filter.mp hp).1)
  have hsum : α * ((W.totient : ℝ) / W) * ∑ p ∈ quarterIntervalSetClass A W N b, log p =
      ∑ n ∈ (quarterIntervalSetClass A W N b).image (untrickPrimeZMod N W b),
        wTrickedSetWeight A α W b n := by
    rw [Finset.sum_image hinj, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p hp => (wTrickedSetWeight_untrickPrimeZMod α hW hp).symm
  rw [mean, Fintype.expect_eq_sum_div_card, ZMod.card, hsum]
  exact div_le_div_of_nonneg_right
    (Finset.sum_le_univ_sum_of_nonneg (wTrickedSetWeight_nonneg hα W b)) (Nat.cast_nonneg N)

omit [NeZero N] in
theorem card_mul_log_cutoff_le_setClass_log_mass :
    (#(quarterIntervalSetClass A W N b) : ℝ) * log (wTrickPrimeScale W N / 4 + 1 : ℕ) ≤
      ∑ p ∈ quarterIntervalSetClass A W N b, log p := by
  rw [← nsmul_eq_mul, ← Finset.sum_const]
  apply Finset.sum_le_sum
  intro p hp
  apply Real.log_le_log
  · positivity
  · exact_mod_cast Nat.succ_le_iff.mpr
      (mem_quarterIntervalResidueClass.mp (mem_filter.mp hp).1).2.1

/-- **Residue pigeonhole for `A`.** Adapted from `exists_reducedResidue_mean_lower_bound`, with
the primes of the quarter interval replaced by the elements of `A` among them. -/
theorem exists_reducedResidue_setWeight_mean_lower_bound (A : Set ℕ) {w N : ℕ} [NeZero N]
    {α : ℝ} (hα : 0 ≤ α) (hw : w ≤ wTrickPrimeScale (primorial w) N / 4) :
    ∃ b ∈ reducedResidues (primorial w),
      (((α / (primorial w : ℝ)) *
          (#((primesInQuarterInterval (wTrickPrimeScale (primorial w) N)).filter (· ∈ A)) : ℝ) *
          log (wTrickPrimeScale (primorial w) N / 4 + 1 : ℕ)) / N) ≤
        mean (wTrickedSetWeight A α (primorial w) b : ZMod N → ℝ) := by
  set X := wTrickPrimeScale (primorial w) N with hX
  set S := (primesInQuarterInterval X).filter (· ∈ A) with hS
  obtain ⟨b, hb, hcard⟩ := exists_reducedResidue_for_primes_above (w := w) S
    (fun p hp => (mem_primesInQuarterInterval.mp (mem_filter.mp hp).1).1)
    (fun p hp => hw.trans_lt (mem_primesInQuarterInterval.mp (mem_filter.mp hp).1).2.1)
  have hfiber : residueFiber S (primorial w) b = quarterIntervalSetClass A (primorial w) N b := by
    ext p
    simp only [hS, mem_residueFiber, mem_filter, quarterIntervalSetClass,
      quarterIntervalResidueClass, ← hX]
    tauto
  rw [hfiber] at hcard
  refine ⟨b, hb, ?_⟩
  have hcardReal : (#S : ℝ) ≤
      ((primorial w).totient : ℝ) * (#(quarterIntervalSetClass A (primorial w) N b) : ℝ) := by
    exact_mod_cast hcard
  set L : ℝ := log (X / 4 + 1 : ℕ) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by exact_mod_cast (show 1 ≤ X / 4 + 1 by omega))
  have hscale : 0 ≤ (α / (primorial w : ℝ)) * L :=
    mul_nonneg (div_nonneg hα (Nat.cast_nonneg _)) hL0
  have hW : (0 : ℝ) < primorial w := by exact_mod_cast primorial_pos w
  calc ((α / (primorial w : ℝ)) * (#S : ℝ) * L) / N
      = (((α / (primorial w : ℝ)) * L) * (#S : ℝ)) / N := by ring
    _ ≤ (((α / (primorial w : ℝ)) * L) * (((primorial w).totient : ℝ) *
          (#(quarterIntervalSetClass A (primorial w) N b) : ℝ))) / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcardReal hscale)
          (Nat.cast_nonneg N)
    _ = (α * (((primorial w).totient : ℝ) / primorial w) *
          ((#(quarterIntervalSetClass A (primorial w) N b) : ℝ) * L)) / N := by
        field_simp
    _ ≤ (α * (((primorial w).totient : ℝ) / primorial w) *
          ∑ p ∈ quarterIntervalSetClass A (primorial w) N b, log p) / N := by
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
        exact mul_le_mul_of_nonneg_left card_mul_log_cutoff_le_setClass_log_mass
          (mul_nonneg hα (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
    _ ≤ mean (wTrickedSetWeight A α (primorial w) b : ZMod N → ℝ) :=
        setClass_log_mass_div_card_le_mean hα (primorial_pos w)

end Density

end ZInQ.GreenTaoDense
