import ZInQKernel.Contrib.TYZEquivalence.Equivalence

/-!
# Focused P5 statement, boundary and axiom checks

Compile this file in a fresh Lean process after compiling the two proof modules.
The named `exactStatement` provides an independently written expected type for
`scripts/audit_kernel.lean`. These checks do not authorize protocol acceptance
and do not discharge any of the headline's literature premises.
-/

namespace ZInQ.PropN.TYZEquivalence.Checks

open ZInQ.Literature ZInQ.RouteK.Rank5b

/-- The exact source-derived target type, with no extra hypotheses or universes. -/
theorem exactStatement :
    TYZInputs ↔ ∀ n : ℕ, n % 8 = 5 → Squarefree n →
      (∃ F : ℂ → ℂ, IsLContinuation (shortCurve (-(n : ℚ) ^ 2)) F ∧
        analyticOrderAt F 1 ≤ 1) ∨ (T5aCl n = 0 ∧ T5bCl n = 0) :=
  tyzInputs_iff

/-- Class 5 implies positive odd indices other than 1, before imposing
squarefreeness. Thus no zero parameter or degenerate endpoint enters I7. -/
theorem class5_domain {n : ℕ} (hn : n % 8 = 5) : 0 < n ∧ n ≠ 1 ∧ Odd n := by
  exact ⟨by omega, by omega, Nat.odd_iff.mpr (by omega)⟩

/-- The two exceptional numerical indices have the stipulated witness values. -/
theorem zero_and_one : canonicalL 0 = 0 ∧ canonicalL 1 = 1 :=
  ⟨canonicalL_zero, canonicalL_one⟩

/-- All chosen integer values really are bits; this is a representative for the
existential encoding, not a claim that the original TYZ invariants are bits. -/
theorem canonicalL_values (m : ℕ) : canonicalL m = 0 ∨ canonicalL m = 1 := by
  unfold canonicalL
  split_ifs
  · have hval : (Lam m).val < 2 := ZMod.val_lt (Lam m)
    omega
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- A zero class-5 value with an inhabited model cannot hide a nonzero row.
This checks both rows and explicitly covers the zero-value witness branch. -/
theorem no_zero_value_at_nonzero_rows {L : ℕ → ℤ} (hL1 : L 1 = 1)
    (h28 : LemmaTwoEight L) {n : ℕ} (hn : n % 8 = 5) (hsq : Squarefree n)
    (hG : Nonempty (GenusData L n)) (hrows : T5aCl n ≠ 0 ∨ T5bCl n ≠ 0) : L n ≠ 0 := by
  intro hLn
  have hzero := (genusData_nonempty_iff_genusSums hL1 h28 hn hsq hLn).mp hG
  rcases hrows with ha | hb
  · exact ha hzero.1
  · exact hb hzero.2

#check ZInQ.PropN.tyzInputs_iff
#check ZInQ.PropN.tyzInputs_iff_readingA_and_supportedContinuation
#check ZInQ.PropN.tyzInputs_of_readingA

#print axioms canonicalL
#print axioms canonicalL_cast
#print axioms canonicalL_zero
#print axioms canonicalL_one
#print axioms canonicalL_ne_zero_iff
#print axioms canonicalL_eq_zero_of_other
#print axioms canonicalL_lemmaTwoEight
#print axioms weightedParity_eq_lam
#print axioms genusData_nonempty_iff_genusSums
#print axioms canonicalL_genusData
#print axioms ZInQ.PropN.ParitySupportedContinuation
#print axioms ZInQ.PropN.ParitySupportedOrderOne
#print axioms ZInQ.PropN.tyzInputs_iff
#print axioms ZInQ.PropN.tyzInputs_iff_supportedOrderOne
#print axioms ZInQ.PropN.supportedOrderOne_of_readingA
#print axioms ZInQ.PropN.tyzInputs_iff_readingA_and_supportedContinuation
#print axioms ZInQ.PropN.supportedContinuation_of_hecke
#print axioms ZInQ.PropN.tyzInputs_of_readingA
#print axioms ZInQ.PropN.tyzInputs_and_hecke_iff
#print axioms exactStatement
#print axioms class5_domain
#print axioms zero_and_one
#print axioms canonicalL_values
#print axioms no_zero_value_at_nonzero_rows

-- Axiom closure of the existing substantive proof suppliers, checked as read-only
-- imports. No source or declaration in these modules is changed by P5.
#print axioms ZInQ.PropN.lemmaN1_core
#print axioms ZInQ.PropN.lemmaN1
#print axioms ZInQ.PropN.matching
#print axioms ZInQ.PropN.genusSums_eq_zero
#print axioms ZInQ.PropN.Witness.genusData_nonempty
#print axioms ZInQ.PropN.Witness.genusData_nonempty_iff_parities
#print axioms ZInQ.Literature.IsLContinuation.eq

end ZInQ.PropN.TYZEquivalence.Checks
