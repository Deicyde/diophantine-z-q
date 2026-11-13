/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.
Authors: The Tau Ceti contributors

The finite-support truncation argument is adapted from TauCetiProject/TauCeti
at a6027b1d24fcb935c53bd5b50d11b40991cda418,
 NumberTheory/LocalField/Different/Hilbert.lean, lines 105–117.
The actual-global faithful action, different multiplicity interfaces and
unramified specialization are project proofs over the existing Mathlib pin.
See docs/research/t20-hilbert-different.md for provenance and license.
-/
import ZInQKernel.Contrib.HilbertDifferent.Filtration
import ZInQKernel.HDecomp.Conductor.Breaks

/-!
# The actual global ramification filtration

These lemmas concern exactly `GlueConductor.ramGroup`, not a surrogate local
filtration. They prove eventual triviality and basic ideal-exponent interfaces;
they do not assume or claim Hilbert's different formula.
-/

open NumberField Finset

namespace ZInQ.Contrib.HilbertDifferent

/-- Restricting automorphisms to the ring of integers is faithful: equality there extends to
its fraction field. Kept as a named instance value, rather than a new global instance. -/
theorem ringOfIntegers_faithfulSMul (L : Type*) [Field L] [NumberField L] :
    FaithfulSMul Gal(L/ℚ) (𝓞 L) where
  eq_of_smul_eq_smul {σ τ} h := by
    apply AlgEquiv.ext
    intro y
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (𝓞 L) y
    have ha : σ (algebraMap (𝓞 L) L a) = τ (algebraMap (𝓞 L) L a) :=
      congrArg (fun z : 𝓞 L ↦ (z : L)) (h a)
    have hb : σ (algebraMap (𝓞 L) L b) = τ (algebraMap (𝓞 L) L b) :=
      congrArg (fun z : 𝓞 L ↦ (z : L)) (h b)
    simp only [map_div₀, ha, hb]

/-- The global lower ramification groups decrease. -/
theorem ramGroup_antitone (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) :
    Antitone (GlueConductor.ramGroup L P) :=
  powerInertia_antitone P

/-- The orders of the global lower ramification groups decrease. -/
theorem ramCard_antitone (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) :
    Antitone (GlueConductor.ramCard L P) :=
  fun _ _ hij ↦ Subgroup.card_le_of_le (ramGroup_antitone L P hij)

/-- Every lower ramification group contains its identity, including the trivial-group case. -/
theorem ramCard_pos (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L)) (i : ℕ) :
    0 < GlueConductor.ramCard L P i := Nat.card_pos

/-- A trivial lower ramification group stays trivial at all larger indices. -/
theorem ramGroup_eq_bot_of_ge (L : Type*) [Field L] [NumberField L] (P : Ideal (𝓞 L))
    {n i : ℕ} (hn : GlueConductor.ramGroup L P n = ⊥) (hi : n ≤ i) :
    GlueConductor.ramGroup L P i = ⊥ :=
  le_bot_iff.mp ((ramGroup_antitone L P hi).trans hn.le)

/-- Every prime's actual global ramification filtration is eventually trivial. No nonzero-prime
or Galois hypothesis is needed for this separation statement. -/
theorem exists_forall_ramGroup_eq_bot (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] :
    ∃ N : ℕ, ∀ i, N ≤ i → GlueConductor.ramGroup L P i = ⊥ := by
  let := ringOfIntegers_faithfulSMul L
  exact exists_forall_powerInertia_eq_bot (G := Gal(L/ℚ)) (Q := P) Ideal.IsPrime.ne_top'

/-- The sum in the main global Hilbert target, with its original natural subtraction. -/
noncomputable abbrev ramificationSum (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, (GlueConductor.ramCard L P i - 1)

/-- Once `G_n` is trivial, the target's finite range contains the whole support. -/
theorem finsum_ramCard_sub_one_eq_sum (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) {n : ℕ} (hn : GlueConductor.ramGroup L P n = ⊥) :
    (∑ᶠ i : ℕ, (GlueConductor.ramCard L P i - 1)) = ramificationSum L P n := by
  apply finsum_eq_sum_of_support_subset
  intro i hi
  simp only [Function.mem_support, ne_eq] at hi
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  have hbot := ramGroup_eq_bot_of_ge L P hn (not_lt.mp h)
  exact hi (by rw [show GlueConductor.ramCard L P i = 1 from
    by rw [GlueConductor.ramCard, hbot, Subgroup.card_bot], Nat.sub_self])

/-- A nonzero prime occurs to a finite multiplicity in the genuine global different. -/
theorem different_finiteMultiplicity (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    FiniteMultiplicity P (differentIdeal ℤ (𝓞 L)) :=
  FiniteMultiplicity.of_prime_left ((Ideal.prime_iff_isPrime hP).mpr inferInstance)
    differentIdeal_ne_bot

/-- A prime's multiplicity in the global different is exactly its ideal-power divisibility.
The finiteness hypothesis is proved here, not silently assumed at exponent zero. -/
theorem multiplicity_different_eq_iff (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) (d : ℕ) :
    multiplicity P (differentIdeal ℤ (𝓞 L)) = d ↔
      P ^ d ∣ differentIdeal ℤ (𝓞 L) ∧ ¬ P ^ (d + 1) ∣ differentIdeal ℤ (𝓞 L) :=
  (different_finiteMultiplicity L P hP).multiplicity_eq_iff

/-- Unconditional partial result: an eventual triviality witness and the exact global different
exponent both exist. This deliberately does not identify that exponent with the ramification sum. -/
theorem exists_ramGroup_eq_bot_and_exact_differentPower (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    ∃ n d : ℕ, GlueConductor.ramGroup L P n = ⊥ ∧
      P ^ d ∣ differentIdeal ℤ (𝓞 L) ∧ ¬ P ^ (d + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  obtain ⟨n, hn⟩ := exists_forall_ramGroup_eq_bot L P
  exact ⟨n, _, hn n le_rfl, (multiplicity_different_eq_iff L P hP _).mp rfl⟩

/-- The exact local-to-global assembly interface. The global arithmetic identity is an explicit
input to this helper, not an assumed `Fact` and not a proof of the closed T20 proposition. -/
theorem hilbertDifferentAt_of_multiplicity_finsum (L : Type*) [Field L] [NumberField L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)
    (hformula : multiplicity P (differentIdeal ℤ (𝓞 L)) =
      ∑ᶠ i : ℕ, (GlueConductor.ramCard L P i - 1)) :
    ∃ n, GlueConductor.ramGroup L P n = ⊥ ∧
      P ^ (ramificationSum L P n) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (ramificationSum L P n + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  obtain ⟨n, hn⟩ := exists_forall_ramGroup_eq_bot L P
  have hsum : multiplicity P (differentIdeal ℤ (𝓞 L)) = ramificationSum L P n :=
    hformula.trans (finsum_ramCard_sub_one_eq_sum L P (hn n le_rfl))
  exact ⟨n, hn n le_rfl, (multiplicity_different_eq_iff L P hP _).mp hsum⟩

/-- The inertia cardinality at a nonzero prime equals the usual global ramification index. -/
theorem ramCard_zero_eq_ramificationIdx (L : Type*) [Field L] [NumberField L] [IsGalois ℚ L]
    (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥) :
    GlueConductor.ramCard L P 0 = P.ramificationIdx ℤ := by
  let p := P.under ℤ
  have hp : p ≠ ⊥ := mt Ideal.eq_bot_of_under_eq_bot hP
  let : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance hp
  show Nat.card ((P ^ (0 + 1)).inertia Gal(L/ℚ)) = _
  rw [zero_add, pow_one, Ideal.card_inertia_eq_ramificationIdxIn p P,
    Ideal.ramificationIdxIn_eq_ramificationIdx p P Gal(L/ℚ)]

/-- Hilbert's exact global conclusion at any unramified prime, including its zero-exponent
boundary case, follows from the pinned Mathlib different and inertia theorems. -/
theorem hilbertDifferentAt_of_isUnramifiedAt (L : Type*) [Field L] [NumberField L]
    [IsGalois ℚ L] (P : Ideal (𝓞 L)) [P.IsPrime] (hP : P ≠ ⊥)
    [Algebra.IsUnramifiedAt ℤ P] :
    ∃ n, GlueConductor.ramGroup L P n = ⊥ ∧
      P ^ (ramificationSum L P n) ∣ differentIdeal ℤ (𝓞 L) ∧
      ¬ P ^ (ramificationSum L P n + 1) ∣ differentIdeal ℤ (𝓞 L) := by
  have hcard : GlueConductor.ramCard L P 0 = 1 := by
    rw [ramCard_zero_eq_ramificationIdx L P hP, Ideal.ramificationIdx_eq_one_of_isUnramifiedAt]
  refine ⟨0, Subgroup.card_eq_one.mp hcard, ?_⟩
  simpa [ramificationSum] using
    And.intro (one_dvd (differentIdeal ℤ (𝓞 L)))
      ((not_dvd_differentIdeal_iff (A := ℤ) (P := P)).mpr inferInstance)

/-- The base ring of the completed/global number-field different can be identified with ℤ
without changing the ideal in `𝓞 L`. This proves the base identification, not completion itself. -/
theorem differentIdeal_ringOfIntegersRat_eq (L : Type*) [Field L] [NumberField L] :
    differentIdeal (𝓞 ℚ) (𝓞 L) = differentIdeal ℤ (𝓞 L) := by
  have hrange : (algebraMap (𝓞 ℚ) ℚ).range = (algebraMap ℤ ℚ).range := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨Rat.ringOfIntegersEquiv y, by simp⟩
    · rintro ⟨y, rfl⟩
      exact ⟨Rat.ringOfIntegersEquiv.symm y, by simp⟩
  apply FractionalIdeal.coeIdeal_injective (K := L)
  change (↑(differentIdeal (𝓞 ℚ) (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) =
    (↑(differentIdeal ℤ (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L)
  rw [coeIdeal_differentIdeal (𝓞 ℚ) ℚ L (𝓞 L), coeIdeal_differentIdeal ℤ ℚ L (𝓞 L)]
  congr 1
  ext x
  rw [FractionalIdeal.mem_dual one_ne_zero, FractionalIdeal.mem_dual one_ne_zero, hrange]

end ZInQ.Contrib.HilbertDifferent
