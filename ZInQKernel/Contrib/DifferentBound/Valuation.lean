/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors

Modified for this contribution: extracted only the finite-sum orthogonality and
DVR prime-power/multiplicity lemmas, moved them to an owned namespace, and added
ramification normalization and the finite-residue power-basis comparison.
Source revision: a6027b1d24fcb935c53bd5b50d11b40991cda418.
Source files: TauCeti/RingTheory/Valuation/Orthogonality.lean and
TauCeti/RingTheory/DiscreteValuationRing/Basic.lean.
-/
import Mathlib.NumberTheory.RamificationInertia.Valuation
import Mathlib.RingTheory.Valuation.Discrete.IsDiscreteValuationRing
import Mathlib.Tactic

/-!
# Valuation lemmas for the Serre derivative argument

No completeness, perfectness or algebraic closedness is assumed here. The
finite-sum theorem explicitly handles zero terms through infinite valuation.
The power-basis theorem proves absence of cancellation from distinct residues
modulo the actual ramification index; it does not assume absence of cancellation.
-/

namespace ZInQ.Contrib.DifferentBound

open IsLocalRing IsDedekindDomain

/-- A finite sum with pairwise distinct finite additive valuations has the least term valuation.
Zero terms (and an all-zero family) are included. Adapted from Tau Ceti's orthogonality lemma. -/
theorem addValuation_sum_eq_inf_of_ne
    {R Γ₀ : Type*} [Ring R] [LinearOrderedAddCommMonoidWithTop Γ₀]
    (v : AddValuation R Γ₀) {ι : Type*} (s : Finset ι) (f : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → v (f i) ≠ ⊤ → v (f j) ≠ ⊤ →
      v (f i) ≠ v (f j)) :
    v (∑ i ∈ s, f i) = s.inf fun i ↦ v (f i) := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hs
  · simp
  obtain ⟨j, hj, hjmin⟩ := s.exists_min_image (fun i ↦ v (f i)) hs
  rw [le_antisymm (Finset.inf_le hj) (Finset.le_inf hjmin)]
  rcases eq_or_ne (v (f j)) ⊤ with htop | htop
  · rw [htop, ← top_le_iff, ← htop]
    exact v.map_le_sum hjmin
  rw [← Finset.add_sum_erase s f hj]
  refine v.map_add_eq_of_lt_left (v.map_lt_sum htop fun i hi ↦ ?_)
  obtain ⟨hij, his⟩ := Finset.mem_erase.mp hi
  exact lt_of_le_of_ne (hjmin i his) fun heq ↦
    h i his j hj hij (heq ▸ htop) htop heq.symm

section DVR

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

/-- A DVR's maximal-ideal powers are measured by its normalized additive valuation. -/
theorem mem_maximalIdeal_pow_iff_le_addVal {n : ℕ} {x : B} :
    x ∈ maximalIdeal B ^ n ↔ (n : ℕ∞) ≤ IsDiscreteValuationRing.addVal B x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  rw [hπ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hπ.addVal_pow]

/-- The additive valuation of a nonzero element equals its principal ideal's multiplicity. -/
theorem addVal_eq_multiplicity_span_singleton {x : B} (hx : x ≠ 0) :
    IsDiscreteValuationRing.addVal B x =
      multiplicity (maximalIdeal B) (Ideal.span {x}) := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hπ
  rw [IsDiscreteValuationRing.addVal_def _ u hπ n rfl,
    Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_singleton_pow,
    ← hπ.maximalIdeal_eq, multiplicity_pow_self_of_prime
      (Ideal.prime_of_isPrime (IsDiscreteValuationRing.not_a_field B) inferInstance)]

end DVR

section DVRExtension

variable {A B : Type*} [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B]
  [Module.IsTorsionFree A B] [(maximalIdeal B).LiesOver (maximalIdeal A)]

/-- Ramification of a faithful local extension of DVRs is positive. -/
theorem dvr_ramificationIdx_pos : 0 < (maximalIdeal B).ramificationIdx A :=
  Ideal.ramificationIdx_pos_of_isDedekindDomain' (maximalIdeal B)
    (IsDiscreteValuationRing.not_a_field A)

/-- Normalized additive valuation on a DVR extension restricts by the ramification index. -/
theorem addVal_algebraMap (a : A) :
    IsDiscreteValuationRing.addVal B (algebraMap A B a) =
      (maximalIdeal B).ramificationIdx A • IsDiscreteValuationRing.addVal A a := by
  have he : (maximalIdeal B).ramificationIdx A ≠ 0 :=
    (dvr_ramificationIdx_pos (A := A) (B := B)).ne'
  by_cases ha : a = 0
  · simp [ha, nsmul_eq_mul, he]
  have hmapa : algebraMap A B a ≠ 0 := by
    simpa only [map_zero] using (FaithfulSMul.algebraMap_injective A B).ne_iff.mpr ha
  let v := IsDiscreteValuationRing.maximalIdeal A
  let w := IsDiscreteValuationRing.maximalIdeal B
  have : w.asIdeal.LiesOver v.asIdeal := by
    change (maximalIdeal B).LiesOver (maximalIdeal A)
    infer_instance
  have hI : (Ideal.span {a} : Ideal A) ≠ ⊥ := by
    simpa only [ne_eq, Ideal.span_singleton_eq_bot] using ha
  have hmapI : (Ideal.span {a}).map (algebraMap A B) ≠ ⊥ :=
    Ideal.map_ne_bot_of_ne_bot hI
  have h := Ideal.IsDedekindDomain.emultiplicity_map_eq_ramificationIdx'_mul hI
    v.irreducible w.irreducible w.ne_bot
  rw [Ideal.ramificationIdx'_eq_ramificationIdx v.asIdeal w.asIdeal v.ne_bot,
    (FiniteMultiplicity.of_prime_left v.prime hI).emultiplicity_eq_multiplicity,
    (FiniteMultiplicity.of_prime_left w.prime hmapI).emultiplicity_eq_multiplicity,
    Ideal.map_span, Set.image_singleton] at h
  rw [addVal_eq_multiplicity_span_singleton hmapa,
    addVal_eq_multiplicity_span_singleton ha, nsmul_eq_mul]
  exact h

/-- The valuations of power-basis terms have their exponent as residue modulo `e`. -/
theorem addVal_algebraMap_mul_pow {π : B} (hπ : Irreducible π)
    (a : A) (i : ℕ) :
    IsDiscreteValuationRing.addVal B (algebraMap A B a * π ^ i) =
      (maximalIdeal B).ramificationIdx A • IsDiscreteValuationRing.addVal A a + (i : ℕ∞) := by
  rw [IsDiscreteValuationRing.addVal_mul, addVal_algebraMap, hπ.addVal_pow]

/-- Distinct powers below the ramification index have distinct finite term valuations. -/
theorem powerBasis_term_valuations_ne {π : B} (hπ : Irreducible π) {m : ℕ}
    (hm : m ≤ (maximalIdeal B).ramificationIdx A) (c : Fin m → A)
    (i j : Fin m) (hij : i ≠ j)
    (hi : IsDiscreteValuationRing.addVal B (algebraMap A B (c i) * π ^ (i : ℕ)) ≠ ⊤)
    (hj : IsDiscreteValuationRing.addVal B (algebraMap A B (c j) * π ^ (j : ℕ)) ≠ ⊤) :
    IsDiscreteValuationRing.addVal B (algebraMap A B (c i) * π ^ (i : ℕ)) ≠
      IsDiscreteValuationRing.addVal B (algebraMap A B (c j) * π ^ (j : ℕ)) := by
  intro heq
  have hci : c i ≠ 0 := by
    intro hz
    apply hi
    simp [hz]
  have hcj : c j ≠ 0 := by
    intro hz
    apply hj
    simp [hz]
  have hai : IsDiscreteValuationRing.addVal A (c i) ≠ ⊤ :=
    IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hci
  have haj : IsDiscreteValuationRing.addVal A (c j) ≠ ⊤ :=
    IsDiscreteValuationRing.addVal_eq_top_iff.not.mpr hcj
  lift IsDiscreteValuationRing.addVal A (c i) to ℕ using hai with a ha
  lift IsDiscreteValuationRing.addVal A (c j) to ℕ using haj with b hb
  rw [addVal_algebraMap_mul_pow hπ, addVal_algebraMap_mul_pow hπ, ← ha, ← hb] at heq
  simp only [nsmul_eq_mul] at heq
  have hn : (maximalIdeal B).ramificationIdx A * a + (i : ℕ) =
      (maximalIdeal B).ramificationIdx A * b + (j : ℕ) := by
    exact_mod_cast heq
  have hnmod := congrArg (· % (maximalIdeal B).ramificationIdx A) hn
  have hiLt := i.is_lt.trans_le hm
  have hjLt := j.is_lt.trans_le hm
  simp [Nat.add_mod, Nat.mod_eq_of_lt hiLt, Nat.mod_eq_of_lt hjLt] at hnmod
  exact hij (Fin.ext hnmod)

/-- All powers up to the ramification index participate; zero coefficients do not invalidate
orthogonality. This is the no-cancellation step used for the derivative. -/
theorem addVal_sum_algebraMap_mul_pow {π : B} (hπ : Irreducible π) {m : ℕ}
    (hm : m ≤ (maximalIdeal B).ramificationIdx A) (c : Fin m → A) :
    IsDiscreteValuationRing.addVal B (∑ i, algebraMap A B (c i) * π ^ (i : ℕ)) =
      (Finset.univ : Finset (Fin m)).inf fun i ↦
        (maximalIdeal B).ramificationIdx A • IsDiscreteValuationRing.addVal A (c i) +
          ((i : ℕ) : ℕ∞) := by
  rw [addValuation_sum_eq_inf_of_ne]
  · congr 1
    funext i
    exact addVal_algebraMap_mul_pow hπ (c i) i
  · intro i _ j _ hij hi hj
    exact powerBasis_term_valuations_ne hπ hm c i j hij hi hj

end DVRExtension

end ZInQ.Contrib.DifferentBound
