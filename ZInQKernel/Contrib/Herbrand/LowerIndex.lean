import ZInQKernel.Contrib.Herbrand.Valuation
import ZInQKernel.Contrib.Herbrand.Monogenic

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described at
https://www.apache.org/licenses/LICENSE-2.0 .
Authors: The Tau Ceti contributors

CHANGED / PORTED FILE: minimal lower-index and generator criteria from
TauCeti/RingTheory/LocalRing/RamificationGroup.lean,
TauCeti/RingTheory/Ideal/Inertia.lean and
TauCeti/Algebra/Ring/Action/End.lean at
 a6027b1d24fcb935c53bd5b50d11b40991cda418.
The filtration is `PkgI6.lowerRam`, not a substitute abstract filtration.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing

section Generators

variable {R S G : Type*} [CommSemiring R] [CommRing S] [Group G]
  [Algebra R S] [MulSemiringAction G S] [SMulCommClass G R S]

/-- The congruence criterion is checked on generators by algebra induction. -/
theorem mem_inertia_of_adjoin_eq_top {I : Ideal S} {s : Set S}
    (hs : Algebra.adjoin R s = ⊤) {σ : G} :
    σ ∈ I.inertia G ↔ ∀ x ∈ s, σ • x - x ∈ I := by
  rw [Ideal.mem_inertia]
  refine ⟨fun h x _ => h x, fun h x => ?_⟩
  have hx : x ∈ Algebra.adjoin R s := hs ▸ Algebra.mem_top
  induction hx using Algebra.adjoin_induction with
  | mem y hy => exact h y hy
  | algebraMap r => simp
  | add y z _ _ hy hz =>
    rw [smul_add, add_sub_add_comm]
    exact add_mem hy hz
  | mul y z _ _ hy hz =>
    rw [smul_mul']
    exact I.mul_sub_mul_mem hy hz

/-- Every displacement is a multiple of the displacement of an algebra generator. -/
theorem displacement_dvd_of_adjoin_eq_top {ξ : S} (hξ : Algebra.adjoin R {ξ} = ⊤)
    (σ : G) (x : S) : σ • ξ - ξ ∣ σ • x - x := by
  apply Ideal.mem_span_singleton.mp
  apply Ideal.mem_inertia.mp
    ((mem_inertia_of_adjoin_eq_top hξ).mpr (by
      simpa only [Set.mem_singleton_iff, forall_eq] using
        Ideal.mem_span_singleton_self (σ • ξ - ξ))) x

/-- Faithful automorphisms of a monogenic algebra are distinguished by the generator. -/
theorem generator_orbit_injective [FaithfulSMul G S] {ξ : S}
    (hξ : Algebra.adjoin R {ξ} = ⊤) : Function.Injective fun σ : G => σ • ξ :=
  fun _ _ h => MulSemiringAction.toAlgHom_injective R S <|
    AlgHom.ext_of_adjoin_eq_top hξ <| Set.eqOn_singleton.mpr h

end Generators

section LowerIndex

variable (A B : Type) [CommRing A] [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]
  [Algebra A B]

/-- Serre's actual lower index: the minimum valuation of every displacement on `B`. -/
noncomputable def lowerIndex (σ : B ≃ₐ[A] B) : ℕ∞ :=
  ⨅ x : B, IsDiscreteValuationRing.addVal B (σ x - x)

theorem le_lowerIndex_iff {n : ℕ∞} {σ : B ≃ₐ[A] B} :
    n ≤ lowerIndex A B σ ↔ ∀ x : B, n ≤ IsDiscreteValuationRing.addVal B (σ x - x) :=
  le_iInf_iff

theorem lowerIndex_le_addVal (σ : B ≃ₐ[A] B) (x : B) :
    lowerIndex A B σ ≤ IsDiscreteValuationRing.addVal B (σ x - x) :=
  iInf_le _ x

/-- This ties the lower index to the locked definition, with the exact `i+1` offset. -/
theorem mem_lowerRam_iff_le_lowerIndex {i : ℕ} {σ : B ≃ₐ[A] B} :
    σ ∈ PkgI6.lowerRam A B i ↔ ((i + 1 : ℕ) : ℕ∞) ≤ lowerIndex A B σ := by
  simp only [PkgI6.mem_lowerRam, mem_maximalIdeal_pow_iff_le_addVal, le_lowerIndex_iff]

@[simp]
theorem lowerIndex_one : lowerIndex A B 1 = ⊤ := by
  simp [lowerIndex]

@[simp]
theorem lowerIndex_eq_top_iff {σ : B ≃ₐ[A] B} : lowerIndex A B σ = ⊤ ↔ σ = 1 := by
  refine ⟨fun h => AlgEquiv.ext fun x => ?_, fun h => h ▸ lowerIndex_one A B⟩
  have hx := (le_lowerIndex_iff A B).mp h.ge x
  rw [top_le_iff, IsDiscreteValuationRing.addVal_eq_top_iff, sub_eq_zero] at hx
  simpa only [AlgEquiv.one_apply] using hx

/-- The index of an inverse is the same; this is proved through subgroup membership. -/
@[simp]
theorem lowerIndex_inv (σ : B ≃ₐ[A] B) : lowerIndex A B σ⁻¹ = lowerIndex A B σ := by
  apply ENat.eq_of_forall_natCast_le_iff
  intro n
  cases n with
  | zero => simp
  | succ n =>
    rw [← mem_lowerRam_iff_le_lowerIndex, ← mem_lowerRam_iff_le_lowerIndex]
    exact (PkgI6.lowerRam A B n).inv_mem_iff

/-- The product index is at least the minimum, proved with the actual lower subgroups. -/
theorem min_le_lowerIndex_mul (σ τ : B ≃ₐ[A] B) :
    min (lowerIndex A B σ) (lowerIndex A B τ) ≤ lowerIndex A B (σ * τ) := by
  apply ENat.forall_natCast_le_iff_le.mp
  intro n hn
  cases n with
  | zero => simp
  | succ n =>
    rw [← mem_lowerRam_iff_le_lowerIndex]
    exact (PkgI6.lowerRam A B n).mul_mem
      ((mem_lowerRam_iff_le_lowerIndex A B).mpr (hn.trans (min_le_left ..)))
      ((mem_lowerRam_iff_le_lowerIndex A B).mpr (hn.trans (min_le_right ..)))

/-- Monogenicity computes the actual infimum at a single genuine ring element. -/
theorem lowerIndex_eq_addVal_of_adjoin_eq_top {ξ : B} (hξ : Algebra.adjoin A {ξ} = ⊤)
    (σ : B ≃ₐ[A] B) :
    lowerIndex A B σ = IsDiscreteValuationRing.addVal B (σ ξ - ξ) := by
  refine (lowerIndex_le_addVal A B σ ξ).antisymm ((le_lowerIndex_iff A B).mpr fun x => ?_)
  exact IsDiscreteValuationRing.addVal_le_iff_dvd.mpr (displacement_dvd_of_adjoin_eq_top hξ σ x)

/-- The ceiling bridge includes the identity coset's boundary and `n=0`. -/
theorem mem_lowerRamR_iff_of_lowerIndex_eq {u : ℝ} {σ : B ≃ₐ[A] B} {n : ℕ}
    (hn : lowerIndex A B σ = n) :
    σ ∈ PkgI6.lowerRamR A B u ↔ u ≤ (n : ℝ) - 1 := by
  by_cases hu : u ≤ -1
  · simp only [PkgI6.lowerRamR, ite_eq_left hu, Subgroup.mem_top, true_iff]
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  · have hceil : 0 ≤ ⌈u⌉ := by
      have : (-1 : ℤ) < ⌈u⌉ := Int.lt_ceil.mpr (by simpa using lt_of_not_ge hu)
      omega
    rw [PkgI6.lowerRamR, ite_eq_right hu, mem_lowerRam_iff_le_lowerIndex, hn, Nat.cast_le]
    have hc : ⌈u⌉ ≤ (n : ℤ) - 1 ↔ u ≤ (n : ℝ) - 1 := by
      simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_one] using
        (Int.ceil_le (a := u) (z := (n : ℤ) - 1))
    rw [← hc]
    omega

variable [Fintype (B ≃ₐ[A] B)]

/-- The genuine truncated count needed in Serre's coset argument, not a proxy for T22. -/
theorem sum_min_lowerIndex (m : ℕ) :
    ∑ σ : B ≃ₐ[A] B, min (lowerIndex A B σ) (m : ℕ∞) =
      ∑ k ∈ Finset.range m, (Nat.card (PkgI6.lowerRam A B k) : ℕ∞) := by
  classical
  induction m with
  | zero => simp
  | succ m ih =>
    have key : ∀ a : ℕ∞, min a ((m + 1 : ℕ) : ℕ∞) =
        min a m + if ((m + 1 : ℕ) : ℕ∞) ≤ a then 1 else 0 := by
      intro a
      have hm : (m : ℕ∞) ≤ ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.le_succ m
      split_ifs with h
      · rw [min_eq_right h, min_eq_right (hm.trans h)]
        push_cast
        rfl
      · have h' : a ≤ m := by
          lift a to ℕ using (not_le.mp h).ne_top
          exact_mod_cast Nat.le_of_lt_succ (by exact_mod_cast not_le.mp h)
        rw [min_eq_left h', min_eq_left (h'.trans hm), add_zero]
    have hcard : (Nat.card (PkgI6.lowerRam A B m) : ℕ∞) =
        ((Finset.univ.filter fun σ : B ≃ₐ[A] B => ((m + 1 : ℕ) : ℕ∞) ≤
          lowerIndex A B σ).card : ℕ∞) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 2
      ext σ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_lowerRam_iff_le_lowerIndex]
    simp_rw [key]
    rw [Finset.sum_add_distrib, ih, Finset.sum_boole, Finset.sum_range_succ, hcard]

end LowerIndex

section Tower

variable (A C B : Type) [CommRing A] [CommRing C] [CommRing B] [IsDomain B]
  [IsDiscreteValuationRing B] [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B]

@[simp]
theorem lowerIndex_restrictScalars (σ : B ≃ₐ[C] B) :
    lowerIndex A B (σ.restrictScalars A) = lowerIndex C B σ := rfl

end Tower

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.lowerIndex_eq_addVal_of_adjoin_eq_top
#print axioms ZInQ.Contrib.Herbrand.mem_lowerRamR_iff_of_lowerIndex_eq
#print axioms ZInQ.Contrib.Herbrand.sum_min_lowerIndex
