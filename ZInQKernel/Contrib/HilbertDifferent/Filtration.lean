/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the source LICENSE.
Authors: The Tau Ceti contributors

Adapted for this project from TauCetiProject/TauCeti, immutable revision
 a6027b1d24fcb935c53bd5b50d11b40991cda418:
 * Algebra/Group/Subgroup/FiniteFiltration.lean, lines 39–48;
 * RingTheory/Ideal/RamificationGroup.lean, lines 92–94 and 124–156.
The kernel argument is written directly using FaithfulSMul; no new ideal or
ramification-group definition is introduced. See docs/research/t20-hilbert-different.md
for provenance, license and the precise scope of this partial contribution.
-/
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.Ideal.Pointwise
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.SetLike.Fintype

namespace ZInQ.Contrib.HilbertDifferent

/-- A decreasing filtration with finite first subgroup eventually equals its intersection. -/
theorem exists_forall_subgroup_eq_iInf {G : Type*} [Group G]
    (f : ℕ → Subgroup G) (hf : Antitone f) [Finite (f 0)] :
    ∃ N, ∀ i, N ≤ i → f i = ⨅ j, f j := by
  obtain ⟨N, hN⟩ := WellFoundedLT.antitone_chain_condition
    (f := fun i ↦ (f i).subgroupOf (f 0)) fun _ _ hij ↦ Subgroup.subgroupOf_mono _ (hf hij)
  have hstable (i : ℕ) (hi : N ≤ i) : f i = f N := by
    simpa only [Subgroup.subgroupOf_inj, inf_of_le_left (hf (Nat.zero_le _)), eq_comm] using
      hN i hi
  refine ⟨N, fun i hi ↦ ?_⟩
  rw [hstable i hi, ← hf.iInf_nat_add N]
  simp only [hstable _ (Nat.le_add_left N _), iInf_const]

section IdealPowers

variable {G B : Type*} [Group G] [CommRing B] [MulSemiringAction G B]

/-- The inertia groups of the powers `Q^(i+1)` form a decreasing filtration. -/
theorem powerInertia_antitone (Q : Ideal B) :
    Antitone (fun i : ℕ ↦ (Q ^ (i + 1)).inertia G) := by
  intro i j hij σ hσ x
  exact Ideal.pow_le_pow_right (by omega) (hσ x)

/-- Krull intersection separates a faithful action on a Noetherian domain. -/
theorem iInf_powerInertia_eq_bot [IsNoetherianRing B] [IsDomain B] [FaithfulSMul G B]
    {Q : Ideal B} (hQ : Q ≠ ⊤) :
    (⨅ i : ℕ, (Q ^ (i + 1)).inertia G) = ⊥ := by
  ext σ
  rw [Subgroup.mem_iInf, Subgroup.mem_bot]
  constructor
  · intro hσ
    apply FaithfulSMul.eq_of_smul_eq_smul (α := B)
    intro x
    have hx : σ • x - x ∈ ⨅ n : ℕ, Q ^ n := by
      refine Submodule.mem_iInf _ |>.2 fun n ↦ ?_
      exact Ideal.pow_le_pow_right (Nat.le_succ n) (hσ n x)
    rw [Ideal.iInf_pow_eq_bot_of_isDomain _ hQ, Ideal.mem_bot, sub_eq_zero] at hx
    simpa only [one_smul] using hx
  · rintro rfl
    exact fun i ↦ ((Q ^ (i + 1)).inertia G).one_mem

/-- With finite inertia, the separated filtration is trivial at every sufficiently large index.
This statement requires neither a complete ring nor a local ring. -/
theorem exists_forall_powerInertia_eq_bot [IsNoetherianRing B] [IsDomain B]
    [FaithfulSMul G B] {Q : Ideal B} (hQ : Q ≠ ⊤) [Finite (Q.inertia G)] :
    ∃ N : ℕ, ∀ i, N ≤ i → (Q ^ (i + 1)).inertia G = ⊥ := by
  have : Finite ((Q ^ (0 + 1)).inertia G) := by simpa only [zero_add, pow_one]
  obtain ⟨N, hN⟩ := exists_forall_subgroup_eq_iInf
    (fun i : ℕ ↦ (Q ^ (i + 1)).inertia G) (powerInertia_antitone Q)
  exact ⟨N, fun i hi ↦ (hN i hi).trans (iInf_powerInertia_eq_bot hQ)⟩

end IdealPowers

end ZInQ.Contrib.HilbertDifferent
