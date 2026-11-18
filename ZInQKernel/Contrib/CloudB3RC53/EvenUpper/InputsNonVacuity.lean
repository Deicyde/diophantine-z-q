import ZInQKernel.Contrib.CloudB3RC53.EvenUpper.RedeiWitness
import ZInQKernel.Contrib.OneProof.RC.Wiring.NonVacuity

/-!
# EvenUpper, part 6: `EvenUpperInputsAt` with a partitionability predicate that is not `False`

Consistency check, not part of the manuscript. RC0's toy interface data `toyW` has
`Partitionable = False`, so every statement quantified over partitionable parameters is vacuous
there. `redeiW ℓ` is `toyW ℓ` with the genuine partitionability predicate of the Rédei witness
(`RedeiWitness.lean`), in the shape of `hspec` of `hcubes_of_dictionary`: `d` squarefree, its
primes good for the sign type data, and the typed graph of its primes partitionable for the Rédei
symbol (all `PROVED`):

* `redeiW_partitionable_three`: `3` is partitionable, so the predicate is not `False`;
* `redeiW_not_partitionable_one`: `1` is not (empty graph), so it is not `True` either;
* `evenUpperInputsAt_redeiW`: `EvenUpperInputsAt (redeiW ℓ)` holds.

Remark: clause (iii) of `EvenUpperInputsAt` allows the unit `x` to be `d` itself; here `L_* = 1`,
so every nonzero parameter satisfies (3.3a) and the base serves as its own unit. An instance with
the unit at a nonzero cube address (`realized_cubes_redei`) would need clause (ii) at that
address, which involves the actual Selmer coranks and `Ш` lengths of the twists `Etw ℓ x`; those are
not computable here.
-/

namespace ZInQ.Contrib.CloudB3RC53.EvenUpper

open ZInQ.Manuscript ZInQ.Manuscript.SelmerTwoPower ZInQ.Manuscript.RC ZInQ.Manuscript.RC.Wiring
  ZInQ.Manuscript.RC.Symbols ZInQ.Contrib.CloudB3RC53.CoefficientDictionary

/-- The Rédei partitionability predicate on parameters. -/
def RedeiPartitionable (d : ℤ) : Prop :=
  Squarefree d ∧ (∀ p ∈ d.natAbs.primeFactors, signTypeData.Good p) ∧
    IsPartitionable (AddMonoidHom.id (ZMod 2)) (symb signTypeData redeiReading)
      (primeConfig d.natAbs.primeFactors signTypeData.typ)

/-- `toyW ℓ` with the Rédei partitionability predicate. -/
noncomputable def redeiW (ℓ : ℕ) : WData ℓ := { toyW ℓ with Partitionable := RedeiPartitionable }

/-- **`3` is partitionable in `redeiW`** (`PROVED`). -/
theorem redeiW_partitionable_three (ℓ : ℕ) : (redeiW ℓ).Partitionable 3 := by
  refine ⟨Int.squarefree_natAbs.mp Nat.prime_three.squarefree, ?_, redei_partitionable_three⟩
  rw [primeFactors_three]
  intro p hp
  rw [Finset.mem_singleton.1 hp]
  exact good_three

/-- **`1` is not partitionable in `redeiW`** (`PROVED`): its typed graph is empty. -/
theorem redeiW_not_partitionable_one (ℓ : ℕ) : ¬ (redeiW ℓ).Partitionable 1 := by
  rintro ⟨-, -, hne, -⟩
  simp [primeConfig] at hne

/-- **`EvenUpperInputsAt` for `redeiW`** (`PROVED`). -/
theorem evenUpperInputsAt_redeiW (ℓ : ℕ) : EvenUpperInputsAt (redeiW ℓ) := by
  have hL : ∀ p, (redeiW ℓ).Lstar p = 1 := fun _ => rfl
  refine ⟨0, 0, fun d hd0 _ _ => ?_⟩
  refine ⟨fun p => p ≠ 0 ∧ (redeiW ℓ).Lstar p ≠ 0 ∧
      padicValRat 2 ((redeiW ℓ).Lstar p) ≤ 2 * omega p + 0,
    fun p => (2 : ℚ_[2]) ^ (-(2 * (omega p : ℤ) + (shaLength (Etw ℓ p) : ℤ))),
    fun p hp => hp, fun p _ _ => ?_, d, ⟨hd0, ?_, ?_⟩, Or.inl rfl⟩
  · rw [hL]
    refine ⟨⟨fun h => absurd h (zpow_ne_zero _ two_ne_zero), fun h => absurd h one_ne_zero⟩,
      fun _ => ?_⟩
    rw [Padic.valuation_zpow]
    have h2 : (2 : ℚ_[2]).valuation = 1 := by simp
    rw [h2, padicValRat.one, mul_one]
    have h0 : ∀ a b : ℤ, -(2 * a + b) - (0 - 2 * a - b) = 0 := fun a b => by ring
    rw [h0, abs_zero]
  · rw [hL]; exact one_ne_zero
  · rw [hL, padicValRat.one]
    have : (0 : ℤ) ≤ omega d := Int.natCast_nonneg _
    omega

end ZInQ.Contrib.CloudB3RC53.EvenUpper
