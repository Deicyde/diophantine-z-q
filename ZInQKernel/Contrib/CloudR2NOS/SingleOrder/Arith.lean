/-
# H5 / NOS round 2, lane 1: the single-order counting contradiction (Mathlib only)

Derived from the counting step (`key_ineq` and the final `omega`) of
`P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_abelianSchemePropertyBundle_of_neronModelPropertyBundle_of_forall_specMap_comp_eq_self.lean`
in `anthropics/fermats-last-theorem` at revision `6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright 2026 Anthropic, PBC. Licensed under the Apache License, Version 2.0; see the
`LICENSE`/`NOTICE` files shipped with this contribution.

NOTICE OF MODIFICATION (Apache-2.0 §4(b)), 2026-11-14. The source chooses the prime power
`ℓ ^ c` of ONE fixed prime `ℓ` and compares `ℓ ^ (2 * d * c)` with `c * ℓ ^ (c * (2 * d - 1))`.
This file replaces that choice by ONE arbitrary order `m > c` (no primality, no tower, no
divisibility closure) and isolates:
* the pure arithmetic inequality `c * m ^ (2 * d - 1) < m ^ (2 * d)` for `c < m`, `0 < d`;
* the abstract counting contradiction for one order (an injection `Fin (m ^ (2 * d)) → T`
  into a finite `T` with `Nat.card T ≤ c * m ^ (2 * d - 1)` forces `m ≤ c`);
* the extraction, from an infinite set of the exact shape
  `{m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ P m}` used by the original target, of one order
  `m > c` satisfying every original guard, together with `(m : residue field) ≠ 0`;
* the finite/admissible-order contradiction at those fixed guards against ONE uniform
  bound `∃ c, ∀ m, (m : k) ≠ 0 → …` (quantifier order `∃ c, ∀ m`).
No geometric statement, Néron-model premise or inertia hypothesis is assumed here.
-/
import Mathlib

set_option autoImplicit false

namespace ZInQ.Contrib.CloudR2NOS.SingleOrder

/-- Pure arithmetic: for `c < m` and `0 < d`, `c * m ^ (2 * d - 1) < m ^ (2 * d)`. -/
theorem mul_pow_two_mul_sub_one_lt_pow {c m d : ℕ} (hcm : c < m) (hd : 0 < d) :
    c * m ^ (2 * d - 1) < m ^ (2 * d) := by
  have hm : 0 < m := lt_of_le_of_lt (Nat.zero_le c) hcm
  have hpos : 0 < m ^ (2 * d - 1) := pow_pos hm _
  have hlt : c * m ^ (2 * d - 1) < m * m ^ (2 * d - 1) :=
    Nat.mul_lt_mul_of_pos_right hcm hpos
  have hexp : m * m ^ (2 * d - 1) = m ^ (2 * d) := by
    rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ 2 * d)]
  exact hexp ▸ hlt

/-- One order: an injection of `Fin (m ^ (2 * d))` into a finite type whose cardinality is
at most `c * m ^ (2 * d - 1)` forces `m ≤ c` (for `0 < d`). -/
theorem le_of_injective_of_natCard_le {T : Type*} [Finite T] {c m d : ℕ} (hd : 0 < d)
    {r : Fin (m ^ (2 * d)) → T} (hr : Function.Injective r)
    (hT : Nat.card T ≤ c * m ^ (2 * d - 1)) : m ≤ c := by
  by_contra h
  have hcm : c < m := Nat.lt_of_not_le h
  have h1 : m ^ (2 * d) ≤ Nat.card T := by
    have := Nat.card_le_card_of_injective r hr
    simpa using this
  have h2 := mul_pow_two_mul_sub_one_lt_pow hcm hd
  omega

/-- The same, stated as the contradiction used for a single chosen order `m > c`. -/
theorem false_of_injective_of_natCard_le {T : Type*} [Finite T] {c m d : ℕ} (hd : 0 < d)
    (hcm : c < m) {r : Fin (m ^ (2 * d)) → T} (hr : Function.Injective r)
    (hT : Nat.card T ≤ c * m ^ (2 * d - 1)) : False :=
  absurd (le_of_injective_of_natCard_le hd hr hT) (Nat.not_le.mpr hcm)

/-- Every order admitting such an injection against one uniform bound is at most `c`. -/
theorem subset_Iic_of_forall_injective {S : Set ℕ} {d c : ℕ} (hd : 0 < d)
    (T : ℕ → Type*) (hfin : ∀ m ∈ S, Finite (T m))
    (hbound : ∀ m ∈ S, Nat.card (T m) ≤ c * m ^ (2 * d - 1))
    (hinj : ∀ m ∈ S, ∃ r : Fin (m ^ (2 * d)) → T m, Function.Injective r) :
    S ⊆ Set.Iic c := by
  intro m hmS
  have := hfin m hmS
  obtain ⟨r, hr⟩ := hinj m hmS
  exact le_of_injective_of_natCard_le hd hr (hbound m hmS)

/-- Consequently such a set of orders is finite. -/
theorem finite_of_forall_injective {S : Set ℕ} {d c : ℕ} (hd : 0 < d)
    (T : ℕ → Type*) (hfin : ∀ m ∈ S, Finite (T m))
    (hbound : ∀ m ∈ S, Nat.card (T m) ≤ c * m ^ (2 * d - 1))
    (hinj : ∀ m ∈ S, ∃ r : Fin (m ^ (2 * d)) → T m, Function.Injective r) :
    S.Finite :=
  (Set.finite_Iic c).subset (subset_Iic_of_forall_injective hd T hfin hbound hinj)

/-- An infinite set of natural numbers contains an element above any bound. -/
theorem exists_mem_gt_of_infinite {S : Set ℕ} (hS : S.Infinite) (c : ℕ) :
    ∃ m ∈ S, c < m :=
  hS.exists_gt c

/-- Guard extraction at the exact shape of the original target's set of orders: for any
commutative ring `O` and any order predicate `P`, an infinite
`{m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ P m}` contains ONE order `m > c` with every guard. -/
theorem exists_gt_of_infinite_setOf {O : Type*} [CommRing O] {P : ℕ → Prop}
    (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ P m}.Infinite) (c : ℕ) :
    ∃ m : ℕ, c < m ∧ 0 < m ∧ IsUnit (m : O) ∧ P m := by
  obtain ⟨m, ⟨hm0, hmu, hP⟩, hcm⟩ := hS.exists_gt c
  exact ⟨m, hcm, hm0, hmu, hP⟩

/-- An order invertible in a local ring has nonzero image in its residue field. -/
theorem natCast_residue_ne_zero {R : Type*} [CommRing R] [IsLocalRing R] {m : ℕ}
    (hm : IsUnit (m : R)) : (m : IsLocalRing.ResidueField R) ≠ 0 := by
  have h := hm.map (IsLocalRing.residue R)
  rw [map_natCast] at h
  exact h.ne_zero

/-- An order invertible in a ring has nonzero image in any nontrivial algebra over it. -/
theorem natCast_algebraMap_ne_zero {R k : Type*} [CommRing R] [Field k] [Algebra R k] {m : ℕ}
    (hm : IsUnit (m : R)) : (m : k) ≠ 0 := by
  have h := hm.map (algebraMap R k)
  rw [map_natCast] at h
  exact h.ne_zero

/-- Guard extraction with the residue condition needed by the uniform special-fibre bound. -/
theorem exists_gt_residue_ne_zero_of_infinite_setOf {O : Type*} [CommRing O] [IsLocalRing O]
    {P : ℕ → Prop} (hS : {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ P m}.Infinite) (c : ℕ) :
    ∃ m : ℕ, c < m ∧ 0 < m ∧ IsUnit (m : O) ∧ P m ∧
      (m : IsLocalRing.ResidueField O) ≠ 0 := by
  obtain ⟨m, hcm, hm0, hmu, hP⟩ := exists_gt_of_infinite_setOf hS c
  exact ⟨m, hcm, hm0, hmu, hP, natCast_residue_ne_zero hmu⟩

/-- **Finite/admissible-order contradiction at the fixed original guards.**
Let `T m` be (say) the special-fibre `m`-torsion. Suppose ONE uniform constant `c` bounds
`Nat.card (T m) ≤ c * m ^ (2 * d - 1)` for every order with nonzero residue (the nonproper
branch of the special-fibre alternative), and every order satisfying the original guards
`0 < m`, `IsUnit (m : O)`, `P m` admits an injection `Fin (m ^ (2 * d)) → T m` (the
single-order specialization injection). Then the set of guarded orders is NOT infinite. -/
theorem not_infinite_setOf_of_uniform_bound {O : Type*} [CommRing O] [IsLocalRing O]
    {P : ℕ → Prop} {d c : ℕ} (hd : 0 < d) (T : ℕ → Type*)
    (hbound : ∀ m : ℕ, (m : IsLocalRing.ResidueField O) ≠ 0 →
      Finite (T m) ∧ Nat.card (T m) ≤ c * m ^ (2 * d - 1))
    (hinj : ∀ m : ℕ, 0 < m → IsUnit (m : O) → P m →
      ∃ r : Fin (m ^ (2 * d)) → T m, Function.Injective r) :
    ¬ {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ P m}.Infinite := by
  intro hS
  obtain ⟨m, hcm, hm0, hmu, hP, hres⟩ := exists_gt_residue_ne_zero_of_infinite_setOf hS c
  obtain ⟨hfin, hcard⟩ := hbound m hres
  have := hfin
  obtain ⟨r, hr⟩ := hinj m hm0 hmu hP
  exact false_of_injective_of_natCard_le hd hcm hr hcard

/-- The stronger conditional form: under the same two inputs, every guarded order is at
most the fixed constant `c`; so the guarded set is finite. -/
theorem setOf_finite_of_uniform_bound {O : Type*} [CommRing O] [IsLocalRing O]
    {P : ℕ → Prop} {d c : ℕ} (hd : 0 < d) (T : ℕ → Type*)
    (hbound : ∀ m : ℕ, (m : IsLocalRing.ResidueField O) ≠ 0 →
      Finite (T m) ∧ Nat.card (T m) ≤ c * m ^ (2 * d - 1))
    (hinj : ∀ m : ℕ, 0 < m → IsUnit (m : O) → P m →
      ∃ r : Fin (m ^ (2 * d)) → T m, Function.Injective r) :
    {m : ℕ | 0 < m ∧ IsUnit (m : O) ∧ P m} ⊆ Set.Iic c := by
  rintro m ⟨hm0, hmu, hP⟩
  obtain ⟨hfin, hcard⟩ := hbound m (natCast_residue_ne_zero hmu)
  have := hfin
  obtain ⟨r, hr⟩ := hinj m hm0 hmu hP
  exact le_of_injective_of_natCard_le hd hr hcard

end ZInQ.Contrib.CloudR2NOS.SingleOrder
