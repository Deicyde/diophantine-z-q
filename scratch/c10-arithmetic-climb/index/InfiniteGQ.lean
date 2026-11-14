/-
climb/infinite-gq — I-G2: `ℚ̄/ℚ` is not finite, `G_ℚ` is infinite, and the ACTUAL trivial-`jj`
counterexample (`range jj = ⊥`, index `0`, cast `0`).

Status of the pinned library (checked by exact path, 56a005855ea1): there is no
`¬ FiniteDimensional ℚ (AlgebraicClosure ℚ)` and no `Infinite (Field.absoluteGaloisGroup ℚ)`.
So the degree growth is proved here, from pinned lemmas only:

  `Polynomial.cyclotomic.irreducible_rat`  (RingTheory/Polynomial/Cyclotomic/Roots.lean:190)
  `Polynomial.cyclotomic.monic`, `Polynomial.natDegree_cyclotomic`
  `Nat.exists_infinite_primes`, `Nat.totient_prime`
  `IsAlgClosed.exists_root`, `minpoly.eq_of_irreducible_of_monic`
  `IntermediateField.adjoin.finrank` (IntermediateField/Adjoin/Basic.lean:495)
  `IntermediateField.fixingSubgroup_top`, `Subgroup.index_bot`

Route: for every `d` pick a prime `p ≥ d + 2`; `cyclotomic p ℚ` is monic irreducible of degree
`φ p = p - 1 > d`; it has a root `x ∈ ℚ̄`; so `ℚ⟮x⟯` has `ℚ`-rank `p - 1 > d`. A finite-dimensional
`ℚ̄` would bound every such rank by `finrank ℚ ℚ̄`. Hence `¬ FiniteDimensional ℚ ℚ̄`, hence
`finrank ℚ ℚ̄ = 0`, hence (reusing the already-proved index transport
`ClimbGaloisIndex.index_eq_zero_of_not_finiteDimensional`) the fixing subgroup of `⊤` — which is
`⊥` — has index `0`, so `Nat.card G_ℚ = 0` and `G_ℚ` is infinite, and the trivial map into `G_ℚ`
is an ACTUAL `jj` with `range jj = ⊥` whose index casts to `0`.

No `θ`/`j`/reverse-map/range construction (120c/40a own that), no normal `C`/`χ`/`L`/`A` data, no
finite-Tate hypothesis. Published `GaloisIndex.lean` (758b632c…) is imported read-only and
unchanged.
-/

import GaloisIndex
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

namespace ClimbInfiniteGQ

open ClimbGaloisIndex Polynomial

/-! ## 1. Arbitrarily large finite degrees inside `ℚ̄` -/

/-- For every `d` there is an `x ∈ ℚ̄` with `[ℚ⟮x⟯ : ℚ] > d`: take a root of `cyclotomic p ℚ`
for a prime `p ≥ d + 2`. -/
theorem exists_adjoin_finrank_gt (d : ℕ) :
    ∃ x : Qbar, d < Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) := by
  obtain ⟨p, hdp, hp⟩ := Nat.exists_infinite_primes (d + 2)
  have hppos : 0 < p := hp.pos
  have hirr : Irreducible (cyclotomic p ℚ) := cyclotomic.irreducible_rat hppos
  have hmonic : (cyclotomic p ℚ).Monic := cyclotomic.monic p ℚ
  have hdeg : (cyclotomic p ℚ).natDegree = p - 1 := by
    rw [natDegree_cyclotomic, Nat.totient_prime hp]
  have hmapnat : ((cyclotomic p ℚ).map (algebraMap ℚ Qbar)).natDegree ≠ 0 := by
    rw [natDegree_map, hdeg]
    omega
  have hmapdeg : ((cyclotomic p ℚ).map (algebraMap ℚ Qbar)).degree ≠ 0 := fun h =>
    hmapnat (natDegree_eq_zero_iff_degree_le_zero.mpr (le_of_eq h))
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hmapdeg
  have haeval : (aeval x) (cyclotomic p ℚ) = 0 := by
    rw [aeval_def, ← eval_map]
    exact hx
  have hmin : minpoly ℚ x = cyclotomic p ℚ :=
    (minpoly.eq_of_irreducible_of_monic hirr haeval hmonic).symm
  have hint : IsIntegral ℚ x := ⟨cyclotomic p ℚ, hmonic, haeval⟩
  refine ⟨x, ?_⟩
  rw [IntermediateField.adjoin.finrank hint, hmin, hdeg]
  omega

/-! ## 2. `ℚ̄/ℚ` is not finite-dimensional -/

/-- **`¬ FiniteDimensional ℚ ℚ̄`.** -/
theorem not_finiteDimensional_qbar : ¬ FiniteDimensional ℚ Qbar := by
  intro h
  obtain ⟨x, hx⟩ := exists_adjoin_finrank_gt (Module.finrank ℚ Qbar)
  have hle : Module.finrank ℚ (IntermediateField.adjoin ℚ {x}) ≤ Module.finrank ℚ Qbar :=
    Submodule.finrank_le (IntermediateField.adjoin ℚ {x}).toSubmodule
  omega

/-- Hence the rank is `0` by the `Module.finrank` convention. -/
theorem finrank_qbar_eq_zero : Module.finrank ℚ Qbar = 0 :=
  Module.finrank_of_infinite_dimensional not_finiteDimensional_qbar

/-- `⊤` as an intermediate field is not finite-dimensional either. -/
theorem not_finiteDimensional_top :
    ¬ FiniteDimensional ℚ (⊤ : IntermediateField ℚ Qbar) := by
  intro h
  have := h
  exact not_finiteDimensional_qbar
    (LinearEquiv.finiteDimensional
      (IntermediateField.topEquiv (F := ℚ) (E := Qbar)).toLinearEquiv)

/-! ## 3. `G_ℚ` is infinite, and the ACTUAL trivial-`jj` counterexample -/

/-- The fixing subgroup of `⊤` has index `0`: the already-proved index transport, at an
infinite-dimensional intermediate field that is now CONSTRUCTED, not hypothetical. -/
theorem index_fixingSubgroup_top_eq_zero :
    (⊤ : IntermediateField ℚ Qbar).fixingSubgroup.index = 0 :=
  index_eq_zero_of_not_finiteDimensional ⊤ not_finiteDimensional_top

/-- …and that subgroup is `⊥`, so `⊥ ≤ G_ℚ` has index `0`. -/
theorem index_bot_eq_zero : (⊥ : Subgroup GQ).index = 0 := by
  rw [← IntermediateField.fixingSubgroup_top (F := ℚ) (E := Qbar)]
  exact index_fixingSubgroup_top_eq_zero

/-- **`G_ℚ` is infinite.** -/
theorem infinite_GQ : Infinite GQ := by
  have h : Nat.card GQ = 0 := by
    rw [← Subgroup.index_bot]
    exact index_bot_eq_zero
  rcases Nat.card_eq_zero.mp h with hempty | hinf
  · exact absurd (hempty.false (1 : GQ)) not_false
  · exact hinf

/-- **The actual trivial-`jj` counterexample.** For the trivial homomorphism into `G_ℚ` the range
is `⊥`, its index is `0`, and the cast is `0` in every field: no `hidx` can be obtained from such
a `jj`. This is a CONSTRUCTED instance, not a conditional statement. -/
theorem trivial_jj_index_zero {Γ : Type*} [Group Γ] :
    MonoidHom.range (1 : Γ →* GQ) = ⊥ ∧ (MonoidHom.range (1 : Γ →* GQ)).index = 0 := by
  constructor
  · exact MonoidHom.range_one
  · rw [MonoidHom.range_one]
    exact index_bot_eq_zero

theorem trivial_jj_cast_zero {Γ : Type*} [Group Γ] (k : Type*) [Field k] :
    (((MonoidHom.range (1 : Γ →* GQ)).index : ℕ) : k) = 0 := by
  rw [(trivial_jj_index_zero (Γ := Γ)).2, Nat.cast_zero]

/-! ## 4. Checks -/

#check @not_finiteDimensional_qbar
#check @finrank_qbar_eq_zero
#check @infinite_GQ
#check @trivial_jj_index_zero
#check @trivial_jj_cast_zero

#print axioms exists_adjoin_finrank_gt
#print axioms not_finiteDimensional_qbar
#print axioms finrank_qbar_eq_zero
#print axioms not_finiteDimensional_top
#print axioms index_fixingSubgroup_top_eq_zero
#print axioms index_bot_eq_zero
#print axioms infinite_GQ
#print axioms trivial_jj_index_zero
#print axioms trivial_jj_cast_zero

end ClimbInfiniteGQ
