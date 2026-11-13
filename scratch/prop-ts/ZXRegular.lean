import Mathlib

/-! prop-ts: a building block for `SpecNonMeeting` (docs/research/prop-ts.md §4.1): the local
rings of `ℤ[X]` at the maximal ideals `(p, dX − a)` are regular local of dimension 2, the base of
t-purity3's `purityGlobalDim2'`. Imports Mathlib only. -/

open Polynomial

namespace PropTSZX

/-- A maximal ideal of `ℤ[X]` over a nonzero prime of `ℤ` (e.g. `(p, dX − a)`) has height `2`. -/
theorem height_maximal_intPoly (m : Ideal ℤ[X]) [m.IsMaximal]
    (hne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊥) : m.height = 2 := by
  have hc : (m.comap (C : ℤ →+* ℤ[X])).IsMaximal :=
    Ideal.IsPrime.isMaximal (Ideal.IsPrime.comap _) hne
  have : m.LiesOver (m.comap (C : ℤ →+* ℤ[X])) := ⟨rfl⟩
  rw [Polynomial.height_eq_height_add_one (m.comap (C : ℤ →+* ℤ[X])) m]
  have h1 : (m.comap (C : ℤ →+* ℤ[X])).height = 1 := by
    apply le_antisymm
    · have := Ideal.height_le_ringKrullDim_of_isPrime (I := m.comap (C : ℤ →+* ℤ[X]))
      rw [IsPrincipalIdealRing.ringKrullDim_eq_one ℤ Int.not_isField] at this
      exact_mod_cast this
    · rw [Order.one_le_iff_pos, pos_iff_ne_zero, Ne, Ideal.height_eq_zero_iff_eq_bot]
      exact hne
  rw [h1]
  rfl

/-- **The local rings of `ℤ[X]` at maximal ideals are regular local of dimension `2`** (the
base of the purity argument in `SpecNonMeeting`; with t-purity3's `purityGlobalDim2'`). -/
theorem regular_dim2_intPoly (m : Ideal ℤ[X]) [m.IsMaximal]
    (hne : m.comap (C : ℤ →+* ℤ[X]) ≠ ⊥) :
    IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = 2 := by
  refine ⟨inferInstance, ?_⟩
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height m, height_maximal_intPoly m hne]
  rfl

end PropTSZX

#print axioms PropTSZX.regular_dim2_intPoly
#print axioms PropTSZX.height_maximal_intPoly
