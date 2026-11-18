import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-! The two parities in (O.3), tex 8505–8511 and 8532–8534. -/

namespace ZInQ.Manuscript.RC.LocalWeights

/-- The roots of unity of the indicated order, obtained by taking the odd-part power
in the cyclic residue group. The construction works in any coefficient domain
with the indicated primitive root. -/
theorem odd_character_exists {p k m : ℕ} [Fact p.Prime]
    {O : Type*} [CommRing O] [IsDomain O] {ζ : O} (hζ : IsPrimitiveRoot ζ (2 ^ k))
    (hp : p ≠ 2) (hcard : Nat.card (ZMod p)ˣ = 2 ^ k * m) (hm : Odd m)
    (s : Oˣ) (hs : s = 1 ∨ s = -1) :
    ∃ α : (ZMod p)ˣ →* Oˣ, α (-1) = s ∧ ∀ u, α u ^ (2 ^ k) = 1 := by
  rcases hs with rfl | rfl
  · exact ⟨1, rfl, fun _ => one_pow _⟩
  have : NeZero (2 ^ k) := ⟨by positivity⟩
  let f : (ZMod p)ˣ →* (ZMod p)ˣ := powMonoidHom m
  have hsize : Nat.card f.range = 2 ^ k := by
    dsimp [f]
    rw [IsCyclic.card_powMonoidHom_range, Nat.gcd_eq_right_iff_dvd.mpr ⟨2 ^ k, by
      rw [hcard, mul_comm]⟩, hcard, Nat.mul_div_cancel _ hm.pos]
  let e : f.range ≃* rootsOfUnity (2 ^ k) O :=
    mulEquivOfCyclicCardEq (hsize.trans hζ.card_rootsOfUnity.symm)
  let α := (rootsOfUnity (2 ^ k) O).subtype.comp (e.toMonoidHom.comp f.rangeRestrict)
  have hα : ∀ u, α u ^ (2 ^ k) = 1 := fun u => (e (f.rangeRestrict u)).property
  refine ⟨α, ?_, hα⟩
  have hne : α (-1) ≠ 1 := by
    intro he
    have he' : f.rangeRestrict (-1) = 1 := e.injective (by simpa only [map_one] using
      (show e (f.rangeRestrict (-1)) = (1 : rootsOfUnity (2 ^ k) O) from Subtype.ext he))
    have he'' := congrArg (fun a : f.range => ((a.val : (ZMod p)ˣ) : ZMod p)) he'
    change ((f (-1)) : ZMod p) = 1 at he''
    simp only [f, powMonoidHom_apply, Units.val_neg, Units.val_one,
      hm.neg_one_pow] at he''
    have htwo : (2 : ZMod p) = 0 := by linear_combination -he''
    exact hp (le_antisymm (Nat.le_of_dvd (by decide : 0 < 2)
      ((CharP.cast_eq_zero_iff (ZMod p) p 2).mp htwo)) (Fact.out : p.Prime).two_le)
  apply Units.ext
  have hsq : ((α (-1) : Oˣ) : O) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, neg_one_sq, map_one, Units.val_one]
  rcases sq_eq_one_iff.mp hsq with h | h
  · exact False.elim (hne (Units.ext h))
  · exact h

/-- In an odd residue field there is a character of two-power order of either prescribed parity.
All values lie among the two-power roots of unity. -/
theorem odd_character_complex {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (s : ℂˣ) (hs : s = 1 ∨ s = -1) :
    ∃ k : ℕ, ∃ α : (ZMod p)ˣ →* ℂˣ, α (-1) = s ∧ ∀ u, α u ^ (2 ^ k) = 1 := by
  obtain ⟨k, m, hm, hc⟩ := Nat.exists_eq_two_pow_mul_odd
    (n := Nat.card (ZMod p)ˣ) Nat.card_pos.ne'
  exact ⟨k, odd_character_exists (Complex.isPrimitiveRoot_exp _ (by positivity)) hp hc hm s hs⟩

/-- At two the trivial character and the mod-four character give the two parities. -/
theorem dyadic_character_exists {O : Type*} [CommRing O]
    (s : Oˣ) (hs : s = 1 ∨ s = -1) :
    ∃ α : (ZMod 4)ˣ →* Oˣ, α (-1) = s ∧ ∀ u, α u ^ 2 = 1 := by
  rcases hs with rfl | rfl
  · exact ⟨1, rfl, fun _ => one_pow _⟩
  let α := (Units.map (Int.castRingHom O).toMonoidHom).comp ZMod.χ₄.toUnitHom
  refine ⟨α, ?_, ?_⟩
  · apply Units.ext
    have he : ((ZMod.χ₄.toUnitHom (-1) : ℤˣ) : ℤ) = -1 := by
      change ZMod.χ₄ ((-1 : ℤ) : ZMod 4) = -1
      rw [ZMod.χ₄_int_eq_if_mod_four]
      decide
    change ((↑(ZMod.χ₄.toUnitHom (-1)) : ℤ) : O) = -1
    rw [he, Int.cast_neg, Int.cast_one]
  · intro u
    have hu : (ZMod.χ₄.toUnitHom u) ^ 2 = 1 := by
      apply Units.ext
      have ht := Int.isUnit_iff.mp (ZMod.χ₄.toUnitHom u).isUnit
      change ((ZMod.χ₄.toUnitHom u : ℤˣ) : ℤ) ^ 2 = 1
      rcases ht with h | h <;> rw [h] <;> decide
    change (Units.map (Int.castRingHom O).toMonoidHom (ZMod.χ₄.toUnitHom u)) ^ 2 = 1
    rw [← map_pow, hu, map_one]

end ZInQ.Manuscript.RC.LocalWeights

open ZInQ.Manuscript.RC.LocalWeights in
#print axioms odd_character_exists
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms odd_character_complex
open ZInQ.Manuscript.RC.LocalWeights in
#print axioms dyadic_character_exists
