import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.RingTheory.Nilpotent.Basic
import Mathlib.Tactic.LinearCombination

/-!
# Finite quadratic sums for the theta multiplier (provenance (c))

The transformation at a cusp by Poisson summation uses a finite quadratic
sum. The part depending on the top-left entry is invariant under the change
of that entry in a translation conjugate at level divisible by `4m²`.
-/

noncomputable section

namespace ZInQ.Manuscript.RC.HalfIntegral

/-- Quadratic sum with a linear Fourier phase. -/
def quadraticFourier {C : ℕ} [NeZero C] (a n : ZMod C) : ℂ :=
  ∑ x : ZMod C, ZMod.stdAddChar (a * x ^ 2 + n * x)

/-- Completing the square gives the phase of each even Fourier mode. -/
theorem quadraticFourier_even {C : ℕ} [NeZero C] {a d : ZMod C}
    (had : a * d = 1) (n : ZMod C) :
    quadraticFourier a (2 * n) = ZMod.stdAddChar (- (d * n ^ 2)) * quadraticFourier a 0 := by
  rw [quadraticFourier, quadraticFourier, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight (d * n)) _ _ fun x ↦ ?_
  rw [← AddChar.map_add_eq_mul]
  congr 1
  simp only [Equiv.coe_addRight, zero_mul, add_zero]
  linear_combination -(2 * n * x + d * n ^ 2) * had

/-- A change by a unit square leaves the quadratic sum at frequency zero unchanged. -/
theorem quadraticFourier_unit_sq {C : ℕ} [NeZero C] (a : ZMod C) (t : (ZMod C)ˣ) :
    quadraticFourier (a * (t : ZMod C) ^ 2) 0 = quadraticFourier a 0 := by
  refine Fintype.sum_equiv t.mulLeft _ _ fun x ↦ ?_
  congr 1
  simp only [Units.mulLeft_apply]
  ring

/-- With `C = 4m²k`, changing the numerator by `C u / m` does not
change its quadratic sum. The change is multiplication by the square of
`1 + 2mkua⁻¹` in `ℤ/Cℤ`. -/
theorem quadraticFourier_translate (m k : ℕ) [NeZero (4 * (m ^ 2 * k))]
    (a : (ZMod (4 * (m ^ 2 * k)))ˣ) (u : ZMod (4 * (m ^ 2 * k))) :
    quadraticFourier ((a : ZMod (4 * (m ^ 2 * k))) + 4 * (m : ZMod (4 * (m ^ 2 * k))) * (k : ZMod (4 * (m ^ 2 * k))) * u) 0 =
      quadraticFourier (a : ZMod (4 * (m ^ 2 * k))) 0 := by
  let C := 4 * (m ^ 2 * k)
  let x : ZMod C := 2 * m * k * u * (a⁻¹ : (ZMod C)ˣ)
  have hc : (4 * (m : ZMod C) ^ 2 * k) = 0 := by
    calc
      _ = (C : ZMod C) := by dsimp [C]; push_cast; ring
      _ = 0 := ZMod.natCast_self C
  have hx : x ^ 2 = 0 := by
    dsimp [x]
    calc
      _ = (4 * (m : ZMod C) ^ 2 * k) * (k * u ^ 2 * ((a⁻¹ : (ZMod C)ˣ) : ZMod C) ^ 2) := by ring
      _ = 0 := by rw [hc, zero_mul]
  let t := (show IsUnit (1 + x) from (show IsNilpotent x from ⟨2, hx⟩).isUnit_one_add).unit
  have ht : (t : ZMod C) = 1 + x := IsUnit.unit_spec _
  have ha : (a : ZMod C) * (t : ZMod C) ^ 2 = (a : ZMod C) + 4 * m * k * u := by
    rw [ht, add_sq, one_pow, hx, add_zero, mul_add, mul_one]
    congr 1
    dsimp [x]
    calc
      _ = 4 * m * k * u * ((a : ZMod C) * ((a⁻¹ : (ZMod C)ˣ) : ZMod C)) := by ring
      _ = _ := by simp
  rw [← ha, quadraticFourier_unit_sq]

/-- Translation by half the modulus negates an odd Fourier mode. -/
theorem quadraticFourier_odd (k : ℕ) [NeZero (4 * k)] (a : ZMod (4 * k)) (n : ℤ)
    (hn : Odd n) : quadraticFourier a (n : ZMod (4 * k)) = 0 := by
  let C := 4 * k
  let h : ZMod C := 2 * k
  have hc : 4 * (k : ZMod C) = 0 := by
    calc
      _ = (C : ZMod C) := by dsimp [C]; push_cast; rfl
      _ = 0 := ZMod.natCast_self C
  have hh : 2 * h = 0 := by dsimp [h]; linear_combination hc
  have hs : h ^ 2 = 0 := by dsimp [h]; linear_combination (k : ZMod C) * hc
  have hphase : ZMod.stdAddChar h = -1 := by
    have hk : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by
      intro hk
      exact NeZero.ne C (by simp [C, hk]))
    rw [show h = ((2 * (k : ℤ) : ℤ) : ZMod C) by push_cast; rfl, ZMod.stdAddChar_coe]
    rw [← Complex.exp_pi_mul_I]
    congr 1
    dsimp [C]
    push_cast
    field_simp
    ring
  obtain ⟨j, hj⟩ := hn
  have hnh : (n : ZMod C) * h = h := by
    rw [hj]
    push_cast
    linear_combination (j : ZMod C) * hh
  have hEq : quadraticFourier a (n : ZMod C) =
      -(quadraticFourier a (n : ZMod C)) := by
    unfold quadraticFourier
    rw [← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.addRight h) _ _ fun x ↦ ?_
    have he : a * (x + h) ^ 2 + (n : ZMod C) * (x + h) =
        (a * x ^ 2 + (n : ZMod C) * x) + h := by
      linear_combination a * x * hh + a * hs + hnh
    simp [he, AddChar.map_add_eq_mul, hphase]
  linear_combination hEq / 2

#print axioms quadraticFourier_even
#print axioms quadraticFourier_unit_sq
#print axioms quadraticFourier_translate
#print axioms quadraticFourier_odd

end ZInQ.Manuscript.RC.HalfIntegral
