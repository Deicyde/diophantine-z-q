import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.PrimitiveEisensteinUnitSeries

/-!
# Actual unrestricted congruence-grid identification

Canonical residue lifts give a genuine signed integer-grid bijection with
the unrestricted congruence vectors. The actual gcd-normalized primitive
unit convolution therefore holds for the literal translated grid series.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set ModularForm
open scoped Topology Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinGrid

open ZInQ.Contrib.HeckePrimeRationality
open PrimitiveEisensteinGcdData PrimitiveEisensteinNormalization PrimitiveEisensteinUnitSeries

/-- Canonical integer lifts of finite residue coordinates. -/
def residueLift {N : ℕ} (a : Fin 2 → ZMod N) (i : Fin 2) : ℤ := (a i).val

lemma residueLift_cast {N : ℕ} [NeZero N] (a : Fin 2 → ZMod N) (i : Fin 2) :
    (residueLift a i : ZMod N) = a i := by
  simp only [residueLift, Int.cast_natCast, ZMod.natCast_zmod_val]

lemma congruenceSet_dvd_sub_lift (N : ℕ) (hN : 0 < N) (a : Fin 2 → ZMod N)
    (v : congruenceSet N a) (i : Fin 2) : (N : ℤ) ∣ v.1 i - residueLift a i := by
  let _ : NeZero N := ⟨hN.ne'⟩
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp
  have hc : (v.1 i : ZMod N) = a i := congrFun v.2 i
  rw [Int.cast_sub, hc, residueLift_cast, sub_self]

/-- Every actual congruence vector has a unique signed integer-grid representative. -/
def rowGridEquiv (N : ℕ) (hN : 0 < N) (a : Fin 2 → ZMod N) :
    (ℤ × ℤ) ≃ congruenceSet N a := by
  let _ : NeZero N := ⟨hN.ne'⟩
  refine
    { toFun := fun q => ⟨![residueLift a 0 + N*q.1,residueLift a 1 + N*q.2], ?_⟩
      invFun := fun v => ((v.1 0-residueLift a 0)/(N : ℤ),(v.1 1-residueLift a 1)/(N : ℤ))
      left_inv := ?_
      right_inv := ?_ }
  · funext i
    fin_cases i <;>
      simp [Function.comp_apply, Int.cast_add, Int.cast_mul, Int.cast_natCast, residueLift_cast]
  · intro q
    have hNc : (N : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
    apply Prod.ext
    · change (residueLift a 0 + (N : ℤ)*q.1 - residueLift a 0)/(N : ℤ) = q.1
      rw [add_sub_cancel_left]
      exact Int.mul_ediv_cancel_left _ hNc
    · change (residueLift a 1 + (N : ℤ)*q.2 - residueLift a 1)/(N : ℤ) = q.2
      rw [add_sub_cancel_left]
      exact Int.mul_ediv_cancel_left _ hNc
  · intro v
    apply Subtype.ext
    funext i
    fin_cases i
    · have hd := congruenceSet_dvd_sub_lift N hN a v 0
      have h := Int.mul_ediv_cancel' hd
      change residueLift a 0 + (N : ℤ) * ((v.1 0-residueLift a 0)/(N : ℤ)) = v.1 0
      linear_combination h
    · have hd := congruenceSet_dvd_sub_lift N hN a v 1
      have h := Int.mul_ediv_cancel' hd
      change residueLift a 1 + (N : ℤ) * ((v.1 1-residueLift a 1)/(N : ℤ)) = v.1 1
      linear_combination h

lemma rowGridEquiv_apply (N : ℕ) (hN : 0 < N) (a : Fin 2 → ZMod N) (q : ℤ × ℤ) :
    ((rowGridEquiv N hN a) q).1 = ![residueLift a 0+N*q.1,residueLift a 1+N*q.2] := rfl

/-- Literal equality of the unrestricted vector series and the actual translated congruence grid. -/
theorem unrestrictedSeries_eq_grid (N : ℕ) (hN : 0 < N) (a : Fin 2 → ZMod N) (k : ℕ) (τ : ℍ) :
    unrestrictedSeries N a k τ = ∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ)
      ![residueLift a 0+N*q.1,residueLift a 1+N*q.2] τ := by
  exact ((rowGridEquiv N hN a).tsum_eq
    (fun v : congruenceSet N a => EisensteinSeries.eisSummand (k : ℤ) v.1 τ)).symm

/-- The actual translated grid equals the actual primitive value plus the convergent unit tail. -/
theorem grid_eq_primitive_add_tail (N : ℕ) (hN : 3 ≤ N) (a : PrimitiveRow N)
    (k : ℕ) (hk : 3 ≤ k) (τ : ℍ) :
    (∑' q : ℤ × ℤ, EisensteinSeries.eisSummand (k : ℤ)
      ![residueLift a.1 0+N*q.1,residueLift a.1 1+N*q.2] τ) =
      primitiveValues N k τ a + ∑' n : ℕ,
        unitCoefficient N k (n+2) * primitiveValues N k τ (unitPermutation N (n+2) a) := by
  rw [← unrestrictedSeries_eq_grid N (by omega)]
  exact unrestrictedSeries_eq_primitive_add_tail N hN a k hk τ

end ZInQ.Contrib.HeckePrimeRationality.PrimitiveEisensteinGrid
