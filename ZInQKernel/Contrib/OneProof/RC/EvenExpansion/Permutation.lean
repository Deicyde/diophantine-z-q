import Mathlib.Data.ZMod.Units
import Mathlib.Tactic

/-! The finite reindexing of the normalized sum at a fresh prime.
This is the integral part of the comparison in tex 9519–9532. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenExpansion

private theorem fractionalPermutation {R : Type} [CommRing R] [Finite R]
    (a b c d : R) (hdet : a * d - b * c = 1) (hu : ∀ r : R, IsUnit (a + r * c)) :
    ∃ e : Equiv.Perm R, ∀ r : R, (a + r * c) * e r = b + r * d := by
  let f (r : R) : R := ↑((hu r).unit⁻¹) * (b + r * d)
  have hf (r : R) : (a + r * c) * f r = b + r * d := by
    have hh : (a + r * c) * ↑((hu r).unit⁻¹) = 1 := by
      calc
        _ = ((hu r).unit : R) * ↑((hu r).unit⁻¹) :=
          congrArg (fun x : R => x * ↑((hu r).unit⁻¹)) (hu r).unit_spec.symm
        _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    dsimp only [f]
    rw [← mul_assoc, hh, one_mul]
  have hi : Function.Injective f := by
    intro r s e
    have h : (b + r * d) * (a + s * c) - (b + s * d) * (a + r * c) = 0 := by
      rw [← hf r, ← hf s, e]
      ring
    linear_combination h - (r - s) * hdet
  exact ⟨Equiv.ofBijective f hi.bijective_of_finite, hf⟩

/-- The residue (r') in the (U_{p^2}) conjugation is a permutation of
the residues (r). The last equation supplies the integral upper-right
entry of the conjugate matrix. -/
theorem upSquare_permutation {p : ℕ} (hp : p.Prime) (a b c d : ℤ)
    (hdet : a * d - b * c = 1) (hc : (p : ℤ) ∣ c) :
    ∃ e : Equiv.Perm (ZMod (p ^ 2)), ∀ r, ∃ u : ℤ,
      b + (r.val : ℤ) * d =
        (a + (r.val : ℤ) * c) * ((e r).val : ℤ) + (p : ℤ) ^ 2 * u := by
  letI : Fact (1 < p) := ⟨hp.one_lt⟩
  letI : NeZero (p ^ 2) := ⟨pow_ne_zero _ hp.ne_zero⟩
  let π := ZMod.castHom (dvd_pow_self p (by decide : 2 ≠ 0)) (ZMod p)
  have hc0 : (c : ZMod p) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).2 hc
  have ha0 : (a : ZMod p) ≠ 0 := by
    intro ha
    have h : (a : ZMod p) * (d : ZMod p) - (b : ZMod p) * (c : ZMod p) = 1 := by
      simpa using congrArg (Int.castRingHom (ZMod p)) hdet
    simpa [ha, hc0] using h
  have hu (r : ZMod (p ^ 2)) : IsUnit ((a : ZMod (p ^ 2)) + r * (c : ZMod (p ^ 2))) := by
    let x : ZMod (p ^ 2) := (a : ZMod (p ^ 2)) + r * (c : ZMod (p ^ 2))
    change IsUnit x
    rw [← ZMod.natCast_zmod_val x, ZMod.isUnit_natCast_iff_not_dvd_pow hp (by decide)]
    intro hx
    have h0 : π x = 0 := by
      rw [← ZMod.natCast_zmod_val x, map_natCast]
      exact (ZMod.natCast_eq_zero_iff _ _).2 hx
    have hπx : π x = (a : ZMod p) := by
      simp only [x, map_add, map_mul, map_intCast, hc0, mul_zero, add_zero]
    rw [hπx] at h0
    exact ha0 h0
  have hdet' : (a : ZMod (p ^ 2)) * (d : ZMod (p ^ 2)) -
      (b : ZMod (p ^ 2)) * (c : ZMod (p ^ 2)) = 1 := by
    simpa using congrArg (Int.castRingHom (ZMod (p ^ 2))) hdet
  obtain ⟨e, he⟩ := fractionalPermutation _ _ _ _ hdet' hu
  refine ⟨e, fun r => ?_⟩
  have hzero :
      ((b + (r.val : ℤ) * d - (a + (r.val : ℤ) * c) * ((e r).val : ℤ) : ℤ) :
        ZMod (p ^ 2)) = 0 := by
    push_cast
    simp only [ZMod.natCast_zmod_val, ← he r, sub_self]
  obtain ⟨u, hu⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hzero
  refine ⟨u, ?_⟩
  push_cast at hu
  linarith

/-- The integral conjugates have determinant one, stay at the indicated
level and retain the lower-right entry modulo that level. -/
theorem upSquare_conjugation {p : ℕ} (hp : p.Prime) (M a b c d : ℤ)
    (hdet : a * d - b * c = 1) (hc : (p : ℤ) ∣ c) (hM : M ∣ c) :
    ∃ e : Equiv.Perm (ZMod (p ^ 2)), ∀ r, ∃ u : ℤ,
      b + (r.val : ℤ) * d =
        (a + (r.val : ℤ) * c) * ((e r).val : ℤ) + (p : ℤ) ^ 2 * u ∧
      (a + (r.val : ℤ) * c) * (d - c * ((e r).val : ℤ)) - u * ((p : ℤ) ^ 2 * c) = 1 ∧
      M ∣ (p : ℤ) ^ 2 * c ∧ M ∣ (d - c * ((e r).val : ℤ)) - d := by
  obtain ⟨e, he⟩ := upSquare_permutation hp a b c d hdet hc
  refine ⟨e, fun r => ?_⟩
  obtain ⟨u, hu⟩ := he r
  refine ⟨u, hu, ?_, dvd_mul_of_dvd_right hM _, ?_⟩
  · linear_combination hdet + c * hu
  · simpa only [sub_sub_cancel_left] using dvd_neg.mpr (dvd_mul_of_dvd_left hM ((e r).val : ℤ))


end ZInQ.Manuscript.RC.EvenExpansion
