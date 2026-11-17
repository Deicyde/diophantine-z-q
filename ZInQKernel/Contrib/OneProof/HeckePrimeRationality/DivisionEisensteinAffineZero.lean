import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.DivisionEisensteinCoprimeFiberMoves

/-!
# The unique zero residue in a coprime affine fibre

The coordinates range over actual Fin p residues. Coprimality supplies a
nonzero affine slope and gives exactly one residue for which a + N r is
zero modulo p; no negative integer label is converted to a natural label.
-/

noncomputable section
set_option autoImplicit false
open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups Matrix

namespace ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure

/-- Exactly one actual residue in an affine coprime fibre has zero p class. -/
theorem exists_unique_affine_zero (p N : ℕ) [Fact p.Prime] (hcop : Nat.Coprime p N) (a : ℤ) :
    ∃! r : Fin p, (p : ℤ) ∣ a + (N : ℤ) * (r : ℕ) := by
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let : NeZero p := ⟨hp.ne'⟩
  have hn : (N : ZMod p) ≠ 0 := ((ZMod.isUnit_iff_coprime N p).mpr hcop.symm).ne_zero
  let R : ZMod p := -(a : ZMod p) / (N : ZMod p)
  let r : Fin p := ⟨R.val, ZMod.val_lt R⟩
  have hr : (a : ZMod p) + (N : ZMod p) * ((r : ℕ) : ZMod p) = 0 := by
    simp only [r, ZMod.natCast_zmod_val]
    dsimp [R]
    field_simp
    ring
  refine ⟨r, ?_, ?_⟩
  · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_natCast] using hr
  · intro s hs
    have hz := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr hs
    push_cast at hz
    have he : ((s : ℕ) : ZMod p) = ((r : ℕ) : ZMod p) := by
      apply mul_left_cancel₀ hn
      linear_combination hz - hr
    have hv := congrArg ZMod.val he
    apply Fin.ext
    simpa only [ZMod.val_natCast, Nat.mod_eq_of_lt s.isLt, Nat.mod_eq_of_lt r.isLt] using hv

end ZInQ.Contrib.HeckePrimeRationality.DivisionEisensteinLowerClosure
