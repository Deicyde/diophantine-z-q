import IntegralCongruencePowersQuadratic

/-!
# Finite matrix congruence kernels

The kernel modulo ell of matrices over the genuine ring Z/(ell^(n+1))
has exponent dividing ell^n. In particular it is an ell-group, also
when ell is two.
-/

noncomputable section
set_option autoImplicit false
set_option linter.style.haveILetI false

namespace IntegralCongruence

open Matrix

variable {d : Type*} [Fintype d] [DecidableEq d]

def finiteReduction (ell n : ℕ) [Fact ell.Prime] :
    GL d (ZMod (ell ^ (n + 1))) →* GL d (ZMod ell) :=
  Matrix.GeneralLinearGroup.map
    (ZMod.castHom (dvd_pow_self ell (Nat.succ_ne_zero n)) (ZMod ell))

theorem finite_kernel_principal (ell n : ℕ) [Fact ell.Prime]
    (g : (finiteReduction (d := d) ell n).ker) :
    ∃ B : Matrix d d (ZMod (ell ^ (n + 1))),
      (g.1 : Matrix d d (ZMod (ell ^ (n + 1)))) = 1 + (ell : Matrix d d _) * B := by
  classical
  haveI : NeZero (ell ^ (n + 1)) := ⟨pow_ne_zero _ (Fact.out : ell.Prime).ne_zero⟩
  let A : Matrix d d (ZMod (ell ^ (n + 1))) := (g.1 : Matrix d d _)
  let D := A - 1
  have hD : ∀ i j, (D i j).val % ell = 0 := by
    intro i j
    have hg := congrArg (fun u : GL d (ZMod ell) => (u : Matrix d d (ZMod ell)) i j) g.2
    have hz : ZMod.castHom (dvd_pow_self ell (Nat.succ_ne_zero n)) (ZMod ell) (D i j) = 0 := by
      dsimp only [D]
      rw [Matrix.sub_apply, map_sub]
      apply sub_eq_zero.mpr
      by_cases hij : i = j
      · simpa [A, finiteReduction, Matrix.one_apply, hij] using hg
      · simpa [A, finiteReduction, Matrix.one_apply, hij] using hg
    rw [ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.natCast_eq_zero_iff] at hz
    exact Nat.mod_eq_zero_of_dvd hz
  let B : Matrix d d (ZMod (ell ^ (n + 1))) := fun i j => ((D i j).val / ell : ℕ)
  have hprod : (ell : Matrix d d (ZMod (ell ^ (n + 1)))) * B = D := by
    ext i j
    change ((ell : Matrix d d (ZMod (ell ^ (n + 1)))) * B) i j = D i j
    rw [← nsmul_eq_mul]
    change ell • (B i j) = D i j
    rw [nsmul_eq_mul]
    change (ell : ZMod (ell ^ (n + 1))) * (((D i j).val / ell : ℕ) : ZMod _) = D i j
    rw [← Nat.cast_mul, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (hD i j)), ZMod.natCast_zmod_val]
  exact ⟨B, by rw [hprod]; dsimp [D]; abel⟩

theorem finite_kernel_isPGroup (ell n : ℕ) [Fact ell.Prime] :
    IsPGroup ell (finiteReduction (d := d) ell n).ker := by
  intro g
  obtain ⟨B, hB⟩ := finite_kernel_principal ell n g
  refine ⟨n, Subtype.ext ?_⟩
  exact principal_unit_power ell n
    (by
      rw [← Nat.cast_pow]
      ext i j
      simp [Matrix.natCast_apply, CharP.cast_eq_zero]) g.1 B hB

#check finite_kernel_principal
#check finite_kernel_isPGroup
#print axioms finite_kernel_principal
#print axioms finite_kernel_isPGroup

end IntegralCongruence
