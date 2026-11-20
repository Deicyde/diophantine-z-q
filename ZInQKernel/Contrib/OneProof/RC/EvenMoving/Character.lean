import ZInQKernel.Contrib.OneProof.RC.PrintsAnalytic.Basic
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! The positive-prime quadratic character on the common level, tex 9510–9512. -/

noncomputable section

namespace ZInQ.Manuscript.RC.EvenMoving

open PrintsAnalytic

theorem kronecker_of_odd (D : ℤ) {n : ℕ} (hn : Odd n) :
    kronecker D n = jacobiSym D n := by
  have hfac : n.factorization 2 = 0 := Nat.factorization_eq_zero_of_not_dvd (by
    rcases hn with ⟨k, hk⟩
    omega)
  simp [kronecker, hfac]

/-- The character with values `(p/n)` on units, with its sign at four
obtained by quadratic reciprocity. -/
def primeCharacter {m p : ℕ} [Fact p.Prime] (h4 : 4 ∣ m) (hp : p ∣ m) :
    DirichletCharacter ℂ m :=
  let q : DirichletCharacter ℂ p := (quadraticChar (ZMod p)).ringHomComp (Int.castRingHom ℂ)
  let s : DirichletCharacter ℂ 4 := ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)
  if p % 4 = 3 then q.changeLevel hp * s.changeLevel h4 else q.changeLevel hp

private theorem primeCharacter_int {m p : ℕ} [Fact p.Prime] (h4 : 4 ∣ m) (hp : p ∣ m)
    {d : ℤ} (hd : IsCoprime d (m : ℤ)) :
    primeCharacter h4 hp (d : ZMod m) =
      ((legendreSym p d * (if p % 4 = 3 then ZMod.χ₄ (d : ZMod 4) else 1) : ℤ) : ℂ) := by
  unfold primeCharacter
  dsimp only
  split_ifs <;>
    simp only [MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd' _ _ hd,
      Int.cast_mul, mul_one, MulChar.ringHomComp_apply] <;>
    rfl

theorem primeCharacter_nat {m p : ℕ} [Fact p.Prime] (h4 : 4 ∣ m) (hp : p ∣ m)
    (hodd : Odd p) {n : ℕ} (hn : n.Coprime m) :
    primeCharacter h4 hp n = (kronecker (p : ℤ) n : ℂ) := by
  have hnodd : Odd n := Nat.coprime_two_right.mp
    (hn.coprime_dvd_right ((by decide : 2 ∣ 4).trans h4))
  have h := jacobiSym.quadratic_reciprocity_if (Nat.odd_iff.mp hodd) (Nat.odd_iff.mp hnodd)
  rw [← jacobiSym.legendreSym.to_jacobiSym] at h
  rw [← Int.cast_natCast (R := ZMod m) n, primeCharacter_int h4 hp hn.isCoprime,
    kronecker_of_odd _ hnodd, ← h]
  push_cast
  split_ifs with hp3 hpn hpn
  · rw [ZMod.χ₄_nat_three_mod_four hpn.2]
    ring
  · have hn1 : n % 4 = 1 := by
      have hn2 := Nat.odd_iff.mp hnodd
      omega
    rw [ZMod.χ₄_nat_one_mod_four hn1]
    ring
  · exact (hp3 hpn.1).elim
  · ring

theorem primeCharacter_neg_one {m p : ℕ} [Fact p.Prime] (h4 : 4 ∣ m) (hp : p ∣ m)
    (hodd : Odd p) : primeCharacter h4 hp (-1) = 1 := by
  have hp2 : p ≠ 2 := fun e => (by decide : ¬ Odd (2 : ℕ)) (e ▸ hodd)
  have hc : IsCoprime (-1 : ℤ) (m : ℤ) := ⟨-1, 0, by ring⟩
  have he := primeCharacter_int h4 hp hc
  push_cast at he
  rw [he, legendreSym.at_neg_one hp2]
  split_ifs with h
  · have hneg : ZMod.χ₄ (-1 : ZMod 4) = -1 := by decide
    rw [ZMod.χ₄_nat_three_mod_four h, hneg]
    norm_num
  · have h' : p % 4 = 1 := by have := Nat.odd_iff.mp hodd; omega
    rw [ZMod.χ₄_nat_one_mod_four h']
    norm_num

theorem primeCharacter_sq {m p : ℕ} [Fact p.Prime] (h4 : 4 ∣ m) (hp : p ∣ m)
    {d : ℤ} (hd : IsCoprime d (m : ℤ)) :
    (primeCharacter h4 hp (d : ZMod m)) ^ 2 = 1 := by
  have hdp : IsCoprime d (p : ℤ) :=
    hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr hp)
  have unit_cast {q : ℕ} (hq : IsCoprime d (q : ℤ)) : IsUnit (d : ZMod q) := by
    exact (ZMod.coe_int_isUnit_iff_isCoprime d q).mpr hq.symm
  have hd4 := unit_cast (hd.of_isCoprime_of_dvd_right (Int.natCast_dvd_natCast.mpr h4))
  have hp0 : (d : ZMod p) ≠ 0 := (unit_cast hdp).ne_zero
  have hχ4 : (ZMod.χ₄ (d : ZMod 4)) ^ 2 = 1 := by
    rcases ZMod.isQuadratic_χ₄ (d : ZMod 4) with h0 | h1 | hn
    · exact ((hd4.map ZMod.χ₄.toMonoidHom).ne_zero h0).elim
    · simp [h1]
    · simp [hn]
  rw [primeCharacter_int h4 hp hd, ← Int.cast_pow, mul_pow, legendreSym,
    quadraticChar_sq_one hp0]
  split_ifs
  · rw [hχ4, one_mul, Int.cast_one]
  · norm_num

end ZInQ.Manuscript.RC.EvenMoving
