import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.FieldTheory.Finite.Basic

/-!
# GenusOdd: Euler's criterion against the Jacobi symbol in a finite field (PROVED)

For a finite field `F` of odd characteristic `p` with `q` elements and an integer `d ≡ 1 (mod 4)`
prime to `p`: `d^((q-1)/2) = (q / |d|)` in `F` (`pow_half_eq_jacobiSym`). This is the residue-field
computation behind genus theory: the arithmetic Frobenius at a prime of norm `q` acts on `√d` by
the Jacobi symbol `(q / |d|) = χ_d(q)`.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

/-- **Quadratic reciprocity for `d ≡ 1 (mod 4)`**, any sign: `(d / p) = (p / |d|)` for an odd
prime `p` (PROVED). -/
theorem jacobiSym_one_mod_four_swap {d : ℤ} (hd : d % 4 = 1) {p : ℕ} (hp : Odd p) :
    jacobiSym d p = jacobiSym p d.natAbs := by
  rcases le_or_gt 0 d with h0 | h0
  · have hnat : (d.natAbs : ℤ) = d := Int.natAbs_of_nonneg h0
    have h4 : d.natAbs % 4 = 1 := by omega
    have := jacobiSym.quadratic_reciprocity_one_mod_four h4 hp
    rw [hnat] at this
    exact this
  · have hnat : (d.natAbs : ℤ) = -d := by omega
    have h4 : d.natAbs % 4 = 3 := by omega
    have hd' : d = -(d.natAbs : ℤ) := by omega
    have hp2 : p % 2 = 1 := by obtain ⟨k, hk⟩ := hp; omega
    rw [hd', jacobiSym.neg _ hp, Int.natAbs_neg, Int.natAbs_natCast,
      ← jacobiSym.quadratic_reciprocity_if (a := d.natAbs) (b := p) (by omega) hp2]
    rcases Nat.odd_mod_four_iff.mp hp2 with h1 | h3
    · rw [ZMod.χ₄_nat_one_mod_four h1, if_neg (by omega), one_mul]
    · rw [ZMod.χ₄_nat_three_mod_four h3, if_pos ⟨h4, h3⟩]; ring

/-- Iterating `a^p = a`: `a^((p^f - 1)/2) = (a^((p-1)/2))^f` (PROVED). -/
theorem pow_half_pow {F : Type*} [CommMonoid F] {a : F} {p k : ℕ} (hpk : p = 2 * k + 1)
    (hap : a ^ p = a) (f : ℕ) : ∃ m, p ^ f = 2 * m + 1 ∧ a ^ m = (a ^ k) ^ f := by
  induction f with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ f ih =>
    obtain ⟨m, hm, ham⟩ := ih
    refine ⟨p * m + k, ?_, ?_⟩
    · rw [pow_succ, hm, hpk]; ring
    · rw [pow_add, pow_mul, hap, ham, pow_succ]

/-- **Euler's criterion in a finite field against the Jacobi symbol** (PROVED): in a finite field
`F` of odd characteristic `p` with `q` elements, for `d ≡ 1 (mod 4)`,
`d^((q-1)/2) = (q / |d|)`. -/
theorem pow_half_eq_jacobiSym {F : Type*} [Field F] [Fintype F] {p : ℕ} [hp : Fact p.Prime]
    [CharP F p] (hp2 : p ≠ 2) {d : ℤ} (hd : d % 4 = 1) :
    ∃ m, Fintype.card F = 2 * m + 1 ∧
      (d : F) ^ m = ((jacobiSym (Fintype.card F) d.natAbs : ℤ) : F) := by
  have hodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨k, hk⟩ := hodd
  obtain ⟨f, -, hq⟩ := FiniteField.card F p
  set φ := ZMod.castHom (dvd_refl p) F
  have hdF : (d : F) = φ (d : ZMod p) := by rw [map_intCast]
  have hap : (d : F) ^ p = (d : F) := by
    rw [hdF, ← map_pow, ZMod.pow_card]
  obtain ⟨m, hm, ham⟩ := pow_half_pow (by omega : p = 2 * k + 1) hap (f : ℕ)
  refine ⟨m, by rw [hq, hm], ?_⟩
  rw [ham]
  have hL : (d : F) ^ k = ((legendreSym p d : ℤ) : F) := by
    have := legendreSym.eq_pow p d
    have hk' : p / 2 = k := by omega
    rw [hk'] at this
    rw [hdF, ← map_pow, ← this, map_intCast]
  rw [hL, hq, Nat.cast_pow, jacobiSym.pow_left, ← jacobiSym_one_mod_four_swap hd ⟨k, hk⟩,
    ← jacobiSym.legendreSym.to_jacobiSym]
  push_cast
  ring

end ZInQ.Contrib.CloudB3RC53.GenusOdd
