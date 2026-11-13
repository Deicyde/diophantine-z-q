import ZInQKernel.Progressions.RealChar.Hensel
import Mathlib.NumberTheory.DirichletCharacter.Basic

/-!
# Real Dirichlet characters modulo a prime power

A real character (`χ ^ 2 = 1`) is `1` at every unit square. Modulo `p ^ k` with `p` odd, the unit
squares are the quadratic residues mod `p`, so a real character is trivial or `(· / p)`; modulo
`2 ^ k`, the integers `≡ 1 (mod 8)` are squares, so a real character is one of `1, χ₄, χ₈, χ₈'`.
In each case we produce the integer `d` of the classification (`RealCharData`).
-/

namespace ZInQ.Progressions

/-- The conclusion of the classification of real characters, in the multiplicative form used by
the induction: `d` is squarefree, `|d|` divides `q`, `2 ∣ d` only if `8 ∣ q`, and `χ` agrees with
the Legendre symbol `(d / ℓ)` at every prime `ℓ ∤ 2q`. -/
def RealCharData (q : ℕ) (χ : DirichletCharacter ℂ q) (d : ℤ) : Prop :=
  Squarefree d ∧ d.natAbs ∣ q ∧ (2 ∣ d → 8 ∣ q) ∧
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ 2 * q → χ ℓ = (legendreSym ℓ d : ℂ)

theorem realChar_apply_sq {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1) {v : ZMod q}
    (hv : IsUnit v) : χ (v ^ 2) = 1 := by
  rw [map_pow, ← MulChar.pow_apply' χ two_ne_zero, hχ, MulChar.one_apply hv]

theorem realChar_apply_sq_eq_one {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    {v : ZMod q} (hv : IsUnit v) : χ v ^ 2 = 1 := by
  rw [← map_pow]; exact realChar_apply_sq hχ hv

/-- A real character is `1` at every unit which is a square modulo `q`. -/
theorem realChar_apply_eq_one_of_dvd {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ ^ 2 = 1)
    {n : ℕ} (hn : n.Coprime q) {y : ℤ} (hy : (q : ℤ) ∣ y ^ 2 - n) : χ n = 1 := by
  have h : ((n : ℕ) : ZMod q) = (y : ZMod q) ^ 2 := by
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr hy
    push_cast at this
    exact (sub_eq_zero.mp this).symm
  have hu : IsUnit ((n : ℕ) : ZMod q) := (ZMod.isUnit_iff_coprime n q).mpr hn
  rw [h] at hu ⊢
  exact realChar_apply_sq hχ ((isUnit_pow_iff two_ne_zero).mp hu)

/-- `p* = (-1) ^ ((p - 1) / 2) · p`. -/
def realCharPstar (p : ℕ) : ℤ := if p % 4 = 1 then p else -p

theorem natAbs_realCharPstar (p : ℕ) : (realCharPstar p).natAbs = p := by
  unfold realCharPstar; split_ifs <;> simp

/-- Quadratic reciprocity in the form `(ℓ / p) = (p* / ℓ)`. -/
theorem legendreSym_realCharPstar {p ℓ : ℕ} [Fact p.Prime] [Fact ℓ.Prime] (hp : p ≠ 2)
    (hℓ : ℓ ≠ 2) : legendreSym p ℓ = legendreSym ℓ (realCharPstar p) := by
  have hp1 : p % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hp
  have hℓ1 : ℓ % 2 = 1 := (Nat.Prime.mod_two_eq_one_iff_ne_two Fact.out).mpr hℓ
  unfold realCharPstar
  split_ifs with h
  · exact (legendreSym.quadratic_reciprocity_one_mod_four h hℓ).symm
  · have hp3 : p % 4 = 3 := by omega
    rw [legendreSym.at_neg hℓ, ZMod.χ₄_nat_eq_if_mod_four]
    rcases (by omega : ℓ % 4 = 1 ∨ ℓ % 4 = 3) with h4 | h4
    · rw [legendreSym.quadratic_reciprocity_one_mod_four h4 hp]
      simp [h4, hℓ1]
    · rw [legendreSym.quadratic_reciprocity_three_mod_four hp3 h4]
      simp [h4, hℓ1]

/-- Classification modulo an odd prime power. -/
theorem realChar_primePow_odd {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k)
    (χ : DirichletCharacter ℂ (p ^ k)) (hχ : χ ^ 2 = 1) : ∃ d : ℤ, RealCharData (p ^ k) χ d := by
  have : Fact p.Prime := ⟨hp⟩
  have hcop : ∀ n : ℕ, ¬ p ∣ n → n.Coprime (p ^ k) := fun n hn =>
    Nat.Coprime.pow_right _ (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hn))
  -- `χ` is `1` at the quadratic residues
  have key : ∀ n : ℕ, legendreSym p n = 1 → χ n = 1 := by
    intro n hn
    have hn0 : ((n : ℤ) : ZMod p) ≠ 0 := by
      intro h0
      rw [(legendreSym.eq_zero_iff p n).mpr h0] at hn
      exact zero_ne_one hn
    obtain ⟨x, hx⟩ := (legendreSym.eq_one_iff p hn0).mp hn
    have hpn : ¬ (p : ℤ) ∣ n := fun h => hn0 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mpr h)
    have hxv : (((x.val : ℤ)) : ZMod p) = x := by simp
    have hxd : (p : ℤ) ∣ (x.val : ℤ) ^ 2 - n := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_pow, hxv, hx]
      ring
    obtain ⟨y, hy⟩ := realChar_exists_sq_mod_pow_odd hp hp2 hpn hxd k
    have hpn' : ¬ p ∣ n := fun h => hpn (Int.natCast_dvd_natCast.mpr h)
    exact realChar_apply_eq_one_of_dvd hχ (hcop n hpn') (by push_cast; exact hy)
  -- a quadratic nonresidue `g`
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  have hg : legendreSym p (a.val : ℕ) = -1 := by
    rw [legendreSym.eq_neg_one_iff', ZMod.natCast_zmod_val]; exact ha
  have hgp : ¬ p ∣ a.val := by
    intro h
    apply ha
    rw [← ZMod.natCast_zmod_val a, (ZMod.natCast_eq_zero_iff _ _).mpr h]
    exact ⟨0, by simp⟩
  have hε : χ (a.val : ℕ) ^ 2 = 1 :=
    realChar_apply_sq_eq_one hχ ((ZMod.isUnit_iff_coprime _ _).mpr (hcop _ hgp))
  -- `χ` is constant on the nonresidues
  have key' : ∀ n : ℕ, legendreSym p n = -1 → χ n = χ (a.val : ℕ) := by
    intro n hn
    have h1 : χ ((n * a.val : ℕ) : ZMod (p ^ k)) = 1 :=
      key _ (by push_cast; rw [legendreSym.mul, hn, hg]; norm_num)
    rw [Nat.cast_mul, map_mul] at h1
    calc χ n = χ n * χ (a.val : ℕ) ^ 2 := by rw [hε, mul_one]
      _ = χ (a.val : ℕ) := by rw [sq, ← mul_assoc, h1, one_mul]
  -- primes `ℓ ∤ 2 p ^ k`
  have hℓ : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ 2 * p ^ k →
      ℓ ≠ 2 ∧ (legendreSym p ℓ = 1 ∨ legendreSym p ℓ = -1) := by
    intro ℓ hℓp hdvd
    refine ⟨fun h => hdvd (by rw [h]; exact dvd_mul_right 2 _), legendreSym.eq_one_or_neg_one p ?_⟩
    intro h0
    have h1 : (p : ℤ) ∣ (ℓ : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
    have h2 : p ∣ ℓ := Int.natCast_dvd_natCast.mp h1
    have h3 : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp hℓp.out).mp h2
    exact hdvd (h3 ▸ (dvd_pow_self p (by omega)).mul_left 2)
  rcases mul_self_eq_one_iff.mp (show χ (a.val : ℕ) * χ (a.val : ℕ) = 1 by rw [← sq]; exact hε)
    with he | he
  · refine ⟨1, squarefree_one, by simp, fun h => absurd h (by decide), ?_⟩
    intro ℓ _ hdvd
    obtain ⟨-, h | h⟩ := hℓ ℓ hdvd
    · rw [key ℓ h, legendreSym.at_one]; simp
    · rw [key' ℓ h, he, legendreSym.at_one]; simp
  · refine ⟨realCharPstar p, ?_, ?_, ?_, ?_⟩
    · rw [← Int.squarefree_natAbs, natAbs_realCharPstar]; exact hp.squarefree
    · rw [natAbs_realCharPstar]; exact dvd_pow_self p (by omega)
    · intro h2
      have : 2 ∣ (realCharPstar p).natAbs := Int.natCast_dvd.mp (by exact_mod_cast h2)
      rw [natAbs_realCharPstar] at this
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp this) (Ne.symm hp2)
    · intro ℓ _ hdvd
      obtain ⟨hℓ2, h | h⟩ := hℓ ℓ hdvd
      · rw [← legendreSym_realCharPstar hp2 hℓ2, key ℓ h, h]; simp
      · rw [← legendreSym_realCharPstar hp2 hℓ2, key' ℓ h, he, h]; simp

/-- Classification modulo a power of `2`. -/
theorem realChar_twoPow (k : ℕ) (χ : DirichletCharacter ℂ (2 ^ k)) (hχ : χ ^ 2 = 1) :
    ∃ d : ℤ, RealCharData (2 ^ k) χ d := by
  have hcop : ∀ n : ℕ, n % 2 = 1 → n.Coprime (2 ^ k) := fun n hn =>
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr hn))
  have key : ∀ n : ℕ, n % 8 = 1 → χ n = 1 := by
    intro n hn
    obtain ⟨y, hy⟩ := realChar_exists_sq_mod_two_pow (n := n) (by omega) k
    exact realChar_apply_eq_one_of_dvd hχ (hcop n (by omega)) (by push_cast; exact hy)
  have hsq : ∀ n : ℕ, n % 2 = 1 → χ n ^ 2 = 1 := fun n hn =>
    realChar_apply_sq_eq_one hχ ((ZMod.isUnit_iff_coprime n _).mpr (hcop n hn))
  -- `χ ℓ = χ r` whenever `ℓ r ≡ 1 (mod 8)`
  have red : ∀ ℓ r : ℕ, r % 2 = 1 → (ℓ * r) % 8 = 1 → χ ℓ = χ r := by
    intro ℓ r hr hℓr
    have h1 := key _ hℓr
    rw [Nat.cast_mul, map_mul] at h1
    calc χ ℓ = χ ℓ * χ r ^ 2 := by rw [hsq r hr, mul_one]
      _ = χ r := by rw [sq, ← mul_assoc, h1, one_mul]
  have h7 : χ (7 : ℕ) = χ (3 : ℕ) * χ (5 : ℕ) := by
    have h := key (7 * 3 * 5) (by norm_num)
    rw [Nat.cast_mul, Nat.cast_mul, map_mul, map_mul] at h
    calc χ (7 : ℕ) = χ (7 : ℕ) * (χ (3 : ℕ) ^ 2 * χ (5 : ℕ) ^ 2) := by
          rw [hsq 3 rfl, hsq 5 rfl]; ring
      _ = (χ (7 : ℕ) * χ (3 : ℕ) * χ (5 : ℕ)) * (χ (3 : ℕ) * χ (5 : ℕ)) := by ring
      _ = χ (3 : ℕ) * χ (5 : ℕ) := by rw [h, one_mul]
  have hval : ∀ ℓ : ℕ, ℓ % 2 = 1 →
      (ℓ % 8 = 1 ∧ χ ℓ = 1) ∨ (ℓ % 8 = 3 ∧ χ ℓ = χ (3 : ℕ)) ∨
        (ℓ % 8 = 5 ∧ χ ℓ = χ (5 : ℕ)) ∨ (ℓ % 8 = 7 ∧ χ ℓ = χ (3 : ℕ) * χ (5 : ℕ)) := by
    intro ℓ hℓ
    rcases (by omega : ℓ % 8 = 1 ∨ ℓ % 8 = 3 ∨ ℓ % 8 = 5 ∨ ℓ % 8 = 7) with h | h | h | h
    · exact Or.inl ⟨h, by rw [red ℓ 1 rfl (by rw [Nat.mul_mod, h]), Nat.cast_one, map_one]⟩
    · exact Or.inr <| Or.inl ⟨h, red ℓ 3 rfl (by rw [Nat.mul_mod, h])⟩
    · exact Or.inr <| Or.inr <| Or.inl ⟨h, red ℓ 5 rfl (by rw [Nat.mul_mod, h])⟩
    · exact Or.inr <| Or.inr <| Or.inr ⟨h, by rw [red ℓ 7 rfl (by rw [Nat.mul_mod, h]), h7]⟩
  -- `χ 5 = -1` forces `8 ∣ 2 ^ k`
  have hk3 : χ (5 : ℕ) = -1 → 3 ≤ k := by
    intro h5
    by_contra hk
    have h51 : ((5 : ℕ) : ZMod (2 ^ k)) = ((1 : ℕ) : ZMod (2 ^ k)) :=
      (ZMod.natCast_eq_natCast_iff' 5 1 (2 ^ k)).mpr (by interval_cases k <;> norm_num)
    rw [h51, Nat.cast_one, map_one] at h5
    norm_num at h5
  have h8k : 3 ≤ k → 8 ∣ 2 ^ k := fun hk => Nat.pow_dvd_pow 2 hk
  have h2k : 3 ≤ k → 2 ∣ 2 ^ k := fun hk => dvd_pow_self 2 (by omega)
  have hodd : ∀ (ℓ : ℕ) [Fact ℓ.Prime], ¬ ℓ ∣ 2 * 2 ^ k → ℓ ≠ 2 ∧ ℓ % 2 = 1 := by
    intro ℓ hℓp hdvd
    have hℓ2 : ℓ ≠ 2 := fun h => hdvd (by rw [h]; exact dvd_mul_right 2 _)
    exact ⟨hℓ2, (Nat.Prime.mod_two_eq_one_iff_ne_two hℓp.out).mpr hℓ2⟩
  rcases mul_self_eq_one_iff.mp (show χ (3 : ℕ) * χ (3 : ℕ) = 1 by rw [← sq]; exact hsq 3 rfl)
    with h3 | h3 <;>
  rcases mul_self_eq_one_iff.mp (show χ (5 : ℕ) * χ (5 : ℕ) = 1 by rw [← sq]; exact hsq 5 rfl)
    with h5 | h5
  · -- the trivial character
    refine ⟨1, squarefree_one, by simp, fun h => absurd h (by decide), ?_⟩
    intro ℓ _ hdvd
    obtain ⟨-, hℓ⟩ := hodd ℓ hdvd
    rw [legendreSym.at_one]
    rcases hval ℓ hℓ with ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ | ⟨-, h⟩ <;> simp only [h, h3, h5] <;> simp
  · -- `χ₈'`, `d = -2`
    have hk := hk3 h5
    refine ⟨-2, ?_, by simpa using h2k hk, fun _ => h8k hk, ?_⟩
    · rw [← Int.squarefree_natAbs]; exact Nat.prime_two.squarefree
    intro ℓ _ hdvd
    obtain ⟨hℓ2, hℓ⟩ := hodd ℓ hdvd
    rw [legendreSym.at_neg_two hℓ2, ZMod.χ₈'_nat_eq_if_mod_eight]
    rcases hval ℓ hℓ with ⟨h8, h⟩ | ⟨h8, h⟩ | ⟨h8, h⟩ | ⟨h8, h⟩ <;> simp only [h, h3, h5] <;> simp [h8, hℓ]
  · -- `χ₄`, `d = -1`
    refine ⟨-1, isUnit_neg_one.squarefree, by simp, fun h => absurd h (by decide), ?_⟩
    intro ℓ _ hdvd
    obtain ⟨hℓ2, hℓ⟩ := hodd ℓ hdvd
    rw [legendreSym.at_neg_one hℓ2, ZMod.χ₄_nat_eq_if_mod_four]
    rcases hval ℓ hℓ with ⟨h8, h⟩ | ⟨h8, h⟩ | ⟨h8, h⟩ | ⟨h8, h⟩ <;>
      simp only [h, h3, h5] <;> simp [hℓ, show ℓ % 4 = (ℓ % 8) % 4 by omega, h8]
  · -- `χ₈`, `d = 2`
    have hk := hk3 h5
    refine ⟨2, Int.prime_two.squarefree, by simpa using h2k hk, fun _ => h8k hk, ?_⟩
    intro ℓ _ hdvd
    obtain ⟨hℓ2, hℓ⟩ := hodd ℓ hdvd
    rw [legendreSym.at_two hℓ2, ZMod.χ₈_nat_eq_if_mod_eight]
    rcases hval ℓ hℓ with ⟨h8, h⟩ | ⟨h8, h⟩ | ⟨h8, h⟩ | ⟨h8, h⟩ <;> simp only [h, h3, h5] <;> simp [h8, hℓ]

end ZInQ.Progressions
