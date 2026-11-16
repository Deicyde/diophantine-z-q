import ZInQKernel.Contrib.OneProof.FHPrinted.LocalNorm
import Mathlib.NumberTheory.FundamentalDiscriminant

/-!
# The Kronecker symbol `(D / n)` and the idelic character of `ℚ(√D)` (Mathlib only)

Task bfh-kronecker (report `docs/research/bfh-kronecker.md`). Bump–Friedberg–Hoffstein (Invent.
Math. 102, 1990) write `χ_D(n) = (D / n)`, the Kronecker symbol, for a fundamental discriminant
`D`. Mathlib has the Jacobi symbol `jacobiSym a b` (odd `b`) and the characters `ZMod.χ₈`, but no
Kronecker symbol. This file defines it by the textbook formula and proves the bridge to the
character `FHPrinted.idelicChar` (built from the local norm-residue characters of `ℚ_p(√D)`) used
by fh-printed and bfh-leaf.

* `kroneckerPrime D p`: `(D / 2) = χ₈(D)` (`0` for `D` even, `(−1)^{(D²−1)/8}` for `D` odd) and
  `(D / p) = J(D | p)` (Mathlib's Jacobi symbol at a prime, i.e. the Legendre symbol) for `p ≠ 2`;
* `kroneckerSym D n`: `(D / 0) = 1` if `|D| = 1`, else `0`; for `n ≥ 1`,
  `(D / n) = ∏_{p^k ∥ n} (D / p)^k` (the definition of H. Cohen, *A course in computational
  algebraic number theory*, Def. 1.4.8, UNVERIFIED number; the sign `(D / −1)` is not needed since
  `n ≥ 0`).

Theorems:
* `kroneckerSym_mul` (complete multiplicativity on `n ≠ 0`), `kroneckerSym_prime` (Legendre symbol
  at odd primes), `kroneckerSym_two` (`χ₈(D)`), `kroneckerSym_two_of_one_mod_four`;
* `charAtPrime_eq_kroneckerPrime`, `idelicChar_eq_kroneckerSym`: for every fundamental
  discriminant `D` (odd or even), `idelicChar D n = (D / n)` for `n ≠ 0`;
* `kroneckerSym_eq_jacobiSym`: for `D ≡ 1 (mod 4)` squarefree, `(D / n) = J(n | |D|)` (`n ≠ 0`),
  the form in which `GZDecomp.chiD` is defined.
-/

namespace ZInQ.BFHPrinted

open ZInQ.FHPrinted

/-! ## The Kronecker symbol -/

/-- **The Kronecker symbol at a prime**: `(D / 2) = χ₈(D)` (`0` if `D` is even, `1` if
`D ≡ ±1 (mod 8)`, `−1` if `D ≡ ±3 (mod 8)`) and, for `p ≠ 2`, `(D / p) = J(D | p)` (Mathlib's
Jacobi symbol, which is the Legendre symbol at a prime). -/
noncomputable def kroneckerPrime (D : ℤ) (p : ℕ) : ℤ :=
  if p = 2 then ZMod.χ₈ (D : ZMod 8) else jacobiSym D p

/-- **The Kronecker symbol `(D / n)`** for `n ≥ 0`: `(D / 0) = 1` if `|D| = 1` and `0`
otherwise; for `n ≥ 1`, `(D / n) = ∏_{p^k ∥ n} (D / p)^k` with `(D / p)` as in
`kroneckerPrime`. -/
noncomputable def kroneckerSym (D : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then (if D.natAbs = 1 then 1 else 0)
  else n.factorization.prod fun p k => kroneckerPrime D p ^ k

theorem kroneckerSym_of_ne_zero (D : ℤ) {n : ℕ} (hn : n ≠ 0) :
    kroneckerSym D n = n.factorization.prod fun p k => kroneckerPrime D p ^ k := by
  rw [kroneckerSym, ite_eq_right hn]

@[simp] theorem kroneckerSym_one (D : ℤ) : kroneckerSym D 1 = 1 := by
  rw [kroneckerSym_of_ne_zero D one_ne_zero, Nat.factorization_one, Finsupp.prod_zero_index]

/-- **`(D / ·)` is completely multiplicative** (on `n ≠ 0`). -/
theorem kroneckerSym_mul (D : ℤ) {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    kroneckerSym D (m * n) = kroneckerSym D m * kroneckerSym D n := by
  rw [kroneckerSym_of_ne_zero D (mul_ne_zero hm hn), kroneckerSym_of_ne_zero D hm,
    kroneckerSym_of_ne_zero D hn, Nat.factorization_mul hm hn,
    Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]

/-- The symbol at a prime is `kroneckerPrime`. -/
theorem kroneckerSym_of_prime (D : ℤ) {p : ℕ} (hp : p.Prime) :
    kroneckerSym D p = kroneckerPrime D p := by
  rw [kroneckerSym_of_ne_zero D hp.ne_zero, hp.factorization,
    Finsupp.prod_single_index (by simp), pow_one]

/-- **`(D / p)` is the Legendre symbol at an odd prime.** -/
theorem kroneckerSym_prime {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (D : ℤ) :
    kroneckerSym D p = legendreSym p D := by
  rw [kroneckerSym_of_prime D Fact.out, kroneckerPrime, ite_eq_right hp2,
    jacobiSym.legendreSym.to_jacobiSym]

/-- **`(D / 2) = χ₈(D)`.** -/
theorem kroneckerSym_two (D : ℤ) : kroneckerSym D 2 = ZMod.χ₈ (D : ZMod 8) := by
  rw [kroneckerSym_of_prime D Nat.prime_two, kroneckerPrime, ite_eq_left rfl]

/-- **`(D / 2)` for `D ≡ 1 (mod 4)`**: `1` if `D ≡ 1 (mod 8)`, `−1` if `D ≡ 5 (mod 8)`. -/
theorem kroneckerSym_two_of_one_mod_four {D : ℤ} (hD : D % 4 = 1) :
    kroneckerSym D 2 = if D % 8 = 1 then 1 else -1 := by
  rw [kroneckerSym_two, ZMod.χ₈_int_eq_if_mod_eight, ite_eq_right (by omega)]
  rcases (by omega : D % 8 = 1 ∨ D % 8 = 5) with h | h
  · rw [ite_eq_left (Or.inl h), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## The idelic character at a prime -/

/-- At an odd prime `p` with `p² ∤ d`, the local character `χ_{d,p}` gives the Legendre symbol:
`charAtPrime d p = (d / p)` (`0` if `p ∣ d`: a ramified local component). -/
theorem charAtPrime_odd {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {d : ℤ}
    (hd2 : ¬ (p : ℤ) ^ 2 ∣ d) : charAtPrime d p = legendreSym p d := by
  unfold charAtPrime
  rw [dite_eq_left hp.out]
  by_cases hpd : (p : ℤ) ∣ d
  · -- ramified
    rw [ite_eq_right]
    · symm
      rw [legendreSym.eq_zero_iff]
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd d p).mpr hpd
    · intro hall
      obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod p)
        (by rw [ZMod.ringChar_zmod_n]; exact hp2)
      have ha0 : a ≠ 0 := by rintro rfl; exact ha ⟨0, by ring⟩
      set u : ℤ := ((a.val : ℕ) : ℤ)
      have hu : (u : ZMod p) = a := by simp [u]
      have hn := not_isLocalNorm_of_ramified hpd hd2 (u := u) (by rw [hu]; exact ha)
      apply hn
      have := hall (u : ℤ_[p]) (isUnit_of_toZMod (by rw [map_intCast, hu]; exact ha0))
      simpa using this
  · -- unramified
    rw [ite_eq_left (fun u hu => isLocalNorm_unit hp2 hpd ((hu.map PadicInt.toZMod).ne_zero))]
    have h0 := intCast_ne_zero_of_not_dvd hpd
    by_cases hsq : IsSquare (d : ZMod p)
    · obtain ⟨w, hw0, hw⟩ := exists_sq_of_int hp2 hpd hsq
      rw [ite_eq_left (isLocalNorm_of_eq_sq (by norm_num) hw0 hw _),
        (legendreSym.eq_one_iff p h0).mpr hsq]
    · rw [ite_eq_right (not_isLocalNorm_p hsq), (legendreSym.eq_neg_one_iff p).mpr hsq]

/-- At `2`, for `d ≡ 1 (mod 4)`: `charAtPrime d 2 = χ₈(d)` (`1` for `d ≡ 1`, `−1` for
`d ≡ 5 (mod 8)`; `ℚ₂(√d)/ℚ₂` is unramified). -/
theorem charAtPrime_two_of_one_mod_four {d : ℤ} (hd4 : d % 4 = 1) :
    charAtPrime d 2 = ZMod.χ₈ (d : ZMod 8) := by
  have := Fact.mk Nat.prime_two
  have hR : ZMod.χ₈ (d : ZMod 8) = if d % 8 = 1 then 1 else -1 := by
    rw [ZMod.χ₈_int_eq_if_mod_eight, ite_eq_right (by omega : ¬ d % 2 = 0)]
    rcases (by omega : d % 8 = 1 ∨ d % 8 = 5) with h | h
    · rw [ite_eq_left (Or.inl h), ite_eq_left h]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  rw [hR]
  unfold charAtPrime
  rw [dite_eq_left Nat.prime_two, ite_eq_left (fun u hu => isLocalNorm_two_unit hd4 hu)]
  have e2 : ((2 : ℕ) : ℚ_[2]) = 2 := by norm_num
  rw [e2]
  rcases (by omega : d % 8 = 1 ∨ d % 8 = 5) with h | h
  · rw [ite_eq_left (isLocalNorm_two_of_one h _), ite_eq_left h]
  · rw [ite_eq_right (not_isLocalNorm_two_of_five h), ite_eq_right (by omega)]

/-- `charAtPrime` depends only on the square class of `d`: `charAtPrime (4 m) p = charAtPrime m p`
(`ℚ_p(√(4m)) = ℚ_p(√m)`). -/
theorem charAtPrime_four_mul (m : ℤ) (p : ℕ) : charAtPrime (4 * m) p = charAtPrime m p := by
  unfold charAtPrime
  by_cases hp : p.Prime
  · rw [dite_eq_left hp, dite_eq_left hp]
    have := Fact.mk hp
    have key : ∀ x : ℚ_[p], IsLocalNorm ℚ_[p] (4 * m) x ↔ IsLocalNorm ℚ_[p] m x :=
      isLocalNorm_iff_of_eq_mul_sq (c := (2 : ℚ_[p])) two_ne_zero (by push_cast; ring)
    have key' : IsLocalNorm ℚ_[p] (4 * m) = IsLocalNorm ℚ_[p] m := funext fun x => propext (key x)
    rw [key']
  · rw [dite_eq_right hp, dite_eq_right hp]

/-- **The idelic character at a prime is the Kronecker symbol**, for every fundamental
discriminant `d`. -/
theorem charAtPrime_eq_kroneckerPrime {d : ℤ} (hd : Int.IsFundamentalDiscr d) {p : ℕ}
    (hp : p.Prime) : charAtPrime d p = kroneckerPrime d p := by
  unfold kroneckerPrime
  by_cases hp2 : p = 2
  · subst hp2
    rw [ite_eq_left rfl]
    rcases Int.isFundamentalDiscr_iff_squarefree.mp hd with ⟨h1, -⟩ | ⟨h0, -, h23⟩
    · exact charAtPrime_two_of_one_mod_four h1
    · have hm : d = 4 * (d / 4) := by omega
      rw [hm, charAtPrime_four_mul, charAtPrime_two_of_ramified h23, Int.cast_mul,
        map_mul]
      have : ZMod.χ₈ ((4 : ℤ) : ZMod 8) = 0 := by decide
      rw [this, zero_mul]
  · rw [ite_eq_right hp2]
    have := Fact.mk hp
    rw [← jacobiSym.legendreSym.to_jacobiSym]
    refine charAtPrime_odd hp2 (hd.2.2 p hp (hp.odd_of_ne_two hp2))

/-- **The idelic character of `ℚ(√d)` is the Kronecker symbol** `n ↦ (d / n)` for every
fundamental discriminant `d` and `n ≠ 0`. -/
theorem idelicChar_eq_kroneckerSym {d : ℤ} (hd : Int.IsFundamentalDiscr d) {n : ℕ} (hn : n ≠ 0) :
    idelicChar d n = kroneckerSym d n := by
  rw [idelicChar, kroneckerSym_of_ne_zero d hn]
  refine Finsupp.prod_congr fun p hp => ?_
  rw [charAtPrime_eq_kroneckerPrime hd (Nat.prime_of_mem_primeFactors (by simpa using hp))]

/-- **For `d ≡ 1 (mod 4)` squarefree, `(d / n) = J(n | |d|)`** (`n ≠ 0`; quadratic reciprocity,
through `idelicChar_eq_jacobiSym`). -/
theorem kroneckerSym_eq_jacobiSym {d : ℤ} (hd4 : d % 4 = 1) (hd : Squarefree d) {n : ℕ}
    (hn : n ≠ 0) : kroneckerSym d n = jacobiSym (n : ℤ) d.natAbs := by
  have hfd : Int.IsFundamentalDiscr d := Int.isFundamentalDiscr_iff_squarefree.mpr (Or.inl ⟨hd4, hd⟩)
  rw [← idelicChar_eq_kroneckerSym hfd hn, idelicChar_eq_jacobiSym hd4 hd n hn]

end ZInQ.BFHPrinted
