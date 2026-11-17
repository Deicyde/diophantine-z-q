import Mathlib
import ZInQKernel.Contrib.OneProof.RC.Odd.Operators

/-!
# Lane RC12-odd: the integer divisions (O.9) and (O.11) (App F, tex 9558–9636)

Manuscript (11/5), Appendix F, proof of Proposition `ex:app-coefficient-rules`:

* (O.9) (tex 9570–9584): `v₂ B_U[J r m²] ≥ w(r) + ½#{p ∈ J simple} − e_U`; in the full-two-torsion
  family every prime is split, `w = ω` and `e_U = 0` (matching parity), so with
  `B_U = 2^{−n_U} ∏_{p∈U}(U_p − η(p)V_p) g`, `n_U = δ + |U|`, this reads
  `v₂ (∏_{p∈U}(U_p − η(p)V_p) g)[n] ≥ δ + |U| + ω(r)`, `r` the part of the squarefree kernel of `n`
  prime to `U`. For the odd source, at one advanced stage, the bound holds truncated
  ("replaced by its minimum with `R`", tex 9578–9584): here the truncation level is `T`.
* (O.11) (tex 9618–9636): "In matching parity the shell recurrence gives
  `B_U[Jm²] − B_U[J] η(m) ∈ 2𝒪`. Thus `H_U = (B_U − ∑_J B_U[J] Θ_J)/2` is integral."

We state them undivided, as divisibilities by powers of `2` in the coefficient ring `R`, for an
abstract coefficient function `a` satisfying:
* the source depth inequality `2^{min T (δ + ω(sqf n))} ∣ a(n)` (the "fixed minimum depth" of the
  even source, or the minimum-depth inequalities of Proposition `ex:app-odd-minimum` at an odd stage,
  tex 9450–9453, 9484); `ω(sqf n)` is the number of primes with odd exponent in `n` (`oddPart n`);
* the recurrence (O.6) at every good prime `q` (odd, outside the support, `a_q ≡ q + 1 (mod 4)` as
  every prime is split in `ℚ(E[2]) = ℚ`, tex 9585, 9593), with `ψ(q)/η(q) = ±1`;
* a completely multiplicative phase character `χ = η` and `a(0) = 0` (tex 9092).

Everything here is PROVED.
-/

namespace ZInQ.Manuscript.RC.Odd

/-- The primes with odd exponent in `n`: the support of the squarefree kernel of `n`. -/
def oddPart (n : ℕ) : Finset ℕ := n.primeFactors.filter (fun q => Odd (n.factorization q))

theorem mem_oddPart {n q : ℕ} : q ∈ oddPart n ↔ Odd (n.factorization q) := by
  unfold oddPart
  rw [Finset.mem_filter, ← Nat.support_factorization, Finsupp.mem_support_iff]
  refine ⟨fun h => h.2, fun h => ⟨fun h0 => ?_, h⟩⟩
  rw [h0] at h
  exact absurd h (by decide)

theorem oddPart_mul_sq {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0) : oddPart (n * m ^ 2) = oddPart n := by
  ext q
  rw [mem_oddPart, mem_oddPart, Nat.factorization_mul hn (pow_ne_zero 2 hm),
    Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul,
    Nat.odd_iff, Nat.odd_iff]
  omega

theorem factorization_pow_mul_apply {p k n' q : ℕ} (hp : p.Prime) (hn' : n' ≠ 0) :
    (p ^ k * n').factorization q = (if q = p then k else 0) + n'.factorization q := by
  rw [Nat.factorization_mul (pow_ne_zero k hp.ne_zero) hn', hp.factorization_pow,
    Finsupp.add_apply, Finsupp.single_apply]
  by_cases h : q = p
  · subst h; simp
  · simp [Ne.symm h, h]

theorem oddPart_pow_even_mul {p s n' : ℕ} (hp : p.Prime) (hn' : n' ≠ 0) (hpn : ¬ p ∣ n') :
    oddPart (p ^ (2 * s) * n') = oddPart n' := by
  ext q
  rw [mem_oddPart, mem_oddPart, factorization_pow_mul_apply hp hn']
  by_cases h : q = p
  · subst h
    rw [if_pos rfl, Nat.factorization_eq_zero_of_not_dvd hpn]
    simp [Nat.odd_iff]
  · rw [if_neg h, zero_add]

theorem oddPart_pow_odd_mul {p s n' : ℕ} (hp : p.Prime) (hn' : n' ≠ 0) (hpn : ¬ p ∣ n') :
    oddPart (p ^ (2 * s + 1) * n') = insert p (oddPart n') := by
  ext q
  rw [Finset.mem_insert, mem_oddPart, mem_oddPart, factorization_pow_mul_apply hp hn']
  by_cases h : q = p
  · subst h
    rw [if_pos rfl, Nat.factorization_eq_zero_of_not_dvd hpn]
    simp [Nat.odd_iff]
  · rw [if_neg h, zero_add]; simp [h]

theorem not_mem_oddPart_of_not_dvd {p n' : ℕ} (hpn : ¬ p ∣ n') : p ∉ oddPart n' := by
  rw [mem_oddPart, Nat.factorization_eq_zero_of_not_dvd hpn]
  decide

theorem oddPart_mul_prime {p n' : ℕ} (hp : p.Prime) (hn' : n' ≠ 0) (hpn : ¬ p ∣ n') :
    oddPart (p * n') = insert p (oddPart n') := by
  have := oddPart_pow_odd_mul (s := 0) hp hn' hpn
  simpa using this

theorem legendreSym_neg_mul_sq {p : ℕ} [Fact p.Prime] {n m : ℕ} (hpm : ¬ p ∣ m) :
    legendreSym p (-((n * m ^ 2 : ℕ) : ℤ)) = legendreSym p (-(n : ℤ)) := by
  have hm : legendreSym p (m : ℤ) ^ 2 = 1 := by
    apply legendreSym.sq_one
    intro h0
    apply hpm
    have : (p : ℤ) ∣ (m : ℤ) := by
      rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]; exact_mod_cast h0
    exact Int.natCast_dvd_natCast.mp this
  have : -((n * m ^ 2 : ℕ) : ℤ) = (-(n : ℤ)) * ((m : ℤ) ^ 2) := by push_cast; ring
  rw [this, legendreSym.mul, show ((m : ℤ) ^ 2) = (m : ℤ) * (m : ℤ) by ring, legendreSym.mul,
    ← pow_two, hm, mul_one]

theorem min_succ_le (T x : ℕ) : min T (x + 1) ≤ min T x + 1 := by omega

variable {R : Type*} [CommRing R]

theorem two_pow_dvd_two_mul {k : ℕ} {x : R} (h : (2 : R) ^ k ∣ x) : (2 : R) ^ (k + 1) ∣ 2 * x := by
  rw [pow_succ, mul_comm _ (2 : R)]; exact mul_dvd_mul_left 2 h

theorem two_pow_dvd_of_le {k k' : ℕ} {x : R} (hk : k' ≤ k) (h : (2 : R) ^ k ∣ x) :
    (2 : R) ^ k' ∣ x := dvd_trans (pow_dvd_pow 2 hk) h

theorem two_pow_dvd_intCast_even_mul {k : ℕ} {x : R} {c : ℤ} (hc : Even c) (h : (2 : R) ^ k ∣ x) :
    (2 : R) ^ (k + 1) ∣ (c : R) * x := by
  obtain ⟨d, rfl⟩ := hc
  have : ((d + d : ℤ) : R) * x = (d : R) * (2 * x) := by push_cast; ring
  rw [this]; exact dvd_mul_of_dvd_right (two_pow_dvd_two_mul h) _

/-- The invariant carried through `∏_{p∈U}(U_p − η(p)V_p)`: vanishing at `0`, the bound (O.9),
and the shell congruence behind (O.11) (tex 9626–9627). -/
structure DivInv (T δ : ℕ) (χ : ℕ → R) (GoodPrime : ℕ → Prop) (U : Finset ℕ) (b : ℕ → R) :
    Prop where
  zero : b 0 = 0
  bound : ∀ n, (2 : R) ^ (min T (δ + U.card + (oddPart n \ U).card)) ∣ b n
  cong : ∀ n m, n ≠ 0 → m ≠ 0 → (∀ q ∈ m.primeFactors, GoodPrime q) →
    (∀ q ∈ oddPart n \ U, ¬ q ∣ m) →
    (2 : R) ^ (min T (δ + U.card + (oddPart n \ U).card + 1)) ∣ b (n * m ^ 2) - χ m * b n

end ZInQ.Manuscript.RC.Odd
