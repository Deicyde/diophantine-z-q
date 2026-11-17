import ZInQKernel.Contrib.OneProof.RC.Boolean.BooleanDegree
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.CharP.Lemmas

/-!
# Lane RC1-boolean, part 3: the Boolean bit-degree lemma

Proof of Proposition `ex:limits-coefficient-transfer` (`diophantine_zq.tex` 5647–5739), tex
5666–5678:

> For a coefficient of any element of `𝒪[G]`, its sign-value function on `𝔽₂^b` expands as
> `A(x) = a_∅ + Σ_{I≠∅} 2^{|I|} a_I Π_{i∈I} x_i`.
> Its low bit is constant and its bit of index `j ≥ 1` has Boolean degree at most `2^{j−1}`.
> One can see this by extracting the `Y^{2^j}` coefficient of `(1+Y)^{A(x)}` modulo two: the
> first possible contribution of `x_I` has degree at least `2^{|I|}` in `Y`, and
> `|I| ≤ 2^{|I|−1}`. Thus `q` coefficient equalities modulo `2^M` have sum of Boolean degrees at
> most `q(2^{M−1}−1)`.

The proof follows the text: bit `j` of `n` is the `Y^{2^j}` coefficient of `(1+Y)^n` over `𝔽₂`
(Lucas, `choose_two_pow_eq_natBit`), and the generating polynomial
`Π_I (1 + X^I ((1+Y^{2^{|I|}})^{a_I} − 1))` over `𝔽₂[X_1,…,X_b]` specializes at every address to
`(1+Y)^{A(x)}`; in it every coefficient of `Y^k` has total degree at most `k/2`, because the factor
attached to `I` only contributes from `Y^{2^{|I|}}` on and `2|I| ≤ 2^{|I|}`.

Auxiliary objects: `bitQ N e = (1+Y^N)^e − 1`, the generating polynomial `genPoly`, and the
predicate `CoeffHalfDeg` ("the coefficient of `Y^k` has total degree at most `k/2`"), which holds
for `1` and is closed under products.

Main results (kind PROVED):
* `natBit_expansionNat_degree`: the core statement for natural-number coefficients;
* `padicBit_zero_signEval_const`, `padicBit_signEval_hasBoolDegLE`: lane item 1, for the
  sign-value function of any element of `ℤ₂[G]` (the Laurent coefficients of elements of `𝒪[G]`
  lie in `ℤ₂[G]`);
* `eqIndicator_hasBoolDegLE`: the indicator of one coefficient equality modulo `2^M` has Boolean
  degree at most `2^{M−1} − 1` (tex 5677–5678).
-/

namespace ZInQ.Manuscript.RC.Boolean

open Finset MvPolynomial

variable {b : ℕ} {G : Type*}

/-- The binary digit of index `j` of the natural number `n`, as an element of `𝔽₂`. -/
def natBit (j n : ℕ) : ZMod 2 := ((n / 2 ^ j : ℕ) : ZMod 2)

/-- Lucas's theorem at `k = 2^j`: `C(n, 2^j) ≡ (bit j of n) (mod 2)`; equivalently bit `j` of `n`
is the `Y^{2^j}` coefficient of `(1+Y)^n` over `𝔽₂` (`Polynomial.coeff_one_add_X_pow`). -/
theorem choose_two_pow_eq_natBit (n j : ℕ) :
    ((n.choose (2 ^ j) : ℕ) : ZMod 2) = natBit j n := by
  induction j generalizing n with
  | zero => simp [natBit]
  | succ j ih =>
    have h := (ZMod.natCast_eq_natCast_iff _ _ 2).mpr
      (Choose.choose_modEq_choose_mod_mul_choose_div_nat (n := n) (k := 2 ^ (j + 1)) (p := 2))
    rw [h]
    have h1 : 2 ^ (j + 1) % 2 = 0 := by simp [pow_succ]
    have h2 : 2 ^ (j + 1) / 2 = 2 ^ j := by simp [pow_succ]
    rw [h1, h2, Nat.choose_zero_right, one_mul, ih]
    unfold natBit
    rw [Nat.div_div_eq_div_mul, ← pow_succ']

/-- The natural-number form of the sign-value expansion,
`N(x) = Σ_I 2^{|I|} a_I Π_{i ∈ I} x_i` with `a_I ∈ ℕ` and `x_i ∈ {0, 1}`. -/
def expansionNat (a : Finset (Fin b) → ℕ) (x : Address b) : ℕ :=
  ∑ I : Finset (Fin b), 2 ^ I.card * a I * ∏ i ∈ I, (x i).val

/-- `2n ≤ 2^n`. -/
theorem two_mul_le_two_pow (n : ℕ) : 2 * n ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := n)
    omega

/-- The one-variable polynomial `(1 + Y^N)^e − 1` over `𝔽₂`. -/
noncomputable def bitQ (N e : ℕ) : Polynomial (ZMod 2) := (1 + Polynomial.X ^ N) ^ e - 1

/-- `Y^N` divides `(1 + Y^N)^e − 1`, so its coefficients below `Y^N` vanish. -/
theorem bitQ_coeff_eq_zero {N e k : ℕ} (hk : k < N) : (bitQ N e).coeff k = 0 := by
  have hdvd : (Polynomial.X : Polynomial (ZMod 2)) ^ N ∣ bitQ N e := by
    have := sub_dvd_pow_sub_pow (1 + Polynomial.X ^ N : Polynomial (ZMod 2)) 1 e
    simpa [bitQ] using this
  exact Polynomial.X_pow_dvd_iff.mp hdvd k hk

/-- A polynomial in `Y` over `𝔽₂[X_1, …, X_b]` whose coefficient of `Y^k` has total degree at most
`k / 2`, for every `k`. -/
def CoeffHalfDeg (Ψ : Polynomial (MvPolynomial (Fin b) (ZMod 2))) : Prop :=
  ∀ k, 2 * (Ψ.coeff k).totalDegree ≤ k

/-- The constant polynomial `1` satisfies `CoeffHalfDeg`. -/
theorem coeffHalfDeg_one : CoeffHalfDeg (1 : Polynomial (MvPolynomial (Fin b) (ZMod 2))) := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs <;> simp

/-- `CoeffHalfDeg` is closed under products: the coefficient of `Y^k` in a product is a sum of
products of coefficients of `Y^i` and `Y^{k-i}`. -/
theorem CoeffHalfDeg.mul {Ψ₁ Ψ₂ : Polynomial (MvPolynomial (Fin b) (ZMod 2))}
    (h₁ : CoeffHalfDeg Ψ₁) (h₂ : CoeffHalfDeg Ψ₂) : CoeffHalfDeg (Ψ₁ * Ψ₂) := by
  intro k
  rw [Polynomial.coeff_mul]
  have : (∑ p ∈ antidiagonal k, Ψ₁.coeff p.1 * Ψ₂.coeff p.2).totalDegree ≤ k / 2 := by
    refine (totalDegree_finsetSum _ _).trans (Finset.sup_le fun p hp => ?_)
    have hk := Finset.mem_antidiagonal.mp hp
    have := totalDegree_mul (Ψ₁.coeff p.1) (Ψ₂.coeff p.2)
    have := h₁ p.1
    have := h₂ p.2
    omega
  omega

/-- The factor `1 + X^I · ((1 + Y^{2^{|I|}})^e − 1)` of the generating polynomial satisfies
`CoeffHalfDeg`: it only contributes from `Y^{2^{|I|}}` on, and `2|I| ≤ 2^{|I|}`. -/
theorem coeffHalfDeg_factor (I : Finset (Fin b)) (e : ℕ) :
    CoeffHalfDeg (1 + Polynomial.C (∏ i ∈ I, X i) *
      (bitQ (2 ^ I.card) e).map (MvPolynomial.C : ZMod 2 →+* MvPolynomial (Fin b) (ZMod 2))) := by
  intro k
  rw [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_map]
  have h1 :
      (Polynomial.coeff (1 : Polynomial (MvPolynomial (Fin b) (ZMod 2))) k).totalDegree = 0 := by
    rw [Polynomial.coeff_one]; split_ifs <;> simp
  by_cases hk : k < 2 ^ I.card
  · rw [bitQ_coeff_eq_zero hk, map_zero, mul_zero, add_zero, h1]
    omega
  · have h2 : (∏ i ∈ I, (X i : MvPolynomial (Fin b) (ZMod 2))).totalDegree ≤ I.card := by
      refine (totalDegree_finsetProd _ _).trans ?_
      simp [totalDegree_X]
    have h4 := totalDegree_mul (∏ i ∈ I, (X i : MvPolynomial (Fin b) (ZMod 2)))
      (C ((bitQ (2 ^ I.card) e).coeff k))
    rw [totalDegree_C, add_zero] at h4
    have h3 := (totalDegree_add
      (Polynomial.coeff (1 : Polynomial (MvPolynomial (Fin b) (ZMod 2))) k)
      ((∏ i ∈ I, X i) * C ((bitQ (2 ^ I.card) e).coeff k))).trans
      (max_le (h1.le.trans (Nat.zero_le I.card)) (h4.trans h2))
    have h5 := two_mul_le_two_pow I.card
    omega

/-- The generating polynomial `Φ = Π_I (1 + X^I ((1 + Y^{2^{|I|}})^{a_I} − 1))` over
`𝔽₂[X_1, …, X_b]`. -/
noncomputable def genPoly (a : Finset (Fin b) → ℕ) :
    Polynomial (MvPolynomial (Fin b) (ZMod 2)) :=
  ∏ I : Finset (Fin b), (1 + Polynomial.C (∏ i ∈ I, X i) *
    (bitQ (2 ^ I.card) (a I)).map (MvPolynomial.C : ZMod 2 →+* MvPolynomial (Fin b) (ZMod 2)))

/-- In the generating polynomial, the coefficient of `Y^k` has total degree at most `k / 2`. -/
theorem coeffHalfDeg_genPoly (a : Finset (Fin b) → ℕ) : CoeffHalfDeg (genPoly a) := by
  unfold genPoly
  exact Finset.prod_induction _ CoeffHalfDeg (fun _ _ h₁ h₂ => h₁.mul h₂) coeffHalfDeg_one
    (fun I _ => coeffHalfDeg_factor I (a I))

/-- At the address `x`, the generating polynomial specializes to `(1 + Y)^{N(x)}` over `𝔽₂`. -/
theorem map_eval_genPoly (a : Finset (Fin b) → ℕ) (x : Address b) :
    (genPoly a).map (MvPolynomial.eval x) = (1 + Polynomial.X) ^ expansionNat a x := by
  unfold genPoly expansionNat
  rw [Polynomial.map_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun I _ => ?_
  have hmap : ((bitQ (2 ^ I.card) (a I)).map
      (MvPolynomial.C : ZMod 2 →+* MvPolynomial (Fin b) (ZMod 2))).map (MvPolynomial.eval x) =
      bitQ (2 ^ I.card) (a I) := by
    rw [Polynomial.map_map]
    have : (MvPolynomial.eval x).comp (MvPolynomial.C) = RingHom.id (ZMod 2) :=
      RingHom.ext fun c => eval_C c
    rw [this, Polynomial.map_id]
  rw [Polynomial.map_add, Polynomial.map_one, Polynomial.map_mul, Polynomial.map_C, hmap,
    map_prod]
  simp only [eval_X]
  have hp : ∏ i ∈ I, x i = ((∏ i ∈ I, (x i).val : ℕ) : ZMod 2) := by
    rw [Nat.cast_prod]; simp
  have h01 : (∏ i ∈ I, (x i).val) = 0 ∨ (∏ i ∈ I, (x i).val) = 1 := by
    refine Finset.prod_induction _ (fun n => n = 0 ∨ n = 1) ?_ (Or.inr rfl) ?_
    · rintro m n (rfl | rfl) (rfl | rfl) <;> simp
    · intro i _
      have := ZMod.val_lt (x i)
      omega
  rw [hp]
  rcases h01 with h | h
  · rw [h]; simp
  · rw [h, Nat.cast_one, map_one, one_mul, mul_one, pow_mul, add_pow_char_pow, one_pow]
    unfold bitQ
    ring

/-- **Bit degree, core form** (tex 5672–5676). For natural-number coefficients `a_I`, bit `j` of
`N(x) = Σ_I 2^{|I|} a_I Π_{i∈I} x_i` is represented on `𝔽₂^b` by a polynomial `P` over `𝔽₂` with
`2 · deg P ≤ 2^j`. -/
theorem natBit_expansionNat_degree (a : Finset (Fin b) → ℕ) (j : ℕ) :
    ∃ P : MvPolynomial (Fin b) (ZMod 2), 2 * P.totalDegree ≤ 2 ^ j ∧
      ∀ x : Address b, eval x P = natBit j (expansionNat a x) := by
  refine ⟨(genPoly a).coeff (2 ^ j), coeffHalfDeg_genPoly a (2 ^ j), fun x => ?_⟩
  rw [← Polynomial.coeff_map, map_eval_genPoly, Polynomial.coeff_one_add_X_pow,
    choose_two_pow_eq_natBit]

/-- Bit `j` of a `2`-adic integer: the binary digit of index `j` of its residue modulo `2^{j+1}`. -/
noncomputable def padicBit (j : ℕ) (z : ℤ_[2]) : ZMod 2 :=
  natBit j (PadicInt.toZModPow (j + 1) z).val

/-- Modulo `2^n`, the sign-value function of an element of `ℤ₂[G]` is the residue of a
natural-number expansion `N(x) = Σ_I 2^{|I|} a_I Π_{i∈I} x_i` (from `signEval_expansion`). -/
theorem toZModPow_signEval_eq_expansionNat [Fintype G] (ℓ : G → Address b →+ ZMod 2)
    (α : G → ℤ_[2]) (n : ℕ) :
    ∃ a : Finset (Fin b) → ℕ, ∀ x : Address b,
      PadicInt.toZModPow n (signEval ℓ α x) = (expansionNat a x : ZMod (2 ^ n)) := by
  obtain ⟨a, ha⟩ := signEval_expansion ℓ α
  refine ⟨fun I => (PadicInt.toZModPow n (a I)).val, fun x => ?_⟩
  rw [ha x, expansionNat]
  simp only [map_sum, map_mul, map_pow, map_prod, map_natCast, map_ofNat, Nat.cast_sum,
    Nat.cast_mul, Nat.cast_pow, Nat.cast_prod, Nat.cast_ofNat, ZMod.natCast_zmod_val]

/-- Bit `j` of a natural number only depends on its residue modulo `2^{j+1}`. -/
theorem natBit_mod_two_pow_succ (j N : ℕ) : natBit j (N % 2 ^ (j + 1)) = natBit j N := by
  unfold natBit
  rw [pow_succ, Nat.mod_mul_right_div_self, ZMod.natCast_mod]

/-- `padicBit j z` is bit `j` of any natural number representing `z` modulo `2^{j+1}`. -/
theorem padicBit_eq_natBit {z : ℤ_[2]} {j N : ℕ}
    (h : PadicInt.toZModPow (j + 1) z = (N : ZMod (2 ^ (j + 1)))) :
    padicBit j z = natBit j N := by
  unfold padicBit
  rw [h, ZMod.val_natCast, natBit_mod_two_pow_succ]

/-- **The Boolean bit-degree lemma, low bit** (lane item 1; tex 5672). The low bit of the
sign-value function of an element of `ℤ₂[G]` is constant. -/
theorem padicBit_zero_signEval_const [Fintype G] (ℓ : G → Address b →+ ZMod 2) (α : G → ℤ_[2])
    (x : Address b) : padicBit 0 (signEval ℓ α x) = padicBit 0 (signEval ℓ α 0) := by
  obtain ⟨a, ha⟩ := toZModPow_signEval_eq_expansionNat ℓ α (0 + 1)
  obtain ⟨P, hP, hPe⟩ := natBit_expansionNat_degree a 0
  have hdeg : P.totalDegree = 0 := by
    rw [pow_zero] at hP; omega
  rw [totalDegree_eq_zero_iff_eq_C] at hdeg
  rw [padicBit_eq_natBit (ha x), padicBit_eq_natBit (ha 0), ← hPe, ← hPe, hdeg, eval_C, eval_C]

/-- **The Boolean bit-degree lemma** (lane item 1; tex 5672–5676). Bit `j ≥ 1` of the sign-value
function of an element of `ℤ₂[G]` has Boolean degree at most `2^{j−1}`. -/
theorem padicBit_signEval_hasBoolDegLE [Fintype G] (ℓ : G → Address b →+ ZMod 2)
    (α : G → ℤ_[2]) {j : ℕ} (hj : 1 ≤ j) :
    HasBoolDegLE (fun x => padicBit j (signEval ℓ α x)) (2 ^ (j - 1)) := by
  obtain ⟨a, ha⟩ := toZModPow_signEval_eq_expansionNat ℓ α (j + 1)
  obtain ⟨P, hP, hPe⟩ := natBit_expansionNat_degree a j
  refine ⟨P, ?_, fun x => ?_⟩
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    rw [pow_succ] at hP
    omega
  · rw [hPe]
    exact (padicBit_eq_natBit (ha x)).symm

open Classical in
/-- The indicator of the coefficient equality `A(x) ≡ A(0) (mod 2^M)`. -/
noncomputable def eqIndicator (A : Address b → ℤ_[2]) (M : ℕ) (x : Address b) : ZMod 2 :=
  if (2 : ℤ_[2]) ^ M ∣ A x - A 0 then 1 else 0

/-- The support of the indicator is the solution set of `A(x) ≡ A(0) (mod 2^M)`. -/
theorem eqIndicator_ne_zero_iff (A : Address b → ℤ_[2]) (M : ℕ) (x : Address b) :
    eqIndicator A M x ≠ 0 ↔ (2 : ℤ_[2]) ^ M ∣ A x - A 0 := by
  classical
  unfold eqIndicator
  split_ifs with h
  · simp [h]
  · simp [h]

/-- On `𝔽₂`, `1 + u + v` is the indicator of `u = v`. -/
theorem one_add_add_eq_ite (u v : ZMod 2) : 1 + u + v = if u = v then 1 else 0 := by
  fin_cases u <;> fin_cases v <;> decide

/-- Two natural numbers agree modulo `2^M` iff their bits of index `< M` agree. -/
theorem mod_two_pow_eq_iff (n m M : ℕ) :
    n % 2 ^ M = m % 2 ^ M ↔ ∀ j < M, natBit j n = natBit j m := by
  induction M with
  | zero => simp [Nat.mod_one]
  | succ M ih =>
    rw [Nat.forall_lt_succ_right, ← ih]
    have hbit : natBit M n = natBit M m ↔ n / 2 ^ M % 2 = m / 2 ^ M % 2 :=
      ZMod.natCast_eq_natCast_iff' _ _ 2
    rw [hbit]
    have hd : 2 ^ M ∣ 2 ^ (M + 1) := pow_dvd_pow 2 (Nat.le_succ M)
    constructor
    · intro h
      refine ⟨?_, ?_⟩
      · have := congrArg (· % 2 ^ M) h
        rwa [Nat.mod_mod_of_dvd _ hd, Nat.mod_mod_of_dvd _ hd] at this
      · have := congrArg (· / 2 ^ M) h
        rwa [pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self] at this
    · rintro ⟨h1, h2⟩
      rw [Nat.mod_pow_succ, Nat.mod_pow_succ, h1, h2]

/-- `2^M ∣ z` in `ℤ₂` iff `z` vanishes modulo `2^M`. -/
theorem two_pow_dvd_iff_toZModPow (z : ℤ_[2]) (M : ℕ) :
    (2 : ℤ_[2]) ^ M ∣ z ↔ PadicInt.toZModPow M z = 0 := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]
  norm_num

/-- `Σ_{j < M} ⌊2^j / 2⌋ = 2^{M−1} − 1`. -/
theorem sum_range_two_pow_div_two (M : ℕ) : ∑ j ∈ range M, 2 ^ j / 2 = 2 ^ (M - 1) - 1 := by
  induction M with
  | zero => simp
  | succ M ih =>
    rw [sum_range_succ, ih]
    rcases M with _ | M
    · simp
    · simp only [Nat.add_sub_cancel, pow_succ]
      have := Nat.one_le_two_pow (n := M)
      omega

/-- **One coefficient equality** (tex 5677–5678). The indicator of `A(x) ≡ A(0) (mod 2^M)`, for
the sign-value function `A` of an element of `ℤ₂[G]`, has Boolean degree at most `2^{M−1} − 1`:
its low bit is constant and bits `1, …, M−1` contribute `1 + 2 + ⋯ + 2^{M−2}`. -/
theorem eqIndicator_hasBoolDegLE [Fintype G] (ℓ : G → Address b →+ ZMod 2) (α : G → ℤ_[2])
    (M : ℕ) : HasBoolDegLE (eqIndicator (signEval ℓ α) M) (2 ^ (M - 1) - 1) := by
  classical
  obtain ⟨a, ha⟩ := toZModPow_signEval_eq_expansionNat ℓ α M
  have key : ∀ x, ((2 : ℤ_[2]) ^ M ∣ signEval ℓ α x - signEval ℓ α 0 ↔
      ∀ j ∈ range M, natBit j (expansionNat a x) = natBit j (expansionNat a 0)) := by
    intro x
    rw [two_pow_dvd_iff_toZModPow, map_sub, sub_eq_zero, ha x, ha 0,
      ZMod.natCast_eq_natCast_iff', mod_two_pow_eq_iff]
    simp only [Finset.mem_range]
  have hfun : eqIndicator (signEval ℓ α) M = fun x =>
      ∏ j ∈ range M, (1 + natBit j (expansionNat a x) + natBit j (expansionNat a 0)) := by
    funext x
    simp only [one_add_add_eq_ite]
    rw [Finset.prod_boole]
    unfold eqIndicator
    exact if_congr (key x) rfl rfl
  rw [hfun]
  refine (HasBoolDegLE.prod (range M)
    (fun j x => 1 + natBit j (expansionNat a x) + natBit j (expansionNat a 0))
    (fun j => 2 ^ j / 2) fun j _ => ?_).mono (sum_range_two_pow_div_two M).le
  obtain ⟨P, hP, hPe⟩ := natBit_expansionNat_degree a j
  refine ⟨1 + P + C (natBit j (expansionNat a 0)), ?_, fun x => ?_⟩
  · have h1 := totalDegree_add (1 + P) (C (natBit j (expansionNat a 0)))
    have h2 := totalDegree_add 1 P
    rw [totalDegree_C] at h1
    rw [totalDegree_one] at h2
    have h3 : P.totalDegree ≤ 2 ^ j / 2 := by omega
    exact h1.trans (max_le (h2.trans (max_le (Nat.zero_le _) h3)) (Nat.zero_le _))
  · simp [hPe]

end ZInQ.Manuscript.RC.Boolean
