import ZInQKernel.Contrib.OneProof.RC.Boolean.BitDegree

/-!
# Lane RC1-boolean, part 5: the missing address and the choice (5.10)

Proof of Proposition `ex:limits-coefficient-transfer` (`diophantine_zq.tex` 5647–5739), tex
5677–5693:

> Thus `q` coefficient equalities modulo `2^M` have sum of Boolean degrees at most `q(2^{M−1}−1)`.
> If that sum is less than `b`, multiply the complementary indicators of the equations. Its degree
> is less than `b`, so its sum over the Boolean cube is zero: every monomial misses a variable. The
> support of this indicator is the simultaneous solution set. It has even cardinality and contains
> zero, hence another address.
>
> Apply this to the coefficients of `f` from `−L_T(M)` through zero and the single constant
> coefficient of `d`. It suffices to choose
> `M > max(c_det, B + 2c_det)`, `b > (L_T(M)+2)(2^M−1)`   (5.10).

Main results (kind PROVED):
* `exists_ne_zero_of_coefficient_equalities`: `q` coefficient equalities modulo `2^M` with
  `q(2^{M−1}−1) < b` have a common nonzero solution (tex 5677–5684);
* `Choice510`, `Choice510.degree_sum_lt`, `choice510_exists`: the choice (5.10) with Elliot's
  constants `L_T(M) = 16(d_K+5)M` and `c_det = a + 4(h_K+2c_E+2t_K)` from (5.9);
* `exists_address_of_choice510`: lane item 3, the system of `q = L_T(M) + 2` equations (the
  coefficients of `f` from `−L_T(M)` through `0` and the constant coefficient of `d`), each of
  Boolean degree at most `2^{M−1} − 1`, has a nonzero solution under (5.10) (tex 5686–5693).
-/

namespace ZInQ.Manuscript.RC.Boolean

open Finset

variable {b : ℕ} {G : Type*} [Fintype G]

/-- **The missing address** (tex 5677–5684; kind PROVED). Given `q = #s` sign-value functions of
elements of `ℤ₂[G]` with `q(2^{M−1} − 1) < b`, there is a nonzero address `x` at which all of them
agree with their values at `0` modulo `2^M`. Proof as in the text: the product of the indicators of
the equations has Boolean degree `< b`, so its support, the simultaneous solution set, has even
cardinality; it contains `0`, hence another address. -/
theorem exists_ne_zero_of_coefficient_equalities {ι : Type*} (ℓ : G → Address b →+ ZMod 2)
    (s : Finset ι) (α : ι → G → ℤ_[2]) (M : ℕ) (h : s.card * (2 ^ (M - 1) - 1) < b) :
    ∃ x : Address b, x ≠ 0 ∧
      ∀ k ∈ s, (2 : ℤ_[2]) ^ M ∣ signEval ℓ (α k) x - signEval ℓ (α k) 0 := by
  classical
  -- the product of the indicators of the equations
  set φ : Address b → ZMod 2 := fun x => ∏ k ∈ s, eqIndicator (signEval ℓ (α k)) M x with hφ
  have hdeg : HasBoolDegLE φ (∑ _k ∈ s, (2 ^ (M - 1) - 1)) :=
    HasBoolDegLE.prod s _ _ fun k _ => eqIndicator_hasBoolDegLE ℓ (α k) M
  rw [sum_const, smul_eq_mul] at hdeg
  -- its support has even cardinality
  have heven := cube_parity hdeg h
  -- and it is the simultaneous solution set
  have hsupp : ∀ x, φ x ≠ 0 ↔
      ∀ k ∈ s, (2 : ℤ_[2]) ^ M ∣ signEval ℓ (α k) x - signEval ℓ (α k) 0 := by
    intro x
    simp only [hφ, prod_ne_zero_iff, eqIndicator_ne_zero_iff]
  -- which contains zero
  have h0 : (0 : Address b) ∈ univ.filter fun x => φ x ≠ 0 := by
    rw [mem_filter, hsupp]
    exact ⟨mem_univ _, fun k _ => by simp⟩
  -- hence another address
  have hcard : 1 < (univ.filter fun x => φ x ≠ 0).card := by
    have hpos : 0 < (univ.filter fun x => φ x ≠ 0).card := card_pos.mpr ⟨0, h0⟩
    obtain ⟨r, hr⟩ := heven
    omega
  obtain ⟨x, hx, hne⟩ := exists_mem_ne hcard 0
  exact ⟨x, hne, (hsupp x).mp (mem_filter.mp hx).2⟩

/-- `L_T(M) = 16(d_K + 5)M`, the uniform bound (5.9) on the negative Laurent support modulo `2^M`
of every sign evaluation `f_x` (tex 5627–5634). -/
def LT (dK M : ℕ) : ℕ := 16 * (dK + 5) * M

/-- `c_det = a + 4(h_K + 2c_E + 2t_K)`, the bound (5.9) on `c = v₂ f_0(0)` (tex 5627). -/
def cDet (a hK cE tK : ℕ) : ℕ := a + 4 * (hK + 2 * cE + 2 * tK)

/-- **The choice (5.10)** (tex 5688–5690):
`M > max(c_det, B + 2c_det)` and `b > (L_T(M) + 2)(2^M − 1)`, where `B` bounds the nonzero-address
central valuations. It refers only to `c_det`, `B` and `d_K`, so it precedes the graph, its theta
precision and the binary family itself (tex 5693). -/
def Choice510 (cdet : ℕ) (B : ℤ) (dK M b : ℕ) : Prop :=
  max (cdet : ℤ) (B + 2 * cdet) < M ∧ (LT dK M + 2) * (2 ^ M - 1) < b

theorem Choice510.cdet_lt {cdet : ℕ} {B : ℤ} {dK M : ℕ} (h : Choice510 cdet B dK M b) :
    cdet < M := by
  have := (max_lt_iff.mp h.1).1
  exact_mod_cast this

theorem Choice510.bound_lt {cdet : ℕ} {B : ℤ} {dK M : ℕ} (h : Choice510 cdet B dK M b) :
    B + 2 * cdet < M :=
  (max_lt_iff.mp h.1).2

/-- Under (5.10) the `q = L_T(M) + 2` equations, each of Boolean degree at most `2^{M−1} − 1`, have
sum of Boolean degrees less than `b` (tex 5677–5690). -/
theorem Choice510.degree_sum_lt {cdet : ℕ} {B : ℤ} {dK M : ℕ} (h : Choice510 cdet B dK M b) :
    (LT dK M + 2) * (2 ^ (M - 1) - 1) < b := by
  refine lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) h.2
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le M 1)) 1


/-- The choice (5.10) can be made: given `c_det`, `B` and `d_K`, take `M` beyond
`max(c_det, B + 2c_det)`, then every `b > (L_T(M)+2)(2^M−1)` works. -/
theorem choice510_exists (cdet : ℕ) (B : ℤ) (dK : ℕ) :
    ∃ M : ℕ, max (cdet : ℤ) (B + 2 * cdet) < M ∧
      ∀ b : ℕ, (LT dK M + 2) * (2 ^ M - 1) < b → Choice510 cdet B dK M b := by
  refine ⟨(max (cdet : ℤ) (B + 2 * cdet)).toNat + 1, ?_, fun b hb => ⟨?_, hb⟩⟩ <;>
  · push_cast
    have := Int.self_le_toNat (max (cdet : ℤ) (B + 2 * cdet))
    omega

/-- The tested coefficients (tex 5686–5687): the coefficients of `f` from `−L` through zero
(indexed by `some i ↦ [t^{−i}] f`, `i = 0, …, L`) and the single constant coefficient of `d`
(`none`); there are `q = L + 2` of them. -/
def testedCoefficients (f d : G → ℤ → ℤ_[2]) (L : ℕ) : Option (Fin (L + 1)) → G → ℤ_[2]
  | none => fun g => d g 0
  | some i => fun g => f g (-(i : ℤ))

/-- **The system of `q = L + 2` tested equations** (tex 5686–5687; kind PROVED). If
`(L + 2)(2^{M−1} − 1) < b`, there is a nonzero address `x` at which the coefficients of `f_x` from
`−L` through `0` and the constant coefficient of `d_x` agree with those of `f_0` and `d_0` modulo
`2^M`. -/
theorem exists_address_of_tested (ℓ : G → Address b →+ ZMod 2) (f d : G → ℤ → ℤ_[2]) (L M : ℕ)
    (h : (L + 2) * (2 ^ (M - 1) - 1) < b) :
    ∃ x : Address b, x ≠ 0 ∧
      (∀ i : ℤ, -(L : ℤ) ≤ i → i ≤ 0 →
        (2 : ℤ_[2]) ^ M ∣ signEval ℓ (fun g => f g i) x - signEval ℓ (fun g => f g i) 0) ∧
      (2 : ℤ_[2]) ^ M ∣ signEval ℓ (fun g => d g 0) x - signEval ℓ (fun g => d g 0) 0 := by
  have hq : (univ : Finset (Option (Fin (L + 1)))).card = L + 2 := by
    simp
  obtain ⟨x, hx, hall⟩ := exists_ne_zero_of_coefficient_equalities ℓ univ
    (testedCoefficients f d L) M (by rw [hq]; exact h)
  refine ⟨x, hx, fun i hi1 hi2 => ?_, hall none (mem_univ _)⟩
  have hk : (-i).toNat < L + 1 := by omega
  have hi : -(((⟨(-i).toNat, hk⟩ : Fin (L + 1)) : ℕ) : ℤ) = i := by
    simp only
    omega
  have := hall (some ⟨(-i).toNat, hk⟩) (mem_univ _)
  simpa only [testedCoefficients, hi] using this

/-- Elliot's constant in (5.10) is more than enough: `(L + 2)(2^M − 1) < b` gives
`(L + 2)(2^{M−1} − 1) < b`. -/
theorem degree_sum_lt_of_lt {L M : ℕ} (h : (L + 2) * (2 ^ M - 1) < b) :
    (L + 2) * (2 ^ (M - 1) - 1) < b := by
  refine lt_of_le_of_lt (Nat.mul_le_mul_left _ ?_) h
  exact Nat.sub_le_sub_right (Nat.pow_le_pow_right (by norm_num) (Nat.sub_le M 1)) 1

/-- **The system of `q = L_T(M) + 2` equations** (lane item 3; tex 5686–5693; kind PROVED). Under
the choice (5.10) there is a nonzero address `x` at which the coefficients of `f_x` from
`−L_T(M)` through `0` and the constant coefficient of `d_x` agree with those of `f_0` and `d_0`
modulo `2^M`. -/
theorem exists_address_of_choice510 (ℓ : G → Address b →+ ZMod 2) (f d : G → ℤ → ℤ_[2])
    {cdet : ℕ} {B : ℤ} {dK M : ℕ} (h : Choice510 cdet B dK M b) :
    ∃ x : Address b, x ≠ 0 ∧
      (∀ i : ℤ, -(LT dK M : ℤ) ≤ i → i ≤ 0 →
        (2 : ℤ_[2]) ^ M ∣ signEval ℓ (fun g => f g i) x - signEval ℓ (fun g => f g i) 0) ∧
      (2 : ℤ_[2]) ^ M ∣ signEval ℓ (fun g => d g 0) x - signEval ℓ (fun g => d g 0) 0 :=
  exists_address_of_tested ℓ f d (LT dK M) M h.degree_sum_lt

/-- **The missing address, in the form the skeleton consumes** (tex 5677–5684; kind PROVED). For
`G = 𝔽₂^b` with the standard pairing and `q` elements `α_j` of `ℤ₂[G]` with `q(2^{M−1} − 1) < b`,
some nonzero address makes all `q` sign-value functions agree with their values at `0` modulo
`2^M`. (This is lane RC0's `BooleanAddress`.) -/
theorem booleanAddress (b M q : ℕ) (α : Fin q → Address b → ℤ_[2])
    (h : q * (2 ^ (M - 1) - 1) < b) :
    ∃ x : Address b, x ≠ 0 ∧ ∀ j, (2 : ℤ_[2]) ^ M ∣
      signEval (dotPairing b) (α j) x - signEval (dotPairing b) (α j) 0 := by
  obtain ⟨x, hx, hall⟩ := exists_ne_zero_of_coefficient_equalities (dotPairing b) univ α M
    (by simpa using h)
  exact ⟨x, hx, fun j => hall j (mem_univ j)⟩

end ZInQ.Manuscript.RC.Boolean
