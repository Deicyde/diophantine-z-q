import ZInQKernel.Contrib.OneProof.RC.Boolean.BooleanDegree
import Mathlib.Data.Finset.Interval

/-!
# Lane RC1-boolean, part 2b: Boolean degree is the degree of the multilinear representative

Definition `ex:sec7-address` (`diophantine_zq.tex` 2216) speaks of the *unique multilinear
polynomial over `𝔽₂`* of a function on the cube, and the Boolean degree used at tex 5672–5684 is
its degree. `HasBoolDegLE φ d` (part 2) asks for *some* representing polynomial of total degree at
most `d`. This file proves that the two notions agree (kind PROVED):
* `anf_expansion`: every `φ : 𝔽₂^b → 𝔽₂` is `x ↦ Σ_S c_S Π_{i ∈ S} x_i` with
  `c_S = Σ_{supp y ⊆ S} φ(y)` (`anfCoeff`, Möbius inversion on subsets);
* `anfCoeff_of_expansion`: the multilinear coefficients are unique;
* `hasBoolDegLE_iff_anf`: `HasBoolDegLE φ d` holds exactly when every nonzero multilinear
  coefficient `c_S` has `|S| ≤ d`.

Method. A point of the cube is determined by its support `supp x = {i | x_i ≠ 0}`
(`addrSupportEquiv`), and `x^S = 1` exactly when `S ⊆ supp x` (`cubeMonomial_eq_ite`). Both
expansions then reduce to the parity count `#{T : A ⊆ T ⊆ B} = 2^{|B| - |A|}`, odd exactly when
`A = B` (`sum_ite_subset_subset`). For `hasBoolDegLE_iff_anf`, any polynomial is multilinear on
the cube after `x_i^k = x_i` (`eval_eq_sum_cubeMonomial`), and its coefficients regroup by
supports.
-/

namespace ZInQ.Manuscript.RC.Boolean

open Finset MvPolynomial

variable {b : ℕ}

/-- The monomial `x^S = Π_{i ∈ S} x_i` on `𝔽₂^b`. -/
def cubeMonomial (S : Finset (Fin b)) (x : Address b) : ZMod 2 := ∏ i ∈ S, x i

/-- The coefficient of `x^S` in the unique multilinear polynomial of `φ` (its algebraic normal
form): `c_S = Σ_{y : supp y ⊆ S} φ(y)`. -/
def anfCoeff (φ : Address b → ZMod 2) (S : Finset (Fin b)) : ZMod 2 :=
  ∑ y ∈ univ.filter (fun y : Address b => ∀ i, y i ≠ 0 → i ∈ S), φ y

/-! ### Supports of addresses and the cube monomials -/

/-- Every element of `𝔽₂` is `0` or `1`. -/
private theorem zmod_two_eq_zero_or_one (a : ZMod 2) : a = 0 ∨ a = 1 := by
  revert a; decide

/-- On `𝔽₂`, `a ^ k = a` for every exponent `k ≠ 0`. -/
private theorem zmod_two_pow_eq_self (a : ZMod 2) {k : ℕ} (hk : k ≠ 0) : a ^ k = a := by
  rcases zmod_two_eq_zero_or_one a with rfl | rfl
  · exact zero_pow hk
  · exact one_pow k

/-- The support `supp x = {i | x_i ≠ 0}` of an address. -/
def addrSupport (x : Address b) : Finset (Fin b) := univ.filter fun i => x i ≠ 0

/-- The address with support `S`: the indicator vector of `S`. -/
def addrOfSupport (S : Finset (Fin b)) : Address b := fun i => if i ∈ S then 1 else 0

theorem mem_addrSupport {x : Address b} {i : Fin b} : i ∈ addrSupport x ↔ x i ≠ 0 := by
  simp [addrSupport]

/-- An address is determined by its support: `𝔽₂^b ≃ Finset (Fin b)`. -/
def addrSupportEquiv : Address b ≃ Finset (Fin b) where
  toFun := addrSupport
  invFun := addrOfSupport
  left_inv x := by
    funext i
    simp only [addrOfSupport, mem_addrSupport]
    rcases zmod_two_eq_zero_or_one (x i) with h | h <;> simp [h]
  right_inv S := by
    ext i
    simp [addrOfSupport, mem_addrSupport]

/-- Distinct addresses have distinct supports. -/
theorem addrSupport_injective : Function.Injective (addrSupport (b := b)) :=
  addrSupportEquiv.injective

/-- Summing a function of the support over all addresses is summing it over all subsets. -/
theorem sum_addrSupport {M : Type*} [AddCommMonoid M] (f : Finset (Fin b) → M) :
    ∑ x : Address b, f (addrSupport x) = ∑ S : Finset (Fin b), f S :=
  Equiv.sum_comp addrSupportEquiv f

/-- `x^S = 1` if `S ⊆ supp x`, and `x^S = 0` otherwise. -/
theorem cubeMonomial_eq_ite (S : Finset (Fin b)) (x : Address b) :
    cubeMonomial S x = if S ⊆ addrSupport x then 1 else 0 := by
  unfold cubeMonomial
  split_ifs with h
  · refine prod_eq_one fun i hi => ?_
    have hx : x i ≠ 0 := mem_addrSupport.mp (h hi)
    rcases zmod_two_eq_zero_or_one (x i) with h' | h'
    · exact absurd h' hx
    · exact h'
  · obtain ⟨i, hiS, hi⟩ := not_subset.mp h
    refine prod_eq_zero hiS ?_
    simpa [mem_addrSupport] using hi

/-- `c_S = Σ_{supp y ⊆ S} φ(y)`, written with `addrSupport`. -/
theorem anfCoeff_eq_sum_ite (φ : Address b → ZMod 2) (S : Finset (Fin b)) :
    anfCoeff φ S = ∑ y, if addrSupport y ⊆ S then φ y else 0 := by
  unfold anfCoeff
  rw [sum_filter]
  refine sum_congr rfl fun y _ => ?_
  have hiff : (∀ i, y i ≠ 0 → i ∈ S) ↔ addrSupport y ⊆ S := by
    simp only [subset_iff, mem_addrSupport]
  by_cases h : addrSupport y ⊆ S
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
  · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]

/-- The number of `T` with `A ⊆ T ⊆ B` is odd exactly when `A = B` (it is `2^{|B| - |A|}` when
`A ⊆ B` and `0` otherwise). -/
theorem sum_ite_subset_subset (A B : Finset (Fin b)) :
    ∑ T : Finset (Fin b), (if A ⊆ T ∧ T ⊆ B then (1 : ZMod 2) else 0) =
      if A = B then 1 else 0 := by
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  have hfilt : univ.filter (fun T : Finset (Fin b) => A ⊆ T ∧ T ⊆ B) = Icc A B := by
    ext T
    simp
  rw [hfilt]
  by_cases hAB : A ⊆ B
  · rw [card_Icc_finset hAB]
    by_cases h : A = B
    · subst h; simp
    · rw [ite_eq_right h]
      have hlt : A.card < B.card := card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hAB, h⟩)
      refine (ZMod.natCast_eq_zero_iff_even).mpr ?_
      exact (Nat.even_pow).mpr ⟨even_two, by omega⟩
  · rw [Icc_eq_empty hAB, card_empty, ite_eq_right (fun h : A = B => hAB (h ▸ subset_rfl))]
    simp

/-! ### Existence and uniqueness of the multilinear representative -/

/-- **Existence of the multilinear representative**: `φ(x) = Σ_S c_S x^S`. -/
theorem anf_expansion (φ : Address b → ZMod 2) (x : Address b) :
    φ x = ∑ S : Finset (Fin b), anfCoeff φ S * cubeMonomial S x := by
  have key : ∀ S : Finset (Fin b), anfCoeff φ S * cubeMonomial S x =
      ∑ y, φ y * (if addrSupport y ⊆ S ∧ S ⊆ addrSupport x then 1 else 0) := by
    intro S
    rw [anfCoeff_eq_sum_ite, cubeMonomial_eq_ite, sum_mul]
    refine sum_congr rfl fun y _ => ?_
    by_cases h1 : addrSupport y ⊆ S <;> by_cases h2 : S ⊆ addrSupport x <;> simp [h1, h2]
  simp only [key]
  rw [sum_comm]
  simp only [← mul_sum]
  simp only [sum_ite_subset_subset, addrSupport_injective.eq_iff, mul_ite, mul_one, mul_zero]
  exact (Fintype.sum_ite_eq' x φ).symm

/-- **Uniqueness of the multilinear representative**: the coefficients of any multilinear
representation `φ = Σ_S c_S x^S` are the `anfCoeff φ S`. -/
theorem anfCoeff_of_expansion (c : Finset (Fin b) → ZMod 2) (φ : Address b → ZMod 2)
    (h : ∀ x, φ x = ∑ S : Finset (Fin b), c S * cubeMonomial S x) :
    ∀ S, anfCoeff φ S = c S := by
  intro S
  rw [anfCoeff_eq_sum_ite]
  have key : ∀ y : Address b, (if addrSupport y ⊆ S then φ y else 0) =
      ∑ U, c U * (if U ⊆ addrSupport y ∧ addrSupport y ⊆ S then 1 else 0) := by
    intro y
    rw [h y]
    by_cases hy : addrSupport y ⊆ S
    · rw [ite_eq_left hy]
      refine sum_congr rfl fun U _ => ?_
      rw [cubeMonomial_eq_ite]
      by_cases hU : U ⊆ addrSupport y <;> simp [hU, hy]
    · rw [ite_eq_right hy]
      symm
      refine sum_eq_zero fun U _ => ?_
      simp [hy]
  have hcount : ∀ U : Finset (Fin b),
      ∑ y : Address b, (if U ⊆ addrSupport y ∧ addrSupport y ⊆ S then (1 : ZMod 2) else 0) =
        if U = S then 1 else 0 := by
    intro U
    rw [← sum_ite_subset_subset U S]
    exact sum_addrSupport (fun T => if U ⊆ T ∧ T ⊆ S then (1 : ZMod 2) else 0)
  simp only [key]
  rw [sum_comm]
  simp only [← mul_sum]
  simp only [hcount, mul_ite, mul_one, mul_zero]
  exact Fintype.sum_ite_eq' S c

/-! ### Boolean degree -/

/-- On the cube, a polynomial over `𝔽₂` is `Σ_{e ∈ supp P} coeff_e(P) x^{supp e}`
(because `x_i^k = x_i` for `k ≥ 1`). -/
theorem eval_eq_sum_cubeMonomial (P : MvPolynomial (Fin b) (ZMod 2)) (x : Address b) :
    eval x P = ∑ e ∈ P.support, P.coeff e * cubeMonomial e.support x := by
  rw [eval_eq]
  refine sum_congr rfl fun e _ => ?_
  congr 1
  exact prod_congr rfl fun i hi => zmod_two_pow_eq_self (x i) (Finsupp.mem_support_iff.mp hi)

/-- **`HasBoolDegLE` is the Boolean degree**: `φ` has a representing polynomial of total degree at
most `d` exactly when its unique multilinear polynomial has degree at most `d`. -/
theorem hasBoolDegLE_iff_anf (φ : Address b → ZMod 2) (d : ℕ) :
    HasBoolDegLE φ d ↔ ∀ S : Finset (Fin b), anfCoeff φ S ≠ 0 → S.card ≤ d := by
  constructor
  · rintro ⟨P, hPd, hPφ⟩ S hS
    -- regroup the terms of `P` by the supports of their exponent vectors
    have hexp : ∀ x, φ x = ∑ T : Finset (Fin b),
        (∑ e ∈ P.support with e.support = T, P.coeff e) * cubeMonomial T x := by
      intro x
      rw [← hPφ x, eval_eq_sum_cubeMonomial]
      simp only [sum_mul]
      rw [← sum_fiberwise P.support (fun e => e.support)
        (fun e => P.coeff e * cubeMonomial e.support x)]
      refine sum_congr rfl fun T _ => sum_congr rfl fun e he => ?_
      rw [(mem_filter.mp he).2]
    rw [anfCoeff_of_expansion _ φ hexp S] at hS
    obtain ⟨e, he, -⟩ := exists_ne_zero_of_sum_ne_zero hS
    obtain ⟨heP, rfl⟩ := mem_filter.mp he
    calc e.support.card = ∑ i ∈ e.support, 1 := card_eq_sum_ones _
      _ ≤ ∑ i ∈ e.support, e i :=
          sum_le_sum fun i hi => Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
      _ = e.sum fun _ k => k := rfl
      _ ≤ P.totalDegree := le_totalDegree heP
      _ ≤ d := hPd
  · intro hd
    refine ⟨∑ S : Finset (Fin b), C (anfCoeff φ S) * ∏ i ∈ S, X i, ?_, fun x => ?_⟩
    · refine totalDegree_finsetSum_le fun S _ => ?_
      by_cases h0 : anfCoeff φ S = 0
      · simp [h0]
      · calc (C (anfCoeff φ S) * ∏ i ∈ S, X i : MvPolynomial (Fin b) (ZMod 2)).totalDegree
            ≤ (C (anfCoeff φ S) : MvPolynomial (Fin b) (ZMod 2)).totalDegree +
                (∏ i ∈ S, X i : MvPolynomial (Fin b) (ZMod 2)).totalDegree :=
              totalDegree_mul _ _
          _ ≤ 0 + ∑ i ∈ S, (X i : MvPolynomial (Fin b) (ZMod 2)).totalDegree := by
              rw [totalDegree_C]; exact Nat.add_le_add_left (totalDegree_finsetProd _ _) _
          _ = S.card := by simp
          _ ≤ d := hd S h0
    · rw [anf_expansion φ x]
      simp [cubeMonomial]

end ZInQ.Manuscript.RC.Boolean
