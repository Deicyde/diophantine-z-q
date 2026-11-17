import ZInQKernel.Contrib.OneProof.RC.Boolean.SignValue
import Mathlib.FieldTheory.ChevalleyWarning
import Mathlib.Algebra.MvPolynomial.Degrees

/-!
# Lane RC1-boolean, part 2: Boolean degree and cube parity

Proof of Proposition `ex:limits-coefficient-transfer` (`diophantine_zq.tex` 5647–5739), the
paragraph at tex 5680–5684:

> If that sum is less than `b`, multiply the complementary indicators of the equations. Its degree
> is less than `b`, so its sum over the Boolean cube is zero: every monomial misses a variable.
> The support of this indicator is the simultaneous solution set. It has even cardinality and
> contains zero, hence another address.

A function `φ : 𝔽₂^b → 𝔽₂` has *Boolean degree at most `d`* when some polynomial over `𝔽₂` of
total degree at most `d` represents it (`HasBoolDegLE`). Because `x_i^2 = x_i` on `𝔽₂`, reducing
exponents never raises the degree, so this is the degree of the unique multilinear representative
(the "terminal polynomial" of Definition `ex:sec7-address`, tex 2216); `HasBoolDegLE` records the
bound, which is all the argument uses.

Main results (kind PROVED):
* `HasBoolDegLE.mul`, `HasBoolDegLE.prod`: degrees add under products ("sum of Boolean degrees");
* `cube_parity_sum`: a Boolean function of degree `< b` sums to zero over the cube (tex 5681–5682;
  this is Mathlib's `MvPolynomial.sum_eval_eq_zero` at `q = 2`, whose proof is exactly "every
  monomial misses a variable");
* `cube_parity`: such a function has support of even cardinality (lane item 2).
-/

namespace ZInQ.Manuscript.RC.Boolean

open Finset MvPolynomial

variable {b : ℕ}

/-- `φ : 𝔽₂^b → 𝔽₂` has *Boolean degree at most `d`*: some polynomial over `𝔽₂` of total degree at
most `d` represents it on the cube. -/
def HasBoolDegLE (φ : Address b → ZMod 2) (d : ℕ) : Prop :=
  ∃ P : MvPolynomial (Fin b) (ZMod 2), P.totalDegree ≤ d ∧ ∀ x : Address b, eval x P = φ x

namespace HasBoolDegLE

theorem mono {φ : Address b → ZMod 2} {d e : ℕ} (h : HasBoolDegLE φ d) (hde : d ≤ e) :
    HasBoolDegLE φ e := by
  obtain ⟨P, hP, hφ⟩ := h
  exact ⟨P, hP.trans hde, hφ⟩

/-- Constant functions have Boolean degree `0`. -/
theorem const (c : ZMod 2) : HasBoolDegLE (b := b) (fun _ => c) 0 :=
  ⟨C c, by simp, fun x => by simp⟩

/-- Degrees add under products. -/
theorem mul {φ ψ : Address b → ZMod 2} {d e : ℕ} (hφ : HasBoolDegLE φ d)
    (hψ : HasBoolDegLE ψ e) : HasBoolDegLE (fun x => φ x * ψ x) (d + e) := by
  obtain ⟨P, hP, hPφ⟩ := hφ
  obtain ⟨Q, hQ, hQψ⟩ := hψ
  exact ⟨P * Q, (totalDegree_mul P Q).trans (Nat.add_le_add hP hQ), fun x => by
    simp [hPφ, hQψ]⟩

/-- Degrees are bounded by the larger one under sums. -/
theorem add {φ ψ : Address b → ZMod 2} {d : ℕ} (hφ : HasBoolDegLE φ d)
    (hψ : HasBoolDegLE ψ d) : HasBoolDegLE (fun x => φ x + ψ x) d := by
  obtain ⟨P, hP, hPφ⟩ := hφ
  obtain ⟨Q, hQ, hQψ⟩ := hψ
  exact ⟨P + Q, (totalDegree_add P Q).trans (max_le hP hQ), fun x => by simp [hPφ, hQψ]⟩

/-- The Boolean degree of a finite product is at most the sum of the Boolean degrees. -/
theorem prod {ι : Type*} (s : Finset ι) (φ : ι → Address b → ZMod 2) (d : ι → ℕ)
    (h : ∀ k ∈ s, HasBoolDegLE (φ k) (d k)) :
    HasBoolDegLE (fun x => ∏ k ∈ s, φ k x) (∑ k ∈ s, d k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using const (b := b) 1
  | insert a s ha ih =>
    have h1 := (h a (mem_insert_self a s)).mul (ih fun k hk => h k (mem_insert_of_mem hk))
    simpa [prod_insert ha, sum_insert ha] using h1

end HasBoolDegLE

/-- **Cube parity, summed form** (tex 5681–5682). A Boolean function of degree less than `b` sums
to zero over the Boolean cube `𝔽₂^b`: every monomial misses a variable. -/
theorem cube_parity_sum {φ : Address b → ZMod 2} {d : ℕ} (h : HasBoolDegLE φ d) (hd : d < b) :
    ∑ x : Address b, φ x = 0 := by
  obtain ⟨P, hP, hPφ⟩ := h
  have hlt : P.totalDegree < (Fintype.card (ZMod 2) - 1) * Fintype.card (Fin b) := by
    rw [ZMod.card, Fintype.card_fin]
    omega
  have := MvPolynomial.sum_eval_eq_zero P hlt
  simpa [hPφ] using this

/-- On `𝔽₂`, the sum of the values of `φ` is the parity of its support. -/
theorem sum_eq_card_support (φ : Address b → ZMod 2) :
    ∑ x : Address b, φ x = ((univ.filter fun x => φ x ≠ 0).card : ZMod 2) := by
  classical
  have h : ∀ s : ZMod 2, s ≠ 0 → s = 1 := by decide
  rw [← sum_filter_ne_zero, card_eq_sum_ones, Nat.cast_sum, Nat.cast_one]
  exact sum_congr rfl fun x hx => h _ (mem_filter.mp hx).2

/-- **Cube parity** (lane item 2; tex 5680–5684). A Boolean function on `𝔽₂^b` of Boolean degree
less than `b` has support of even cardinality. -/
theorem cube_parity {φ : Address b → ZMod 2} {d : ℕ} (h : HasBoolDegLE φ d) (hd : d < b) :
    Even (univ.filter fun x => φ x ≠ 0).card := by
  have h0 := cube_parity_sum h hd
  rw [sum_eq_card_support] at h0
  exact (ZMod.natCast_eq_zero_iff_even).mp h0

end ZInQ.Manuscript.RC.Boolean
