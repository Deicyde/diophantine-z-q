import ZInQKernel.Contrib.OneProof.RC.OldStageLaw.Grid
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-! The integral subgroup and rational representatives of a finite additive
quotient. The calculation with representatives is on-the-spot (c) for
tex 8640–8647. Work in coordinates divided by the nonzero lattice step. -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine

open OldStageLaw Complex
open scoped BigOperators Real

variable {A : Type*} [CommRing A] [Algebra ℚ A]

/-- Two arithmetic properties of the finite adèles and their integral subring.
Neither mentions a quadratic form or an operator. -/
structure IntegralModel (I : Subring A) : Prop where
  rat_mem : ∀ q : ℚ, algebraMap ℚ A q ∈ I ↔ ∃ z : ℤ, q = z
  approx : ∀ x : A, ∃ q : ℚ, x - algebraMap ℚ A q ∈ I

def rationalPhase (q : ℚ) : ℂ := Complex.exp (-(2 * π * Complex.I) * (q : ℂ))

theorem rationalPhase_add (q r : ℚ) :
    rationalPhase (q + r) = rationalPhase q * rationalPhase r := by
  simp only [rationalPhase, Rat.cast_add, mul_add, Complex.exp_add]

theorem rationalPhase_eq_one (q : ℚ) :
    rationalPhase q = 1 ↔ ∃ z : ℤ, q = z := by
  unfold rationalPhase
  rw [Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨-z, ?_⟩
    have hc : (2 * π * Complex.I : ℂ) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
    have he : (2 * π * Complex.I : ℂ) * (q : ℂ) =
        (2 * π * Complex.I : ℂ) * (-(z : ℂ)) := by linear_combination -hz
    have he' := mul_left_cancel₀ hc he
    exact_mod_cast he'
  · rintro ⟨z, rfl⟩
    refine ⟨-z, ?_⟩
    push_cast
    ring

theorem rationalPhase_congr {q r : ℚ} (h : ∃ z : ℤ, q - r = z) :
    rationalPhase q = rationalPhase r := by
  rw [← sub_add_cancel q r, rationalPhase_add, (rationalPhase_eq_one _).mpr h, one_mul]

variable {I₀ : Subring A} (M : IntegralModel I₀)

/-- The character on the finite integral quotient, with the negative real
phase on rational representatives. -/
def finitePhase (x : A) : ℂ := rationalPhase (M.approx x).choose

theorem finitePhase_spec {x : A} {q : ℚ}
    (h : x - algebraMap ℚ A q ∈ I₀) : finitePhase M x = rationalPhase q := by
  apply rationalPhase_congr
  apply (M.rat_mem _).mp
  rw [map_sub, show algebraMap ℚ A (M.approx x).choose - algebraMap ℚ A q =
    (x - algebraMap ℚ A q) - (x - algebraMap ℚ A (M.approx x).choose) by abel]
  exact I₀.sub_mem h (M.approx x).choose_spec

theorem finitePhase_add (x y : A) :
    finitePhase M (x + y) = finitePhase M x * finitePhase M y := by
  rw [finitePhase_spec M (q := (M.approx x).choose + (M.approx y).choose),
    rationalPhase_add, finitePhase, finitePhase]
  rw [map_add, show x + y - (algebraMap ℚ A (M.approx x).choose +
    algebraMap ℚ A (M.approx y).choose) =
    (x - algebraMap ℚ A (M.approx x).choose) +
    (y - algebraMap ℚ A (M.approx y).choose) by abel]
  exact I₀.add_mem (M.approx x).choose_spec (M.approx y).choose_spec

theorem finitePhase_eq_one (x : A) : finitePhase M x = 1 ↔ x ∈ I₀ := by
  constructor
  · intro h
    obtain ⟨z, hz⟩ := (rationalPhase_eq_one _).mp h
    exact sub_add_cancel x _ ▸ I₀.add_mem (M.approx x).choose_spec ((M.rat_mem _).mpr ⟨z, hz⟩)
  · intro h
    rw [finitePhase_spec M (q := 0) (by simpa using h), rationalPhase_eq_one]
    exact ⟨0, by simp⟩

/-- A finite sum of rational local representatives gives the product
of their negative real phases. -/
theorem finitePhase_eq_product {P : Type*} (S : Finset P)
    (q : P → ℚ) {x : A} (hx : x - algebraMap ℚ A (∑ p ∈ S, q p) ∈ I₀) :
    finitePhase M x = ∏ p ∈ S, rationalPhase (q p) := by
  rw [finitePhase_spec M hx]
  clear hx
  classical
  induction S using Finset.induction_on with
  | empty => simp [rationalPhase]
  | @insert p S hp ih =>
    rw [Finset.sum_insert hp, Finset.prod_insert hp, rationalPhase_add, ih]

variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

def representative (r : Grid a) (i : Fin 3) : ℚ := (r i).val / (2 * a i : ℚ)

def center (r : Grid a) (i : Fin 3) : A := algebraMap ℚ A (representative r i)

def lattice (I₀ : Subring A) : AddSubgroup (Fin 3 → A) where
  carrier := {x | ∀ i, x i ∈ I₀}
  zero_mem' := fun _ => I₀.zero_mem
  add_mem' hx hy := fun i => I₀.add_mem (hx i) (hy i)
  neg_mem' hx := fun i => I₀.neg_mem (hx i)

def dual (I₀ : Subring A) (a : Fin 3 → ℕ) (x : Fin 3 → A) : Prop :=
  ∀ i, ((2 * a i : ℕ) : A) * x i ∈ I₀

def quad (a : Fin 3 → ℕ) (x : Fin 3 → A) : A := ∑ i, (a i : A) * (x i)^2

def polar (a : Fin 3 → ℕ) (x y : Fin 3 → A) : A := ∑ i, ((2 * a i : ℕ) : A) * x i * y i

theorem center_mul (r : Grid a) (i : Fin 3) :
    ((2 * a i : ℕ) : A) * center r i = (r i).val := by
  have hd : (2 * a i : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne (2 * a i))
  have hq : ((2 * a i : ℕ) : ℚ) * representative r i = (r i).val := by
    unfold representative
    push_cast
    exact mul_div_cancel₀ _ hd
  simpa only [map_mul, map_natCast, center] using congrArg (algebraMap ℚ A) hq

theorem coset_dual (r : Grid a) {x : Fin 3 → A} (hx : x - center r ∈ lattice I₀) :
    dual I₀ a x := by
  intro i
  have hi : x i - center r i ∈ I₀ := hx i
  have h := I₀.add_mem (I₀.mul_mem (natCast_mem I₀ (2 * a i)) hi)
    (natCast_mem I₀ (r i).val)
  rwa [← center_mul (A := A) r i, ← mul_add, sub_add_cancel] at h

theorem phase_on_coset (n : ℤ) (r : Grid a) {x : Fin 3 → A}
    (hx : x - center r ∈ lattice I₀) :
    finitePhase M ((-(n : A)) * quad a x) = kernel (n : ℂ) (energy r) := by
  let q : ℚ := ∑ i, (a i : ℚ) * representative r i ^ 2
  have hq : quad a (center r) = algebraMap ℚ A q := by
    simp [q, quad, center]
  have hdiff : quad a x - quad a (center r) ∈ I₀ := by
    rw [quad, quad, ← Finset.sum_sub_distrib]
    apply I₀.sum_mem
    intro i _
    have hi : x i - center r i ∈ I₀ := hx i
    rw [show (a i : A) * x i ^ 2 - (a i : A) * center r i ^ 2 =
      (a i : A) * (x i - center r i)^2 +
      (((2 * a i : ℕ) : A) * center r i) * (x i - center r i) by push_cast; ring,
      center_mul]
    exact I₀.add_mem (I₀.mul_mem (natCast_mem I₀ _) (I₀.pow_mem hi _))
      (I₀.mul_mem (natCast_mem I₀ _) hi)
  rw [finitePhase_spec M (q := -(n : ℚ) * q)]
  · have hr : (q : ℝ) = energy r := by
      simp only [q, energy, offset, representative, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
        Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
    unfold rationalPhase kernel
    rw [Rat.cast_mul, Rat.cast_neg, Rat.cast_intCast, ← hr, ← RCLike.ofReal_ratCast (K := ℂ)]
    congr 1
    ring_nf <;> rfl
  · rw [map_mul, map_neg, map_intCast, ← hq, ← mul_sub]
    exact I₀.mul_mem (I₀.neg_mem (intCast_mem I₀ n)) hdiff

theorem annihilator_iff (y : Fin 3 → A) :
    (∀ x ∈ lattice I₀, finitePhase M (polar a x y) = 1) ↔ dual I₀ a y := by
  classical
  simp only [finitePhase_eq_one]
  constructor
  · intro h i
    have he := h (Pi.single i 1) (fun j => by
      by_cases e : j = i <;> simp [Pi.single_apply, e])
    have hh : polar a (Pi.single i 1) y = ((2 * a i : ℕ) : A) * y i := by
      classical
      simp [polar, Pi.single_apply, mul_ite, ite_mul, Finset.sum_ite_eq']
    rwa [hh] at he
  · intro h x hx
    apply I₀.sum_mem
    intro i _
    rw [mul_right_comm]
    exact I₀.mul_mem (h i) (hx i)

theorem pairing_on_coset (r s : Grid a) {y : Fin 3 → A}
    (hy : y - center s ∈ lattice I₀) :
    finitePhase M (polar a (center r) y) = pairing r s := by
  let q : Fin 3 → ℚ := fun i => (r i).val * representative s i
  have hdiff : polar a (center r) y - algebraMap ℚ A (∑ i, q i) ∈ I₀ := by
    simp only [polar, center_mul, map_sum, q, map_mul, map_natCast, ← Finset.sum_sub_distrib]
    apply I₀.sum_mem
    intro i _
    change (↑(r i).val : A) * y i - (↑(r i).val : A) * center s i ∈ I₀
    rw [← mul_sub]
    exact I₀.mul_mem (natCast_mem I₀ _) (hy i)
  rw [finitePhase_spec M hdiff]
  simp only [rationalPhase, Rat.cast_sum, Finset.mul_sum, Complex.exp_sum, pairing]
  apply Finset.prod_congr rfl
  intro i _
  have he : -(r i * s i) = ((-((r i).val : ℤ) * (s i).val : ℤ) : ZMod (2 * a i)) := by
    push_cast
    simp
  rw [he, ZMod.stdAddChar_coe]
  push_cast [q, representative]
  congr 1
  ring

#print axioms rationalPhase_add
#print axioms rationalPhase_eq_one
#print axioms rationalPhase_congr
#print axioms finitePhase_spec
#print axioms finitePhase_add
#print axioms finitePhase_eq_one
#print axioms finitePhase_eq_product
#print axioms center_mul
#print axioms coset_dual
#print axioms phase_on_coset
#print axioms annihilator_iff
#print axioms pairing_on_coset

end ZInQ.Manuscript.RC.Intertwine
