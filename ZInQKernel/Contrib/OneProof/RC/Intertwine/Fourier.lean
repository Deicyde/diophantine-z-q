import ZInQKernel.Contrib.OneProof.RC.Intertwine.Cosets
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Integration over a translate of the rectangular lattice, including
vanishing off the dual (tex 8643–8657). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine

open OldStageLaw MeasureTheory Set
open scoped BigOperators

variable {A : Type*} [CommRing A] [Algebra ℚ A] {I₀ : Subring A}
variable (M : IntegralModel I₀)
variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

def coset (r : Grid a) : Set (Fin 3 → A) := {x | x - center r ∈ lattice I₀}

def latticeCharacter (y : Fin 3 → A) (x : Fin 3 → A) : ℂ :=
  (lattice I₀ : Set (Fin 3 → A)).indicator (fun z => finitePhase M (polar a z y)) x

omit [Algebra ℚ A] [∀ i, NeZero (2 * a i)] in
theorem polar_add (x t y : Fin 3 → A) :
    polar a (x + t) y = polar a x y + polar a t y := by
  simp [polar, mul_add, add_mul, Finset.sum_add_distrib]

variable [MeasurableSpace (Fin 3 → A)] [MeasurableAdd (Fin 3 → A)]
variable (ν : Measure (Fin 3 → A)) [ν.IsAddLeftInvariant]

open Classical in
theorem lattice_integral (hL : MeasurableSet (lattice I₀ : Set (Fin 3 → A)))
    (y : Fin 3 → A) :
    (∫ x, latticeCharacter (a := a) M y x ∂ν) =
      if dual I₀ a y then (ν.real (lattice I₀) : ℂ) else 0 := by
  classical
  by_cases hy : dual I₀ a y
  · have he := (annihilator_iff (a := a) M y).2 hy
    have hconst := integral_indicator_const (μ := ν) (1 : ℂ) hL
    rw [RCLike.real_smul_eq_coe_mul, mul_one] at hconst
    rw [ite_eq_left hy]
    calc
      _ = ∫ x, (lattice I₀ : Set (Fin 3 → A)).indicator (fun _ => (1 : ℂ)) x ∂ν := by
        congr 1
        funext x
        by_cases hx : x ∈ lattice I₀ <;> simp [latticeCharacter, hx, he]
      _ = _ := hconst
  · have hn := mt (annihilator_iff (a := a) M y).1 hy
    push Not at hn
    obtain ⟨t, ht, ht'⟩ := hn
    have htrans (x : Fin 3 → A) : x + t ∈ lattice I₀ ↔ x ∈ lattice I₀ :=
      (lattice I₀).add_mem_cancel_right ht
    have he (x : Fin 3 → A) : latticeCharacter (a := a) M y (x + t) =
        finitePhase M (polar a t y) * latticeCharacter (a := a) M y x := by
      by_cases hx : x ∈ lattice I₀
      · simp [latticeCharacter, hx, (htrans x).2 hx, polar_add, finitePhase_add, mul_comm]
      · simp [latticeCharacter, hx, mt (htrans x).1 hx]
    have hh := integral_add_left_eq_self (μ := ν) (latticeCharacter (a := a) M y) t
    simp_rw [add_comm t, he, integral_const_mul] at hh
    rw [ite_eq_right hy]
    by_contra h
    exact ht' (mul_right_cancel₀ h (hh.trans (one_mul _).symm))

theorem integrable_coset (r : Grid a) (y : Fin 3 → A)
    (hi : Integrable (latticeCharacter (a := a) M y) ν) :
    Integrable ((coset (I₀ := I₀) r).indicator (fun x => finitePhase M (polar a x y))) ν := by
  have he (x : Fin 3 → A) :
      (coset (I₀ := I₀) r).indicator (fun z => finitePhase M (polar a z y)) x =
        finitePhase M (polar a (center r) y) * latticeCharacter (a := a) M y (x + -center r) := by
    by_cases hx : x - center r ∈ lattice I₀
    · have hp : polar a x y = polar a (center r) y + polar a (x - center r) y := by
        have hsum : center r + (x - center r) = x := by abel
        rw [← polar_add, hsum]
      simp [coset, latticeCharacter, ← sub_eq_add_neg, hx, hp, finitePhase_add]
    · simp [coset, latticeCharacter, ← sub_eq_add_neg, hx]
  rw [show (coset (I₀ := I₀) r).indicator (fun z => finitePhase M (polar a z y)) =
    (fun x => finitePhase M (polar a (center r) y) * latticeCharacter (a := a) M y (x + -center r))
    from funext he]
  exact (hi.comp_add_right _).const_mul _

theorem integrate_coset (r : Grid a) (y : Fin 3 → A) :
    (∫ x, (coset (I₀ := I₀) r).indicator (fun z => finitePhase M (polar a z y)) x ∂ν) =
      finitePhase M (polar a (center r) y) * (∫ x, latticeCharacter (a := a) M y x ∂ν) := by
  rw [← integral_add_left_eq_self (μ := ν)
    ((coset (I₀ := I₀) r).indicator (fun z => finitePhase M (polar a z y))) (center r),
    ← integral_const_mul]
  congr 1
  funext x
  by_cases hx : x ∈ lattice I₀ <;>
    simp [coset, latticeCharacter, hx, polar_add, finitePhase_add]

omit [MeasurableSpace (Fin 3 → A)] [MeasurableAdd (Fin 3 → A)] in
theorem J_mul_character (w : Grid a → ℂ) (x y : Fin 3 → A) :
    J M w x * finitePhase M (polar a x y) =
      ∑ r : Grid a, w r * (coset (I₀ := I₀) r).indicator
        (fun z => finitePhase M (polar a z y)) x := by
  classical
  cases h : residue (a := a) M x with
  | none =>
    have he (r : Grid a) : x ∉ coset (I₀ := I₀) r := fun hr => by
      rw [(residue_eq_some M).2 hr] at h
      contradiction
    simp [J, RelativeAction.extendCosets, h, he]
  | some s =>
    have hs : x ∈ coset (I₀ := I₀) s := (residue_eq_some M).mp h
    rw [Finset.sum_eq_single s]
    · simp [J, RelativeAction.extendCosets, h, hs]
    · intro r _ hr
      have he : x ∉ coset (I₀ := I₀) r := fun hx => hr (coset_unique M hx hs)
      simp [he]
    · simp

def haarFourier (ν : Measure (Fin 3 → A)) (w : (Fin 3 → A) → ℂ) (y : Fin 3 → A) : ℂ :=
  ∫ x, w x * finitePhase M (polar a x y) ∂ν

/-- A single volume determines the comparison. The input is an additive
invariant measure and integrability of the unweighted lattice character. -/
theorem J_fourier (hL : MeasurableSet (lattice I₀ : Set (Fin 3 → A)))
    (hi : ∀ y, Integrable (latticeCharacter (a := a) M y) ν)
    (hvol : (ν.real (lattice I₀) : ℂ) = ∏ i, 1 / (2 * (a i : ℂ)) ^ (1 / 2 : ℂ))
    (w : Grid a → ℂ) :
    J M (finiteFourier w) = haarFourier (a := a) M ν (J M w) := by
  classical
  funext y
  unfold haarFourier
  simp_rw [J_mul_character M w]
  rw [integral_finsetSum _ fun r _ => (integrable_coset M ν r y (hi y)).const_mul _]
  simp_rw [integral_const_mul, integrate_coset M ν, lattice_integral M ν hL]
  cases h : residue (a := a) M y with
  | none =>
    rw [residue_eq_none M] at h
    have hnone := (residue_eq_none (a := a) M).mpr h
    change (residue M y).elim 0 (finiteFourier w) = _
    simp [h, hnone]
  | some s =>
    have hs := (residue_eq_some M).mp h
    change (residue M y).elim 0 (finiteFourier w) = _
    simp only [h, Option.elim_some, finiteFourier, ite_eq_left (coset_dual s hs),
      pairing_on_coset M _ s hs]
    rw [← hvol, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    ring

#print axioms polar_add
#print axioms lattice_integral
#print axioms integrable_coset
#print axioms integrate_coset
#print axioms J_mul_character
#print axioms J_fourier

end ZInQ.Manuscript.RC.Intertwine
