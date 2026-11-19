import ZInQKernel.Contrib.OneProof.RC.Intertwine.Characters
import ZInQKernel.Contrib.OneProof.RC.RelativeAction.Transport

/-! The literal coset extension and its upper generator on both spaces
(tex 8640–8644, 8733–8735, 9021–9026). -/

noncomputable section

namespace ZInQ.Manuscript.RC.Intertwine

open OldStageLaw RelativeAction
open scoped BigOperators

variable {A : Type*} [CommRing A] [Algebra ℚ A] {I₀ : Subring A}
variable (M : IntegralModel I₀)
variable {a : Fin 3 → ℕ} [∀ i, NeZero (2 * a i)]

include M in
theorem coset_exists {x : Fin 3 → A} (hx : dual I₀ a x) :
    ∃ r : Grid a, x - center r ∈ lattice I₀ := by
  have H (i : Fin 3) : ∃ s : ZMod (2 * a i),
      x i - algebraMap ℚ A ((s.val : ℚ) / (2 * a i : ℚ)) ∈ I₀ := by
    let d : ℕ := 2 * a i
    have hd : d ≠ 0 := NeZero.ne _
    have hdq : (d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hd
    obtain ⟨q, hq⟩ := M.approx (x i)
    have hz₀ : algebraMap ℚ A ((d : ℚ) * q) ∈ I₀ := by
      rw [map_mul, map_natCast, ← sub_sub_cancel ((d : A) * x i) ((d : A) * algebraMap ℚ A q),
        ← mul_sub]
      exact I₀.sub_mem (hx i) (I₀.mul_mem (natCast_mem I₀ d) hq)
    obtain ⟨z, hz⟩ := (M.rat_mem _).mp hz₀
    refine ⟨(z : ZMod d), ?_⟩
    have hdcast : (d : ℚ) = 2 * (a i : ℚ) := by simp [d]
    rw [← hdcast]
    have hz' : q - (((z : ZMod d).val : ℚ) / (d : ℚ)) = ((z / (d : ℤ) : ℤ) : ℚ) := by
      have he : (((z : ZMod d).val : ℤ) + (d : ℤ) * (z / (d : ℤ))) = z := by
        rw [ZMod.val_intCast, Int.emod_add_mul_ediv]
      have he' := congrArg (fun t : ℤ => (t : ℚ)) he
      push_cast at he'
      field_simp [hdq] <;> linear_combination hz - he'
    have ht := (M.rat_mem _).mpr ⟨_, hz'⟩
    rw [map_sub] at ht
    rw [show x i - algebraMap ℚ A (((z : ZMod d).val : ℚ) / (d : ℚ)) =
      (x i - algebraMap ℚ A q) +
      (algebraMap ℚ A q - algebraMap ℚ A (((z : ZMod d).val : ℚ) / (d : ℚ))) by abel]
    exact I₀.add_mem hq ht
  choose r hr using H
  exact ⟨r, hr⟩

include M in
theorem coset_unique {x : Fin 3 → A} {r s : Grid a}
    (hr : x - center r ∈ lattice I₀) (hs : x - center s ∈ lattice I₀) : r = s := by
  funext i
  have hd : (0 : ℚ) < (2 * a i : ℕ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne _))
  have rep_range (t : Grid a) : 0 ≤ representative t i ∧ representative t i < 1 := by
    have ht : ((t i).val : ℚ) < ((2 * a i : ℕ) : ℚ) := Nat.cast_lt.mpr (t i).val_lt
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hd ht
    exact ⟨by unfold representative; positivity,
      (div_lt_iff₀ hd).2 (by simpa using ht)⟩
  have hin : algebraMap ℚ A (representative r i - representative s i) ∈ I₀ := by
    rw [map_sub, ← show center r i = algebraMap ℚ A (representative r i) from rfl,
      ← show center s i = algebraMap ℚ A (representative s i) from rfl,
      show center r i - center s i = (x i - center s i) - (x i - center r i) by abel]
    exact I₀.sub_mem (hs i) (hr i)
  obtain ⟨z, hz⟩ := (M.rat_mem _).mp hin
  have hneg : (-1 : ℤ) < z := by
    exact_mod_cast (show (-1 : ℚ) < (z : ℚ) by linarith [(rep_range r).1, (rep_range s).2])
  have hpos : z < (1 : ℤ) := by
    exact_mod_cast (show (z : ℚ) < (1 : ℚ) by linarith [(rep_range r).2, (rep_range s).1])
  have hz₀ : z = 0 := by omega
  have he : representative r i = representative s i := by simpa [hz₀, sub_eq_zero] using hz
  apply ZMod.val_injective _
  unfold representative at he
  have hd' : (2 * a i : ℚ) ≠ 0 := by exact_mod_cast (NeZero.ne (2 * a i))
  exact_mod_cast (div_left_inj' hd').mp he

def residue (x : Fin 3 → A) : Option (Grid a) := by
  classical
  exact if h : dual I₀ a x then some (coset_exists M h).choose else none

theorem residue_eq_some {x : Fin 3 → A} {r : Grid a} :
    residue M x = some r ↔ x - center r ∈ lattice I₀ := by
  classical
  by_cases h : dual I₀ a x
  · rw [residue, dite_eq_left h, Option.some.injEq]
    exact ⟨fun hr => hr ▸ (coset_exists M h).choose_spec,
      fun hr => coset_unique M (coset_exists M h).choose_spec hr⟩
  · rw [residue, dite_eq_right h]
    simp only [reduceCtorEq, false_iff]
    exact fun hr => h (coset_dual r hr)

theorem residue_eq_none {x : Fin 3 → A} :
    residue (a := a) M x = none ↔ ¬ dual I₀ a x := by
  classical
  by_cases h : dual I₀ a x <;> simp [residue, h]

def J : (Grid a → ℂ) →ₗ[ℂ] ((Fin 3 → A) → ℂ) := extendCosets (residue M)

theorem J_injective : Function.Injective (J (a := a) M) := by
  apply extendCosets_injective
  intro r
  exact ⟨center r, (residue_eq_some M).2 (by simp)⟩

/-- The sign is that of the inverse upper lift, so its phase scalar is one. -/
theorem J_twist (n : ℤ) (w : Grid a → ℂ) :
    J M (twist n w) = fun x => finitePhase M (-(n : A) * quad a x) * J M w x := by
  apply extendCosets_twist
  intro x r hx
  exact phase_on_coset M n r ((residue_eq_some M).mp hx)

#print axioms coset_exists
#print axioms coset_unique
#print axioms residue_eq_some
#print axioms residue_eq_none
#print axioms J_injective
#print axioms J_twist

end ZInQ.Manuscript.RC.Intertwine
