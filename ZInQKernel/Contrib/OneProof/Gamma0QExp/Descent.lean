import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_X0
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Definitions.Def_ModularCurve_LaurentCoeff
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Complex.Basic

/-!
# gamma0-qexp, part 1: descent from `ℂ((q))` to `ℚ((q))`

If a Laurent series `x ∈ ℚ((q))` satisfies a relation `B·x = A` in `ℂ((q))` where `B ≠ 0` and `A`
are `ℂ`-linear combinations of elements of a subfield `F ⊆ ℚ((q))`, then `x ∈ F`: apply a
`ℚ`-linear functional `λ : ℂ → ℚ` with `λ(B_m) ≠ 0` (for one nonzero coefficient `B_m`) to the
coefficients of the relation.

No `sorry`, no `axiom`.
-/

noncomputable section

open ModularCurve

namespace ZInQ.Gamma0QExp

theorem coeff_C_mul {R : Type*} [CommRing R] (c : R) (y : LaurentSeries R) (m : ℤ) :
    (HahnSeries.C c * y).coeff m = c * y.coeff m := by
  rw [HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem coeff_sum_C_mul {R : Type*} [CommRing R] {ι : Type*} (s : Finset ι) (β : ι → R)
    (u : ι → LaurentSeries R) (m : ℤ) :
    (∑ i ∈ s, HahnSeries.C (β i) * u i).coeff m = ∑ i ∈ s, β i * (u i).coeff m := by
  rw [HahnSeries.coeff_sum]
  exact Finset.sum_congr rfl fun i _ => coeff_C_mul _ _ _

/-- **Descent.** -/
theorem mem_of_complex_relation (F : IntermediateField ℚ (LaurentSeries ℚ)) {ι : Type*}
    (s : Finset ι) (u v : ι → LaurentSeries ℚ) (hu : ∀ i ∈ s, u i ∈ F) (hv : ∀ i ∈ s, v i ∈ F)
    (β α : ι → ℂ) (x : LaurentSeries ℚ)
    (hrel : (∑ i ∈ s, HahnSeries.C (β i) * coeffEmb ℂ (u i)) * coeffEmb ℂ x =
      ∑ i ∈ s, HahnSeries.C (α i) * coeffEmb ℂ (v i))
    (hne : ∑ i ∈ s, HahnSeries.C (β i) * coeffEmb ℂ (u i) ≠ 0) : x ∈ F := by
  classical
  obtain ⟨m₀, hm₀⟩ : ∃ m₀, (∑ i ∈ s, HahnSeries.C (β i) * coeffEmb ℂ (u i)).coeff m₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (HahnSeries.ext (funext h))
  set w := (∑ i ∈ s, HahnSeries.C (β i) * coeffEmb ℂ (u i)).coeff m₀
  obtain ⟨l, hl⟩ : ∃ l : Module.Dual ℚ ℂ, l w ≠ 0 := by
    by_contra h
    push Not at h
    exact hm₀ ((Module.forall_dual_apply_eq_zero_iff ℚ w).1 h)
  have hlr : ∀ (c : ℂ) (r : ℚ), l (c * (r : ℂ)) = l c * r := by
    intro c r
    rw [mul_comm c, ← smul_eq_mul, show ((r : ℂ) • c) = r • c from (Rat.smul_def r c).symm,
      map_smul, smul_eq_mul, mul_comm]
  have hemb : ∀ (y : LaurentSeries ℚ) (m : ℤ), (coeffEmb ℂ y).coeff m = ((y.coeff m : ℚ) : ℂ) :=
    fun y m => by rw [coeffEmb_coeff]; rfl
  set B : LaurentSeries ℚ := ∑ i ∈ s, HahnSeries.C (l (β i)) * u i
  set A : LaurentSeries ℚ := ∑ i ∈ s, HahnSeries.C (l (α i)) * v i
  have hsm : ∀ (c : ℚ) (y : LaurentSeries ℚ), y ∈ F → HahnSeries.C c * y ∈ F := fun c y hy => by
    rw [show HahnSeries.C c = algebraMap ℚ (LaurentSeries ℚ) c from
      (algebraMap_apply_eq_single c).symm]
    exact F.mul_mem (F.algebraMap_mem c) hy
  have hB : B ∈ F := F.sum_mem fun i hi => hsm _ _ (hu i hi)
  have hA : A ∈ F := F.sum_mem fun i hi => hsm _ _ (hv i hi)
  have hrelq : B * x = A := by
    ext m
    have h1 := congrArg (fun z : LaurentSeries ℂ => l (z.coeff m)) hrel
    have hBx : B * x = ∑ i ∈ s, HahnSeries.C (l (β i)) * (u i * x) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => mul_assoc _ _ _
    have hBx' : (∑ i ∈ s, HahnSeries.C (β i) * coeffEmb ℂ (u i)) * coeffEmb ℂ x =
        ∑ i ∈ s, HahnSeries.C (β i) * coeffEmb ℂ (u i * x) := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by rw [mul_assoc, map_mul]
    simp only [hBx', coeff_sum_C_mul, hemb, map_sum, hlr] at h1
    rw [hBx, coeff_sum_C_mul, coeff_sum_C_mul]
    exact h1
  have hBne : B ≠ 0 := by
    intro h0
    have h1 : B.coeff m₀ = 0 := by rw [h0]; rfl
    rw [coeff_sum_C_mul] at h1
    apply hl
    simp only [w, coeff_sum_C_mul, hemb, map_sum, hlr]
    exact h1
  have hx : x = A / B := by rw [← hrelq, mul_div_cancel_left₀ _ hBne]
  rw [hx]
  exact F.div_mem hA hB

end ZInQ.Gamma0QExp
