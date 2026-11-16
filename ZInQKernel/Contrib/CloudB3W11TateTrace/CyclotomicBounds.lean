import ZInQKernel.Contrib.CloudB3W11TateTrace.CyclotomicTrace
import ZInQKernel.Contrib.CloudB3W11TateTrace.TraceComparison
import ZInQKernel.Contrib.CloudB3W11TateTrace.ContinuousTrace

/-!
# Unconditional uniform bounds for genuine cyclotomic normalized trace

The arithmetic hypotheses here are PROVED, supplied by the kernel-compiled
cyclotomic degree and one-step trace estimates. The comparison with Mathlib
normalized trace was proved in `TraceComparison`, not postulated.

The first bound is uniform in source and target levels of the cofinal tower
`ℚ_p(μ_{p^{n+2}})`. The second extends it to all target levels, including
`n = 0,1`, using bounded finite-dimensional trace maps on the fixed level 2.
This proves `UniformNormalizedTraceBound p ⊥` with an honest witness. No bound
for arbitrary finite `K/ℚ_p` is claimed here; the whole-group twist proof and
finite-index descent avoid needing that additional statement.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.CloudB3W11TateTrace

open CyclotomicTrace.TCT TraceConstruction.TNT

variable (p : ℕ) [Fact p.Prime]

/-- Explicit arithmetic hypotheses for the actual cofinal cyclotomic tower;
every field is supplied by a proved theorem. -/
theorem cyclotomicArithmeticHyp : Hyp p (CyclotomicTrace.TCT.F p) (CyclotomicTrace.TCT.c p)
    ((p : ℝ) ^ (1 / ((p : ℝ) - 1) ^ 2)) :=
  ⟨CyclotomicTrace.TCT.F_mono p, finiteDimensional_F p,
    (fun n σ _ y hy => stable p n σ y hy), hdeg p, hcyc p,
    one_le_c p, prod_c_le p, htr p⟩

/-- An explicit uniform bound, independent of BOTH source and target levels. -/
def cyclotomicTraceBound : ℝ :=
  max 1 (‖(p : ℚ_[p])‖⁻¹ * (p : ℝ) ^ (1 / ((p : ℝ) - 1) ^ 2))

theorem one_le_cyclotomicTraceBound : 1 ≤ cyclotomicTraceBound p := le_max_left _ _

/-- Genuine normalized trace to level `m+2` is uniformly bounded on all
algebraic points of the cyclotomic tower. -/
theorem norm_cyclotomic_normalizedTrace_le (m : ℕ) (y : PadicAlgCl p)
    (hy : ∃ n : ℕ, y ∈ PadicAlgCl.cyclotomicTower p n) :
    ‖traceRetraction ℚ_[p] (PadicAlgCl p) (rootField p (m + 2)) y‖ ≤
      cyclotomicTraceBound p * ‖y‖ := by
  obtain ⟨n, hn⟩ := hy
  have hn' : y ∈ CyclotomicTrace.TCT.F p n :=
    PadicAlgCl.cyclotomicTower_mono p (Nat.le_add_right n 2) hn
  exact norm_normalizedTrace_le_of_arithmetic_hyp p (cyclotomicArithmeticHyp p) m y hn'

/-- Uniform normalized trace retractions on the PURE cyclotomic tower,
including its initial levels. The general finite-base version is not assumed. -/
theorem uniformNormalizedTraceBound_bot :
    UniformNormalizedTraceBound p (⊥ : IntermediateField ℚ_[p] (PadicAlgCl p)) := by
  let f0 : rootField p 2 →L[ℚ_[p]] PadicAlgCl p :=
    ((traceRetraction ℚ_[p] (PadicAlgCl p) (rootField p 0)).comp
      (rootField p 2).val.toLinearMap).toContinuousLinearMap
  let f1 : rootField p 2 →L[ℚ_[p]] PadicAlgCl p :=
    ((traceRetraction ℚ_[p] (PadicAlgCl p) (rootField p 1)).comp
      (rootField p 2).val.toLinearMap).toContinuousLinearMap
  let M : ℝ := max 1 (‖f0‖ + ‖f1‖)
  have hM : 1 ≤ M := le_max_left _ _
  have hM0 : 0 ≤ M := zero_le_one.trans hM
  have hf0 : ‖f0‖ ≤ M :=
    (le_add_of_nonneg_right (norm_nonneg f1)).trans (le_max_right _ _)
  have hf1 : ‖f1‖ ≤ M :=
    (le_add_of_nonneg_left (norm_nonneg f0)).trans (le_max_right _ _)
  have hB : 1 ≤ cyclotomicTraceBound p := one_le_cyclotomicTraceBound p
  refine ⟨M * cyclotomicTraceBound p, ?_, fun n x => ?_⟩
  · nlinarith
  · have hx : ∃ j : ℕ, (x : PadicAlgCl p) ∈ PadicAlgCl.cyclotomicTower p j := by
      obtain ⟨j, hj⟩ := (mem_cyclotomicTower_iff p ⊥ (x : PadicAlgCl p)).mp x.property
      refine ⟨j, ?_⟩
      simpa [cyclotomicLevel, rootField, PadicAlgCl.cyclotomicTower] using hj
    have h2 := norm_cyclotomic_normalizedTrace_le p 0 (x : PadicAlgCl p) hx
    let y : rootField p 2 :=
      ⟨traceRetraction ℚ_[p] (PadicAlgCl p) (rootField p 2) (x : PadicAlgCl p),
        traceRetraction_mem ℚ_[p] (PadicAlgCl p) (rootField p 2) (x : PadicAlgCl p)⟩
    have hy : ‖y‖ ≤ cyclotomicTraceBound p * ‖x‖ := h2
    have hsmall (j : ℕ) (hj : j ≤ 2)
        (f : rootField p 2 →L[ℚ_[p]] PadicAlgCl p)
        (hf : ∀ z : rootField p 2,
          f z = traceRetraction ℚ_[p] (PadicAlgCl p) (rootField p j) (z : PadicAlgCl p))
        (hfn : ‖f‖ ≤ M) :
        ‖traceRetraction ℚ_[p] (PadicAlgCl p) (rootField p j) (x : PadicAlgCl p)‖ ≤
          M * cyclotomicTraceBound p * ‖x‖ := by
      have heq : f y = traceRetraction ℚ_[p] (PadicAlgCl p) (rootField p j) (x : PadicAlgCl p) := by
        rw [hf]
        exact traceRetraction_comp_of_le ℚ_[p] (PadicAlgCl p) _ _ (rootField_mono p hj) _
      rw [← heq]
      calc
        ‖f y‖ ≤ ‖f‖ * ‖y‖ := f.le_opNorm y
        _ ≤ M * ‖y‖ := mul_le_mul_of_nonneg_right hfn (norm_nonneg y)
        _ ≤ M * (cyclotomicTraceBound p * ‖x‖) := mul_le_mul_of_nonneg_left hy hM0
        _ = M * cyclotomicTraceBound p * ‖x‖ := by ring
    change ‖traceRetraction ℚ_[p] (PadicAlgCl p) (cyclotomicLevel p ⊥ n) (x : PadicAlgCl p)‖ ≤ _
    simp only [cyclotomicLevel, bot_sup_eq]
    cases n with
    | zero => exact hsmall 0 (by omega) f0 (fun _ => rfl) hf0
    | succ n =>
      cases n with
      | zero => exact hsmall 1 (by omega) f1 (fun _ => rfl) hf1
      | succ j =>
        have hlarge :
            ‖traceRetraction ℚ_[p] (PadicAlgCl p) (rootField p (j + 2)) (x : PadicAlgCl p)‖ ≤
              cyclotomicTraceBound p * ‖x‖ :=
          norm_cyclotomic_normalizedTrace_le p j (x : PadicAlgCl p) hx
        have hMB : cyclotomicTraceBound p ≤ M * cyclotomicTraceBound p := by nlinarith
        exact hlarge.trans (mul_le_mul_of_nonneg_right hMB (norm_nonneg x))

end ZInQ.Contrib.CloudB3W11TateTrace
