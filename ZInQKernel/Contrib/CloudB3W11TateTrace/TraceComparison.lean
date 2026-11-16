import ZInQKernel.Contrib.CloudB3W11TateTrace.AlgebraicTrace
import ZInQKernel.Contrib.CloudB3W11TateTrace.TraceConstruction

/-!
# The constructed Tate operator is the genuine Mathlib normalized trace

This comparison prevents an abstract retraction from being silently substituted
for normalized trace. On every algebraic point of a tower satisfying the
explicit arithmetic hypotheses of `TraceConstruction.TNT.Hyp`, its cyclic-sum
operator is exactly `Algebra.normalizedTrace`, embedded in the algebraic closure.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.CloudB3W11TateTrace

open UniformSpace

section Algebraic

variable (F L : Type*) [Field F] [Field L] [CharZero F] [Algebra F L]
  [Algebra.IsIntegral F L]

/-- Normalized trace is unchanged by an automorphism fixing its target field. -/
theorem traceRetraction_invariant (E : IntermediateField F L) (σ : L ≃ₐ[F] L)
    (hσ : σ ∈ E.fixingSubgroup) (x : L) :
    traceRetraction F L E (σ x) = traceRetraction F L E x := by
  have hf := (IntermediateField.mem_fixingSubgroup_iff E σ).mp hσ
  rw [traceRetraction_equivariant F L E σ (AlgEquiv.refl : E ≃ₐ[F] E)
    (fun y => (hf y y.property).symm)]
  exact hf _ (traceRetraction_mem F L E x)

end Algebraic

open TraceConstruction.TNT

variable (p : ℕ) [Fact p.Prime]

/-- Applying normalized trace to the normalized cyclic orbit sum cancels its
normalization factor. No trace bound or ramification estimate is used here. -/
theorem traceRetraction_Top (E : IntermediateField ℚ_[p] (PadicAlgCl p))
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) (hσ : σ ∈ E.fixingSubgroup)
    (k : ℕ) (y : PadicAlgCl p) :
    traceRetraction ℚ_[p] (PadicAlgCl p) E (Top p σ k y) =
      traceRetraction ℚ_[p] (PadicAlgCl p) E y := by
  have hp : (p : PadicAlgCl p) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hcast : ((p : PadicAlgCl p) ^ k)⁻¹ =
      algebraMap ℚ_[p] (PadicAlgCl p) (((p : ℚ_[p]) ^ k)⁻¹) := by
    simp only [map_inv₀, map_pow, map_natCast]
  unfold TraceConstruction.TNT.Top TraceConstruction.TNT.Ssum
  rw [hcast, ← Algebra.smul_def, map_smul, map_sum]
  have hinv : ∀ i ∈ Finset.range (p ^ k),
      traceRetraction ℚ_[p] (PadicAlgCl p) E ((σ ^ i) y) =
        traceRetraction ℚ_[p] (PadicAlgCl p) E y := by
    intro i _
    exact traceRetraction_invariant ℚ_[p] (PadicAlgCl p) E (σ ^ i)
      (E.fixingSubgroup.pow_mem hσ i) y
  rw [Finset.sum_congr rfl hinv, Finset.sum_const, Finset.card_range, Algebra.smul_def,
    nsmul_eq_mul, map_inv₀, map_pow, map_natCast, Nat.cast_pow]
  exact inv_mul_cancel_left₀ (pow_ne_zero k hp) _

/-- On algebraic tower points the constructed Tate operator agrees with genuine
normalized trace to the finite level. -/
theorem constructedTrace_eq_normalizedTrace
    {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {c : ℕ → ℝ} {C : ℝ}
    (H : Hyp p Km c C) (m : ℕ) {n : ℕ} (y : PadicAlgCl p) (hy : y ∈ Km n) :
    tΩ p H m y = traceRetraction ℚ_[p] (PadicAlgCl p) (Km m) y := by
  have hy' : y ∈ Km (m + n) := mem_add_of_mem p H m hy
  have hTopMem : Top p (gen p H m) n y ∈ Km m :=
    Top_mem p H.cyc H.mono H.fin H.deg H.stab m (gen p H m) (gen_spec p H m) n y hy'
  calc
    tΩ p H m y = Top p (gen p H m) n y := tΩ_eq p H m n y hy'
    _ = traceRetraction ℚ_[p] (PadicAlgCl p) (Km m) (Top p (gen p H m) n y) :=
      (traceRetraction_of_mem ℚ_[p] (PadicAlgCl p) (Km m) hTopMem).symm
    _ = traceRetraction ℚ_[p] (PadicAlgCl p) (Km m) y :=
      traceRetraction_Top p (Km m) (gen p H m) (gen_spec p H m).1 n y

/-- The constructed uniform estimate therefore bounds the GENUINE normalized
trace retractions, uniformly in BOTH the source and target levels. -/
theorem norm_normalizedTrace_le_of_arithmetic_hyp
    {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {c : ℕ → ℝ} {C : ℝ}
    (H : Hyp p Km c C) (m : ℕ) {n : ℕ} (y : PadicAlgCl p) (hy : y ∈ Km n) :
    ‖traceRetraction ℚ_[p] (PadicAlgCl p) (Km m) y‖ ≤ max 1 (dconst p C) * ‖y‖ := by
  rw [← constructedTrace_eq_normalizedTrace p H m y hy]
  exact norm_tΩ_le p H m y hy

/-- The arithmetic hypotheses provide an actual uniform bound on genuine
normalized trace over the entire algebraic tower, not merely on each finite
level separately. -/
theorem exists_uniform_normalizedTrace_bound_of_arithmetic_hyp
    {Km : ℕ → IntermediateField ℚ_[p] (PadicAlgCl p)} {c : ℕ → ℝ} {C : ℝ}
    (H : Hyp p Km c C) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ (m : ℕ) (y : PadicAlgCl p),
      y ∈ (⨆ n, Km n) →
        ‖traceRetraction ℚ_[p] (PadicAlgCl p) (Km m) y‖ ≤ B * ‖y‖ := by
  refine ⟨max 1 (dconst p C), le_max_left _ _, fun m y hy => ?_⟩
  change y ∈ (↑(⨆ n, Km n) : Set (PadicAlgCl p)) at hy
  rw [IntermediateField.coe_iSup_of_directed H.mono.directed_le] at hy
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hy
  exact norm_normalizedTrace_le_of_arithmetic_hyp p H m y hn

end ZInQ.Contrib.CloudB3W11TateTrace
