import ZInQKernel.Contrib.CloudB3W11TateTrace.Tower
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Continuous Tate trace, conditional only on its actual uniform estimate

Tate, *p-divisible groups* (1967), printed pp. 171-173, Corollary 3 of
Proposition 5, Proposition 6 and its base-change remark, and the continuous
extension on p. 173 were read in the original scan (PDF pp. 14-16).

`UniformNormalizedTraceBound` is the exact cyclotomic estimate still needed
in this development. It is NOT asserted as a theorem or as a new axiom.
All extension, range, and convergence results below are proved from it.
In particular, convergence is not inferred from density of invariant
algebraic points: uniformly bounded projections are applied to the fixed
completed vector itself.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.CloudB3W11TateTrace

open UniformSpace Filter

variable (p : ℕ) [Fact p.Prime]

/-- The honest completion of the actual algebraic cyclotomic tower. -/
abbrev CompletedTower (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :=
  Completion (cyclotomicTower p K)

/-- Inclusion of any intermediate field in the honest `C_p`, as a linear isometry. -/
def fieldInclusion (E : IntermediateField ℚ_[p] (PadicAlgCl p)) : E →ₗᵢ[ℚ_[p]] ℂ_[p] where
  toLinearMap := (Completion.toComplL : PadicAlgCl p →L[ℚ_[p]] ℂ_[p]).toLinearMap.comp
    E.val.toLinearMap
  norm_map' x := PadicComplex.norm_extends p (x : PadicAlgCl p)

@[simp]
theorem fieldInclusion_apply (E : IntermediateField ℚ_[p] (PadicAlgCl p)) (x : E) :
    fieldInclusion p E x = ((x : PadicAlgCl p) : ℂ_[p]) := rfl

/-- Isometric embedding of the completed tower in the honest `C_p`. -/
def completedTowerEmbedding (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    CompletedTower p K →ₗᵢ[ℚ_[p]] ℂ_[p] := (fieldInclusion p (cyclotomicTower p K)).fromCompletion

@[simp]
theorem completedTowerEmbedding_coe (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (x : cyclotomicTower p K) :
    completedTowerEmbedding p K (x : CompletedTower p K) = ((x : PadicAlgCl p) : ℂ_[p]) :=
  LinearIsometry.fromCompletion_apply_coe _ x

/-- The model of the completed tower is precisely the closure of its algebraic points. -/
theorem range_completedTowerEmbedding (K : IntermediateField ℚ_[p] (PadicAlgCl p)) :
    Set.range (completedTowerEmbedding p K) =
      closure (Set.range (fieldInclusion p (cyclotomicTower p K))) := by
  apply Set.Subset.antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using Completion.induction_on with
    | hp =>
      exact isClosed_closure.preimage (completedTowerEmbedding p K).continuous
    | ih x =>
      rw [completedTowerEmbedding_coe]
      exact subset_closure ⟨x, rfl⟩
  · apply closure_minimal
    · rintro _ ⟨x, rfl⟩
      exact ⟨(x : CompletedTower p K), completedTowerEmbedding_coe p K x⟩
    · exact (completedTowerEmbedding p K).isometry.isClosedEmbedding.isClosed_range

/-- The exact missing uniform estimate: one constant for ALL finite-level
normalized trace retractions and ALL algebraic points of `K(μ_{p^∞})`.
This is a cyclotomic consequence of Tate's ramification estimates, not a
statement claimed to have been proved in this module. -/
def UniformNormalizedTraceBound (K : IntermediateField ℚ_[p] (PadicAlgCl p)) : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ ∀ (n : ℕ) (x : cyclotomicTower p K),
    ‖levelTrace p K n (x : PadicAlgCl p)‖ ≤ C * ‖x‖

/-- The global ramification/normalized-trace theorem still missing from the kernel proof.
A closing theorem for this precise proposition is required to remove the
hypothesis of the continuous Tate trace assembly. -/
def CyclotomicNormalizedTraceBound : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    [FiniteDimensional ℚ_[p] K], UniformNormalizedTraceBound p K

/-- Algebraic trace into its finite-level target, not merely into `C_p`. -/
def towerTraceToLevel (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (n : ℕ) :
    cyclotomicTower p K →ₗ[ℚ_[p]] cyclotomicLevel p K n where
  toFun x := ⟨levelTrace p K n (x : PadicAlgCl p), levelTrace_mem p K n x⟩
  map_add' x y := Subtype.ext (map_add (levelTrace p K n) (x : PadicAlgCl p) (y : PadicAlgCl p))
  map_smul' c x := Subtype.ext (map_smul (levelTrace p K n) c (x : PadicAlgCl p))

section Bounded

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
  (C : ℝ) (h : ∀ (n : ℕ) (x : cyclotomicTower p K),
    ‖levelTrace p K n (x : PadicAlgCl p)‖ ≤ C * ‖x‖)

/-- Extension of genuine normalized trace to the tower completion, with values
still in the COMPLETE finite field `K(μ_{p^n})`. -/
def completedTrace (n : ℕ) : CompletedTower p K →L[ℚ_[p]] cyclotomicLevel p K n :=
  letI : CompleteSpace (cyclotomicLevel p K n) := FiniteDimensional.complete ℚ_[p] _
  ((towerTraceToLevel p K n).mkContinuous C (h n)).fromCompletion

@[simp]
theorem completedTrace_coe (n : ℕ) (x : cyclotomicTower p K) :
    completedTrace p K C h n (x : CompletedTower p K) = towerTraceToLevel p K n x := by
  simp only [completedTrace, ContinuousLinearMap.fromCompletion_apply_coe]
  rfl

/-- The completed finite-level projection viewed in `C_p`. -/
def completedTraceCp (n : ℕ) : CompletedTower p K →L[ℚ_[p]] ℂ_[p] :=
  (fieldInclusion p (cyclotomicLevel p K n)).toContinuousLinearMap.comp (completedTrace p K C h n)

@[simp]
theorem completedTraceCp_coe (n : ℕ) (x : cyclotomicTower p K) :
    completedTraceCp p K C h n (x : CompletedTower p K) =
      ((levelTrace p K n (x : PadicAlgCl p)) : ℂ_[p]) := by
  simp only [completedTraceCp, ContinuousLinearMap.comp_apply, completedTrace_coe]
  rfl

/-- The same norm bound survives completion, with the SAME constant. -/
theorem norm_completedTraceCp_le (n : ℕ) (x : CompletedTower p K) :
    ‖completedTraceCp p K C h n x‖ ≤ C * ‖x‖ := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_le
      (continuous_norm.comp (completedTraceCp p K C h n).continuous)
      (continuous_norm.const_mul C)
  | ih x =>
    rw [completedTraceCp_coe, PadicComplex.norm_extends, Completion.norm_coe]
    exact h n x

/-- Uniformly bounded compatible finite-level projections converge pointwise to
identity on the completed tower.  The proof approximates a vector and applies
the actual bounded operators to its error. -/
theorem completedTraceCp_tendsto (hC : 1 ≤ C) (x : CompletedTower p K) :
    Tendsto (fun n : ℕ => completedTraceCp p K C h n x) atTop
      (nhds (completedTowerEmbedding p K x)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hCpos : 0 < C + 1 := by linarith
  obtain ⟨a, ha⟩ := Completion.denseRange_coe.exists_dist_lt x (div_pos hε hCpos)
  obtain ⟨N, hN⟩ := levelTrace_eventually_eq p K a.property
  refine ⟨N, fun n hn => ?_⟩
  have heq : completedTraceCp p K C h n (a : CompletedTower p K) =
      completedTowerEmbedding p K (a : CompletedTower p K) := by
    rw [completedTraceCp_coe, completedTowerEmbedding_coe, hN n hn]
  have hε' : (C + 1) * dist x (a : CompletedTower p K) < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ hCpos).mp ha
  calc
    dist (completedTraceCp p K C h n x) (completedTowerEmbedding p K x) =
        ‖completedTraceCp p K C h n (x - (a : CompletedTower p K)) -
          completedTowerEmbedding p K (x - (a : CompletedTower p K))‖ := by
      rw [dist_eq_norm, map_sub, map_sub, heq]
      congr 1
      abel
    _ ≤ ‖completedTraceCp p K C h n (x - (a : CompletedTower p K))‖ +
        ‖completedTowerEmbedding p K (x - (a : CompletedTower p K))‖ := norm_sub_le _ _
    _ ≤ C * ‖x - (a : CompletedTower p K)‖ + ‖x - (a : CompletedTower p K)‖ := by
      rw [(completedTowerEmbedding p K).norm_map]
      exact add_le_add (norm_completedTraceCp_le p K C h n _) le_rfl
    _ = (C + 1) * dist x (a : CompletedTower p K) := by rw [dist_eq_norm]; ring
    _ < ε := hε'

/-- A vector annihilated by every completed trace is zero. This uses the proved
projection limit, not any claim about dense invariant algebraic vectors. -/
theorem eq_zero_of_completedTraceCp_eq_zero (hC : 1 ≤ C) (x : CompletedTower p K)
    (hx : ∀ n : ℕ, completedTraceCp p K C h n x = 0) :
    completedTowerEmbedding p K x = 0 := by
  have he : (fun n : ℕ => completedTraceCp p K C h n x) = fun _ => (0 : ℂ_[p]) := funext hx
  have ht := completedTraceCp_tendsto p K C h hC x
  rw [he] at ht
  exact tendsto_nhds_unique ht tendsto_const_nhds

end Bounded

end ZInQ.Contrib.CloudB3W11TateTrace
