import ZInQKernel.Contrib.CloudB3W11TateTrace.ContinuousTrace
import ZInQKernel.Contrib.G9.I4Layer

/-!
# Equivariance of the actual continuous Tate trace projections

All actions and cyclotomic scalars in this module are the genuine
`PkgI4.cpAct` and `PkgI4.cycPow` from the target. The uniform trace bound is
still a hypothesis. Algebraic twisted invariant vanishing is supplied as
an explicit input, to be proved by the independent cyclotomic-image author.
-/

noncomputable section

set_option linter.style.haveILetI false

namespace ZInQ.Contrib.CloudB3W11TateTrace

open UniformSpace ZInQ.Contrib.G9.PkgI4

variable (p : ℕ) [Fact p.Prime]

/-- Restrict the honest algebraic Galois action to the stable cyclotomic tower. -/
def towerAction (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (σ : GQp p) (hσ : σ ∈ K.fixingSubgroup) :
    cyclotomicTower p K →ₗᵢ[ℚ_[p]] cyclotomicTower p K where
  toFun x := ⟨σ (x : PadicAlgCl p), cyclotomicTower_stable p K σ hσ x.property⟩
  map_add' x y := Subtype.ext (map_add σ (x : PadicAlgCl p) (y : PadicAlgCl p))
  map_smul' c x := Subtype.ext (map_smul σ.toLinearMap c (x : PadicAlgCl p))
  norm_map' x := norm_gqp_apply p σ (x : PadicAlgCl p)

/-- The honest isometric completion of the restricted algebraic action. -/
def completedTowerAction (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (σ : GQp p) (hσ : σ ∈ K.fixingSubgroup) :
    CompletedTower p K →ₗᵢ[ℚ_[p]] CompletedTower p K := (towerAction p K σ hσ).completion

@[simp]
theorem completedTowerAction_coe (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (σ : GQp p) (hσ : σ ∈ K.fixingSubgroup) (x : cyclotomicTower p K) :
    completedTowerAction p K σ hσ (x : CompletedTower p K) =
      (towerAction p K σ hσ x : CompletedTower p K) :=
  LinearIsometry.completion_apply_coe _ x

/-- The inclusion of the completed tower intertwines its action with the exact
action on `C_p` in the frozen target. -/
theorem completedTowerEmbedding_action (K : IntermediateField ℚ_[p] (PadicAlgCl p))
    (σ : GQp p) (hσ : σ ∈ K.fixingSubgroup) (x : CompletedTower p K) :
    completedTowerEmbedding p K (completedTowerAction p K σ hσ x) =
      cpAct p σ (completedTowerEmbedding p K x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((completedTowerEmbedding p K).continuous.comp (completedTowerAction p K σ hσ).continuous)
      ((continuous_cpAct p σ).comp (completedTowerEmbedding p K).continuous)
  | ih x =>
    rw [completedTowerAction_coe, completedTowerEmbedding_coe, completedTowerEmbedding_coe, cpAct_coe]
    rfl

section Bounded

variable (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
  (C : ℝ) (h : ∀ (n : ℕ) (x : cyclotomicTower p K),
    ‖levelTrace p K n (x : PadicAlgCl p)‖ ≤ C * ‖x‖)

/-- Galois equivariance survives the continuous extension of normalized trace. -/
theorem completedTraceCp_equivariant (n : ℕ) (σ : GQp p) (hσ : σ ∈ K.fixingSubgroup)
    (x : CompletedTower p K) :
    completedTraceCp p K C h n (completedTowerAction p K σ hσ x) =
      cpAct p σ (completedTraceCp p K C h n x) := by
  induction x using Completion.induction_on with
  | hp =>
    exact isClosed_eq
      ((completedTraceCp p K C h n).continuous.comp (completedTowerAction p K σ hσ).continuous)
      ((continuous_cpAct p σ).comp (completedTraceCp p K C h n).continuous)
  | ih x =>
    rw [completedTowerAction_coe, completedTraceCp_coe, completedTraceCp_coe, cpAct_coe]
    change ((levelTrace p K n (σ (x : PadicAlgCl p)) : PadicAlgCl p) : ℂ_[p]) = _
    rw [levelTrace_equivariant p K n σ hσ]

/-- The projected vector inherits twisted invariance from the original completed
vector. No invariant algebraic approximation is used. -/
theorem completedTraceCp_twist_invariant (n : ℕ) (i : ℤ) (x : CompletedTower p K)
    (hx : ∀ σ ∈ K.fixingSubgroup,
      cycPow p σ i • cpAct p σ (completedTowerEmbedding p K x) = completedTowerEmbedding p K x) :
    ∀ σ ∈ K.fixingSubgroup,
      cycPow p σ i • cpAct p σ (completedTraceCp p K C h n x) = completedTraceCp p K C h n x := by
  intro σ hσ
  have hxs : cycPow p σ i • completedTowerAction p K σ hσ x = x := by
    apply (completedTowerEmbedding p K).injective
    rw [map_smul, completedTowerEmbedding_action]
    exact hx σ hσ
  have ht := congrArg (completedTraceCp p K C h n) hxs
  rw [map_smul, completedTraceCp_equivariant] at ht
  exact ht

/-- Each projection is an actual algebraic twisted invariant, obtained by
projecting the completed vector itself. -/
theorem completedTrace_algebraic_twist_invariant (n : ℕ) (i : ℤ) (x : CompletedTower p K)
    (hx : ∀ σ ∈ K.fixingSubgroup,
      cycPow p σ i • cpAct p σ (completedTowerEmbedding p K x) = completedTowerEmbedding p K x) :
    ∀ σ ∈ K.fixingSubgroup,
      cycPow p σ i • σ (completedTrace p K C h n x : PadicAlgCl p) =
        (completedTrace p K C h n x : PadicAlgCl p) := by
  intro σ hσ
  apply Completion.coe_injective (PadicAlgCl p)
  rw [Completion.coe_smul]
  have ht := completedTraceCp_twist_invariant p K C h n i x hx σ hσ
  change cycPow p σ i • cpAct p σ
      (((completedTrace p K C h n x : cyclotomicLevel p K n) : PadicAlgCl p) : ℂ_[p]) =
    (((completedTrace p K C h n x : cyclotomicLevel p K n) : PadicAlgCl p) : ℂ_[p]) at ht
  rw [cpAct_coe] at ht
  exact ht

end Bounded

/-- Completed-tower nonzero-twist vanishing from the uniform trace estimate and
the separately supplied algebraic theorem. This is a proved conditional
assembly, not a closure of the Tate leaf. -/
theorem completedTower_twist_eq_zero
    (K : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] K]
    (hbound : UniformNormalizedTraceBound p K) (i : ℤ)
    (halg : ∀ y : PadicAlgCl p,
      (∀ σ ∈ K.fixingSubgroup, cycPow p σ i • σ y = y) → y = 0)
    (x : CompletedTower p K)
    (hx : ∀ σ ∈ K.fixingSubgroup,
      cycPow p σ i • cpAct p σ (completedTowerEmbedding p K x) = completedTowerEmbedding p K x) :
    completedTowerEmbedding p K x = 0 := by
  obtain ⟨C, hC, h⟩ := hbound
  apply eq_zero_of_completedTraceCp_eq_zero p K C h hC x
  intro n
  have hz := halg (completedTrace p K C h n x : PadicAlgCl p)
    (completedTrace_algebraic_twist_invariant p K C h n i x hx)
  change (((completedTrace p K C h n x : cyclotomicLevel p K n) : PadicAlgCl p) : ℂ_[p]) = 0
  rw [hz, Completion.coe_zero]

end ZInQ.Contrib.CloudB3W11TateTrace
