import Mathlib

/-!
# bp-analytic: compact complex tori `E ⧸ Λ` as complex Lie groups

First concrete layer of the analytic-uniformization blueprint (docs/research/bp-analytic.md).
Mathlib only.

* `Torus Λ := E ⧸ Λ` for a full lattice `Λ` (`DiscreteTopology Λ`, `IsZLattice ℝ Λ`) in a
  finite-dimensional complex normed space `E`.
* `QuotientAddGroup.mk : E → Torus Λ` is a covering map, hence a local homeomorphism; its local
  inverses are the charts.
* Every transition map is locally a translation by a lattice vector, so `Torus Λ` is a complex
  analytic manifold (`IsManifold 𝓘(ℂ, E) ω`), compact, connected.
-/

open scoped Manifold ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace BPAnalytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

section Discrete

variable (Λ : Submodule ℤ E) [DiscreteTopology Λ]

/-- A discrete subgroup has a uniform gap around `0`. -/
theorem exists_gap : ∃ ε > 0, ∀ v ∈ Λ, ‖v‖ < ε → v = 0 := by
  have h : IsOpen ({0} : Set Λ) := isOpen_discrete _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_singleton_iff.mp h
  refine ⟨ε, hε, fun v hv hlt => ?_⟩
  have := hball ⟨v, hv⟩ (by simpa [Subtype.dist_eq] using hlt)
  simpa using congrArg Subtype.val this

/-- **Local constancy.** A continuous map that differs from the identity by lattice vectors is,
near every point, a translation. -/
theorem eventuallyEq_add_const {U : Set E} (hU : IsOpen U) {F : E → E} (hF : ContinuousOn F U)
    (hΛ : ∀ z ∈ U, F z - z ∈ Λ) {x : E} (hx : x ∈ U) :
    F =ᶠ[𝓝 x] fun z => z + (F x - x) := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap Λ
  have hc : ContinuousAt (fun z => F z - z) x :=
    ((hF.continuousAt (hU.mem_nhds hx)).sub continuousAt_id)
  have h1 : ∀ᶠ z in 𝓝 x, dist (F z - z) (F x - x) < ε :=
    hc.eventually (Metric.ball_mem_nhds _ hε)
  filter_upwards [h1, hU.mem_nhds hx] with z hz hzU
  have hmem : (F z - z) - (F x - x) ∈ Λ := Λ.sub_mem (hΛ z hzU) (hΛ x hx)
  have h0 := hgap _ hmem (by simpa [dist_eq_norm] using hz)
  have : F z - z = F x - x := sub_eq_zero.mp h0
  linear_combination (norm := abel_nf) this

/-- Such a map is analytic (indeed `C^n` for every `n`) on `U`. -/
theorem contDiffOn_of_sub_mem {n : WithTop ℕ∞} {U : Set E} (hU : IsOpen U) {F : E → E}
    (hF : ContinuousOn F U) (hΛ : ∀ z ∈ U, F z - z ∈ Λ) : ContDiffOn ℂ n F U := fun _ hx =>
  ((contDiff_id.add contDiff_const).contDiffAt.congr_of_eventuallyEq
    (eventuallyEq_add_const Λ hU hF hΛ hx)).contDiffWithinAt

end Discrete

variable (Λ : Submodule ℤ E) [DiscreteTopology Λ]

/-- The complex torus `E ⧸ Λ`. -/
abbrev Torus := E ⧸ Λ.toAddSubgroup

/-- The projection `E → E ⧸ Λ` (for the torus, this is the exponential map). -/
abbrev proj : E → Torus Λ := QuotientAddGroup.mk

theorem proj_eq_iff {x y : E} : proj Λ x = proj Λ y ↔ x - y ∈ Λ := by
  rw [QuotientAddGroup.eq_iff_sub_mem]
  simp

theorem isAddQuotientCoveringMap_proj :
    IsAddQuotientCoveringMap (proj Λ) Λ.toAddSubgroup :=
  AddSubgroup.isAddQuotientCoveringMap_of_comm _
    (isDiscrete_iff_discreteTopology.mpr (by assumption))

theorem isCoveringMap_proj : IsCoveringMap (proj Λ) :=
  (isAddQuotientCoveringMap_proj Λ).isCoveringMap

theorem isLocalHomeomorph_proj : IsLocalHomeomorph (proj Λ) :=
  (isAddQuotientCoveringMap_proj Λ).isLocalHomeomorph

/-- The chart at a point `x : E`: the local inverse of `proj` through `x`. -/
def chartOf (x : E) : OpenPartialHomeomorph (Torus Λ) E :=
  (isLocalHomeomorph_proj Λ).localInverseAt x

theorem chartOf_symm_apply (x z : E) : (chartOf Λ x).symm z = proj Λ z := by
  rw [chartOf, (isLocalHomeomorph_proj Λ).localInverseAt_symm]

theorem proj_chartOf {x : E} {q : Torus Λ} (hq : q ∈ (chartOf Λ x).source) :
    proj Λ (chartOf Λ x q) = q :=
  (isLocalHomeomorph_proj Λ).apply_localInverseAt_of_mem hq

theorem self_mem_chartOf_target (x : E) : x ∈ (chartOf Λ x).target :=
  (isLocalHomeomorph_proj Λ).self_mem_localInverseAt_target

theorem proj_mem_chartOf_source (x : E) : proj Λ x ∈ (chartOf Λ x).source :=
  (isLocalHomeomorph_proj Λ).apply_self_mem_localInverseAt_source

instance : ChartedSpace E (Torus Λ) where
  atlas := range (chartOf Λ)
  chartAt q := chartOf Λ q.out
  mem_chart_source q := by
    have := proj_mem_chartOf_source Λ q.out
    rwa [proj, QuotientAddGroup.out_eq'] at this
  chart_mem_atlas q := ⟨_, rfl⟩

theorem chartAt_torus (q : Torus Λ) : chartAt E q = chartOf Λ q.out := rfl

/-- Transition maps differ from the identity by lattice vectors. -/
theorem transition_sub_mem (x x' : E) {z : E}
    (hz : z ∈ ((chartOf Λ x).symm ≫ₕ chartOf Λ x').source) :
    ((chartOf Λ x).symm ≫ₕ chartOf Λ x') z - z ∈ Λ := by
  rw [OpenPartialHomeomorph.trans_source] at hz
  have h2 : (chartOf Λ x).symm z ∈ (chartOf Λ x').source := hz.2
  rw [chartOf_symm_apply] at h2
  have := proj_chartOf Λ h2
  rw [OpenPartialHomeomorph.coe_trans, Function.comp_apply, chartOf_symm_apply]
  exact (proj_eq_iff Λ).mp this

/-- **`E ⧸ Λ` is a complex analytic manifold.** -/
instance : IsManifold 𝓘(ℂ, E) ω (Torus Λ) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ]
  exact contDiffOn_of_sub_mem Λ ((chartOf Λ x).symm ≫ₕ chartOf Λ x').open_source
    ((chartOf Λ x).symm ≫ₕ chartOf Λ x').continuousOn (fun z hz => transition_sub_mem Λ x x' hz)

end BPAnalytic
