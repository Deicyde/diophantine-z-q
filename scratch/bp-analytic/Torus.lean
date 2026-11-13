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
instance isManifold_torus : IsManifold 𝓘(ℂ, E) ω (Torus Λ) := by
  apply isManifold_of_contDiffOn
  rintro e e' ⟨x, rfl⟩ ⟨x', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.id_comp,
    Function.comp_id, preimage_id_eq, id_eq, range_id, inter_univ]
  exact contDiffOn_of_sub_mem Λ ((chartOf Λ x).symm ≫ₕ chartOf Λ x').open_source
    ((chartOf Λ x).symm ≫ₕ chartOf Λ x').continuousOn (fun z hz => transition_sub_mem Λ x x' hz)


/-! ## §2. Smoothness of the projection; descent of smooth maps; the Lie group structure -/

/-- The projection `E → E ⧸ Λ` is analytic. -/
theorem contMDiff_proj {n : ℕ∞ω} : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) n (proj Λ) := by
  intro x
  rw [contMDiffAt_iff_target, extChartAt_coe, modelWithCornersSelf_coe, Function.id_comp,
    contMDiffAt_iff_contDiffAt]
  refine ⟨(isLocalHomeomorph_proj Λ).continuous.continuousAt, ?_⟩
  set c := chartAt E (proj Λ x)
  have hU : IsOpen (proj Λ ⁻¹' c.source) :=
    c.open_source.preimage (isLocalHomeomorph_proj Λ).continuous
  have hx : x ∈ proj Λ ⁻¹' c.source := mem_chart_source E (proj Λ x)
  have hcont : ContinuousOn (c ∘ proj Λ) (proj Λ ⁻¹' c.source) :=
    c.continuousOn.comp (isLocalHomeomorph_proj Λ).continuous.continuousOn (fun _ hz => hz)
  have hsub : ∀ z ∈ proj Λ ⁻¹' c.source, (c ∘ proj Λ) z - z ∈ Λ := by
    intro z hz
    have := proj_chartOf Λ (x := (proj Λ x).out) hz
    exact (proj_eq_iff Λ).mp this
  exact (contDiffOn_of_sub_mem Λ hU hcont hsub).contDiffAt (hU.mem_nhds hx)

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℂ F H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

/-- **Descent.** A map out of `E ⧸ Λ` is `C^n` (analytic for `n = ω`) as soon as its composite
with the projection is. -/
theorem contMDiff_of_comp_proj {n : ℕ∞ω} {f : Torus Λ → M}
    (hf : ContMDiff 𝓘(ℂ, E) I' n (f ∘ proj Λ)) : ContMDiff 𝓘(ℂ, E) I' n f := by
  intro q
  set c := chartAt E q
  have hq : q ∈ c.source := mem_chart_source E q
  have hc : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) n c q :=
    (contMDiffOn_chart).contMDiffAt (c.open_source.mem_nhds hq)
  have heq : f =ᶠ[𝓝 q] (f ∘ proj Λ) ∘ c := by
    filter_upwards [c.open_source.mem_nhds hq] with y hy
    simp only [Function.comp_apply]
    exact congrArg f (proj_chartOf Λ (x := q.out) hy).symm
  exact ((hf (c q)).comp q hc).congr_of_eventuallyEq heq

/-- Descent for maps of two variables. -/
theorem contMDiff_of_comp_proj₂ {n : ℕ∞ω} {f : Torus Λ × Torus Λ → M}
    (hf : ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ, E)) I' n (f ∘ Prod.map (proj Λ) (proj Λ))) :
    ContMDiff (𝓘(ℂ, E).prod 𝓘(ℂ, E)) I' n f := by
  rintro ⟨q₁, q₂⟩
  set c₁ := chartAt E q₁
  set c₂ := chartAt E q₂
  have h₁ : q₁ ∈ c₁.source := mem_chart_source E q₁
  have h₂ : q₂ ∈ c₂.source := mem_chart_source E q₂
  have hc₁ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) n c₁ q₁ :=
    (contMDiffOn_chart).contMDiffAt (c₁.open_source.mem_nhds h₁)
  have hc₂ : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) n c₂ q₂ :=
    (contMDiffOn_chart).contMDiffAt (c₂.open_source.mem_nhds h₂)
  have hc := hc₁.prodMap hc₂
  have heq : f =ᶠ[𝓝 (q₁, q₂)] (f ∘ Prod.map (proj Λ) (proj Λ)) ∘ Prod.map c₁ c₂ := by
    filter_upwards [prod_mem_nhds (c₁.open_source.mem_nhds h₁) (c₂.open_source.mem_nhds h₂)]
      with y hy
    obtain ⟨y₁, y₂⟩ := y
    simp only [Function.comp_apply, Prod.map_apply]
    rw [show proj Λ (c₁ y₁) = y₁ from proj_chartOf Λ (x := q₁.out) hy.1,
      show proj Λ (c₂ y₂) = y₂ from proj_chartOf Λ (x := q₂.out) hy.2]
  exact ((hf _).comp _ hc).congr_of_eventuallyEq heq

/-- **`E ⧸ Λ` is a complex Lie group** (analytic group law). -/
instance lieAddGroup_torus : LieAddGroup 𝓘(ℂ, E) ω (Torus Λ) where
  contMDiff_add := by
    apply contMDiff_of_comp_proj₂ Λ
    have : (fun p : Torus Λ × Torus Λ => p.1 + p.2) ∘ Prod.map (proj Λ) (proj Λ) =
        proj Λ ∘ (fun p : E × E => p.1 + p.2) := by
      ext ⟨a, b⟩; rfl
    rw [this]
    exact (contMDiff_proj Λ).comp (contMDiff_add 𝓘(ℂ, E) ω)
  contMDiff_neg := by
    apply contMDiff_of_comp_proj Λ
    have : (fun a : Torus Λ => -a) ∘ proj Λ = proj Λ ∘ (fun a : E => -a) := by
      ext a; rfl
    rw [this]
    exact (contMDiff_proj Λ).comp (contMDiff_neg 𝓘(ℂ, E) ω)

/-! ## §3. Compactness, connectedness, the exponential -/

instance connectedSpace_torus : ConnectedSpace (Torus Λ) :=
  QuotientAddGroup.mk_surjective.connectedSpace (isLocalHomeomorph_proj Λ).continuous

/-- **`E ⧸ Λ` is compact** for a full lattice: it is the image of a closed parallelepiped. -/
instance compactSpace_torus [FiniteDimensional ℂ E] [IsZLattice ℝ Λ] : CompactSpace (Torus Λ) := by
  have := ZLattice.module_free ℝ Λ
  have := ZLattice.module_finite ℝ Λ
  let b := (Module.Free.chooseBasis ℤ Λ).ofZLatticeBasis ℝ Λ
  refine ⟨?_⟩
  have himg : proj Λ '' parallelepiped b = univ := by
    refine eq_univ_of_forall fun q => ?_
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine ⟨ZSpan.fract b x, ZSpan.fundamentalDomain_subset_parallelepiped b
      (ZSpan.fract_mem_fundamentalDomain b x), ?_⟩
    rw [proj_eq_iff, ZSpan.fract_apply, sub_sub_cancel_left]
    have hspan := Module.Basis.ofZLatticeBasis_span ℝ Λ (Module.Free.chooseBasis ℤ Λ)
    exact Λ.neg_mem (hspan.le (ZSpan.floor b x).2)
  rw [← himg]
  exact b.parallelepiped.isCompact.image (isLocalHomeomorph_proj Λ).continuous

/-- The Lie algebra of the torus is `E` itself (Mathlib's `AddGroupLieAlgebra`, the tangent space
at `0`, is definitionally the model space). -/
example : AddGroupLieAlgebra 𝓘(ℂ, E) (Torus Λ) = E := rfl

instance : Λ.toAddSubgroup.Normal := AddSubgroup.normal_of_isAddCommutative _

/-- **The exponential map** `Lie(E ⧸ Λ) = E → E ⧸ Λ`: the projection, as a group homomorphism.
(Its source is stated as `E`; `AddGroupLieAlgebra 𝓘(ℂ, E) (Torus Λ)` is `E` by `rfl`, above.) -/
def torusExp : E →+ Torus Λ :=
  QuotientAddGroup.mk' Λ.toAddSubgroup

theorem torusExp_apply (v : E) : torusExp Λ v = proj Λ v := rfl

theorem torusExp_surjective : Function.Surjective (torusExp Λ) :=
  QuotientAddGroup.mk_surjective

/-- **The period lattice is the kernel of the exponential.** -/
theorem ker_torusExp : (torusExp Λ).ker = Λ.toAddSubgroup := by
  ext v
  simp [torusExp]

theorem contMDiff_torusExp : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E) ω (torusExp Λ) := contMDiff_proj Λ

/-- One-parameter subgroups: `t ↦ exp(t • v)` is an analytic homomorphism `ℂ → E ⧸ Λ`. -/
theorem contMDiff_torusExp_smul (v : E) :
    ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, E) ω (fun t : ℂ => torusExp Λ (t • v)) :=
  (contMDiff_proj Λ).comp (contMDiff_iff_contDiff.mpr (contDiff_id.smul contDiff_const))

/-- **Liouville on the torus.** Every holomorphic function on `E ⧸ Λ` is constant. -/
theorem holomorphic_const [FiniteDimensional ℂ E] [IsZLattice ℝ Λ] {f : Torus Λ → F}
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, F) f) : ∃ v : F, f = Function.const _ v :=
  hf.exists_eq_const_of_compactSpace

end BPAnalytic
