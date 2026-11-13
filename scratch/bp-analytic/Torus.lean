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


/-! ## §4. The period lattice `Ωℤ^g + ℤ^g` of a point of the Siegel space

For `Ω` with `det (Im Ω) ≠ 0` (in particular `Ω ∈ 𝔥_g`), the `2g` vectors "columns of `Ω`" and
"standard basis" form an `ℝ`-basis of `ℂ^g`; their `ℤ`-span is a full lattice, and
`ℂ^g ⧸ (Ωℤ^g + ℤ^g)` is a compact connected complex Lie group by §1-§3. -/

section Siegel

open Matrix

variable {g : ℕ}

/-- The Siegel upper half-space of degree `g` (pkg-I1's `SiegelH2` is the case `g = 2`). -/
def SiegelSpace (g : ℕ) : Set (Matrix (Fin g) (Fin g) ℂ) :=
  {Ω | Ωᵀ = Ω ∧ (Ω.map Complex.im).PosDef}

/-- The `2g` period vectors: the columns of `Ω`, then the standard basis vectors. -/
def periodVec (Ω : Matrix (Fin g) (Fin g) ℂ) : Fin g ⊕ Fin g → (Fin g → ℂ)
  | Sum.inl j => fun i => Ω i j
  | Sum.inr j => Pi.single j 1

theorem periodVec_linearIndependent (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : (Ω.map Complex.im).det ≠ 0) : LinearIndependent ℝ (periodVec Ω) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hcoord : ∀ i, (∑ j, (c (Sum.inl j) : ℂ) * Ω i j) + (c (Sum.inr i) : ℂ) = 0 := by
    intro i
    have := congrFun hc i
    simp only [Fintype.sum_sum_type, Finset.sum_apply, Pi.smul_apply,
      periodVec, Pi.zero_apply] at this
    rw [← this]
    congr 1
    simp [Pi.single_apply, Complex.real_smul]
  -- imaginary parts: `(Im Ω) a = 0`
  have ha : (Ω.map Complex.im) *ᵥ (fun j => c (Sum.inl j)) = 0 := by
    funext i
    have := congrArg Complex.im (hcoord i)
    simp only [Complex.add_im, Complex.ofReal_im, add_zero, Complex.zero_im] at this
    rw [Complex.im_sum] at this
    simp only [Complex.im_ofReal_mul] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have ha0 := Matrix.eq_zero_of_mulVec_eq_zero hΩ ha
  have hb : ∀ i, c (Sum.inr i) = 0 := by
    intro i
    have := hcoord i
    have hz : ∀ j, (c (Sum.inl j) : ℂ) = 0 := fun j => by
      simpa using congrFun ha0 j
    simp only [hz, zero_mul, Finset.sum_const_zero, zero_add, Complex.ofReal_eq_zero] at this
    exact this
  rintro (j | j)
  · simpa using congrFun ha0 j
  · exact hb j

theorem card_periodIndex : Fintype.card (Fin g ⊕ Fin g) = Module.finrank ℝ (Fin g → ℂ) := by
  rw [Module.finrank_pi_fintype, Fintype.card_sum, Fintype.card_fin]
  simp [Complex.finrank_real_complex]
  ring

/-- The real basis of `ℂ^g` given by the period vectors. -/
def periodBasis (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :
    Module.Basis (Fin g ⊕ Fin g) ℝ (Fin g → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (periodVec_linearIndependent Ω hΩ) card_periodIndex

theorem coe_periodBasis (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :
    ⇑(periodBasis Ω hΩ) = periodVec Ω := by
  simp [periodBasis]

/-- **The period lattice `Λ_Ω = Ωℤ^g + ℤ^g`.** -/
def periodLattice (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :
    Submodule ℤ (Fin g → ℂ) :=
  Submodule.span ℤ (Set.range (periodBasis Ω hΩ))

instance (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :
    DiscreteTopology (periodLattice Ω hΩ) := by
  unfold periodLattice; infer_instance

instance (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :
    IsZLattice ℝ (periodLattice Ω hΩ) := by
  unfold periodLattice; infer_instance

theorem det_im_ne_zero_of_mem_siegelSpace {Ω : Matrix (Fin g) (Fin g) ℂ} (h : Ω ∈ SiegelSpace g) :
    (Ω.map Complex.im).det ≠ 0 :=
  h.2.det_pos.ne'

/-- Membership: `v ∈ Λ_Ω ↔ v = Ω m + n` with `m n ∈ ℤ^g`. -/
theorem mem_periodLattice_iff (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0)
    (v : Fin g → ℂ) :
    v ∈ periodLattice Ω hΩ ↔
      ∃ m n : Fin g → ℤ, v = Ω *ᵥ (fun j => (m j : ℂ)) + (fun j => (n j : ℂ)) := by
  rw [periodLattice, coe_periodBasis, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => c (Sum.inl j), fun j => c (Sum.inr j), ?_⟩
    funext i
    simp [Fintype.sum_sum_type, periodVec, Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_comm]
  · rintro ⟨m, n, rfl⟩
    refine ⟨Sum.elim m n, ?_⟩
    funext i
    simp [Fintype.sum_sum_type, periodVec, Matrix.mulVec, dotProduct, Pi.single_apply,
      mul_comm]

/-- The abelian variety (complex torus) attached to a point `Ω` of the Siegel space. -/
abbrev SiegelTorus (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :=
  Torus (periodLattice Ω hΩ)

example (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :
    LieAddGroup 𝓘(ℂ, Fin g → ℂ) ω (SiegelTorus Ω hΩ) := inferInstance

example (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : (Ω.map Complex.im).det ≠ 0) :
    CompactSpace (SiegelTorus Ω hΩ) := inferInstance

end Siegel


/-! ## §5. Riemann's theta function on `ℂ^g ⧸ Λ_Ω`

`θ(z, Ω) = Σ_{n ∈ ℤ^g} exp(πi nᵀΩn + 2πi nᵀz)`. Quasi-periodicity under `Λ_Ω` (which says that `θ`
is a section of a line bundle on the torus `ℂ^g ⧸ Λ_Ω`), and the identification of pkg-I1's
theta constants with values of `θ` at the 2-torsion points `(Ωa + b)/2`. All identities are
proved for `tsum` by reindexing, so they hold with no convergence hypothesis. -/

section Theta

open Matrix Complex

variable {g : ℕ}

/-- `ℤ^g ⊂ ℂ^g`. -/
def intVec (n : Fin g → ℤ) : Fin g → ℂ := fun j => (n j : ℂ)

theorem intVec_sub (k m : Fin g → ℤ) : intVec (k - m) = intVec k - intVec m := by
  funext j; simp [intVec]

theorem intVec_dotProduct (n m : Fin g → ℤ) :
    intVec n ⬝ᵥ intVec m = ((n ⬝ᵥ m : ℤ) : ℂ) := by
  simp [intVec, dotProduct]

/-- Riemann's theta function. -/
def riemannTheta (Ω : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : ℂ :=
  ∑' n : Fin g → ℤ,
    exp (Real.pi * I * (intVec n ⬝ᵥ (Ω *ᵥ intVec n)) + 2 * Real.pi * I * (intVec n ⬝ᵥ z))

theorem dotProduct_mulVec_symm {Ω : Matrix (Fin g) (Fin g) ℂ} (hΩ : Ωᵀ = Ω) (a b : Fin g → ℂ) :
    b ⬝ᵥ (Ω *ᵥ a) = a ⬝ᵥ (Ω *ᵥ b) := by
  rw [dotProduct_mulVec, ← mulVec_transpose, hΩ, dotProduct_comm]

/-- Periodicity under `ℤ^g`. -/
theorem riemannTheta_add_int (Ω : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) (m : Fin g → ℤ) :
    riemannTheta Ω (z + intVec m) = riemannTheta Ω z := by
  unfold riemannTheta
  congr 1
  funext n
  rw [dotProduct_add, intVec_dotProduct, mul_add, ← add_assoc, exp_add]
  have : exp (2 * Real.pi * I * ((n ⬝ᵥ m : ℤ) : ℂ)) = 1 := by
    rw [show 2 * Real.pi * I * ((n ⬝ᵥ m : ℤ) : ℂ) = ((n ⬝ᵥ m : ℤ) : ℂ) * (2 * Real.pi * I) by ring]
    exact exp_int_mul_two_pi_mul_I _
  rw [this, mul_one]

/-- **Quasi-periodicity under `Ωℤ^g`**: `θ(z + Ωm) = exp(-πi mᵀΩm - 2πi mᵀz) θ(z)`. -/
theorem riemannTheta_add_mulVec (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ωᵀ = Ω)
    (z : Fin g → ℂ) (m : Fin g → ℤ) :
    riemannTheta Ω (z + Ω *ᵥ intVec m) =
      exp (-(Real.pi * I * (intVec m ⬝ᵥ (Ω *ᵥ intVec m))) - 2 * Real.pi * I * (intVec m ⬝ᵥ z)) *
        riemannTheta Ω z := by
  unfold riemannTheta
  rw [← (Equiv.subRight m).tsum_eq, ← tsum_mul_left]
  congr 1
  funext k
  simp only [Equiv.subRight_apply, intVec_sub]
  rw [← exp_add]
  congr 1
  set a := intVec k
  set b := intVec m
  have hs := dotProduct_mulVec_symm hΩ a b
  simp only [mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_add]
  rw [hs]
  ring

/-- Quasi-periodicity under the whole period lattice `Λ_Ω`. -/
theorem riemannTheta_add_period (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ωᵀ = Ω)
    (z : Fin g → ℂ) (m n : Fin g → ℤ) :
    riemannTheta Ω (z + (Ω *ᵥ intVec m + intVec n)) =
      exp (-(Real.pi * I * (intVec m ⬝ᵥ (Ω *ᵥ intVec m))) - 2 * Real.pi * I * (intVec m ⬝ᵥ z)) *
        riemannTheta Ω z := by
  rw [← add_assoc, riemannTheta_add_int, riemannTheta_add_mulVec Ω hΩ]

/-- Theta function with characteristic `(c, d) ∈ ℂ^g × ℂ^g`, at `z = 0`:
`θ[c, d](Ω) = Σ_n exp(πi (n+c)ᵀΩ(n+c) + 2πi (n+c)ᵀd)`. -/
def thetaChar (c d : Fin g → ℂ) (Ω : Matrix (Fin g) (Fin g) ℂ) : ℂ :=
  ∑' n : Fin g → ℤ,
    exp (Real.pi * I * ((intVec n + c) ⬝ᵥ (Ω *ᵥ (intVec n + c))) + 2 * Real.pi * I * ((intVec n + c) ⬝ᵥ d))

/-- **Theta constants are values of `θ` at torsion points**:
`θ[c, d](Ω) = exp(πi cᵀΩc + 2πi cᵀd) · θ(Ωc + d, Ω)`. -/
theorem thetaChar_eq (c d : Fin g → ℂ) (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ωᵀ = Ω) :
    thetaChar c d Ω =
      exp (Real.pi * I * (c ⬝ᵥ (Ω *ᵥ c)) + 2 * Real.pi * I * (c ⬝ᵥ d)) * riemannTheta Ω (Ω *ᵥ c + d) := by
  unfold thetaChar riemannTheta
  rw [← tsum_mul_left]
  congr 1
  funext n
  rw [← exp_add]
  congr 1
  set a := intVec n
  have hs := dotProduct_mulVec_symm hΩ a c
  simp only [mulVec_add, add_dotProduct, dotProduct_add]
  rw [hs]
  ring

/-- pkg-I1's theta constant (copied verbatim from `scratch/pkg-I1/I1.lean`, §3). -/
abbrev Char2 := (Fin 2 → Fin 2) × (Fin 2 → Fin 2)

/-- pkg-I1's theta constant (copied verbatim from `scratch/pkg-I1/I1.lean`, §3). -/
def thetaConst (m : Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  ∑' n : Fin 2 → ℤ,
    let v : Fin 2 → ℂ := fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2
    Complex.exp (Real.pi * I * (v ⬝ᵥ (Ω *ᵥ v)) + Real.pi * I * (v ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)))

/-- The half-integral vectors `a/2`, `b/2` of a characteristic. -/
def charHalf (a : Fin 2 → Fin 2) : Fin 2 → ℂ := fun k => ((a k : ℕ) : ℂ) / 2

/-- pkg-I1's `thetaConst m` is `θ[a/2, b/2]`. -/
theorem thetaConst_eq_thetaChar (m : Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    thetaConst m Ω = thetaChar (charHalf m.1) (charHalf m.2) Ω := by
  unfold thetaConst thetaChar
  congr 1
  funext n
  have hv : (fun k => (n k : ℂ) + ((m.1 k : ℕ) : ℂ) / 2) = intVec n + charHalf m.1 := by
    funext k; simp [intVec, charHalf]
  simp only [hv]
  congr 1
  have : ((intVec n + charHalf m.1) ⬝ᵥ fun k => ((m.2 k : ℕ) : ℂ)) =
      2 * ((intVec n + charHalf m.1) ⬝ᵥ charHalf m.2) := by
    simp only [dotProduct, charHalf, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [this]
  ring

/-- **F1's theta constants are values of Riemann's theta function at the 2-torsion points**
`(Ωa + b)/2` of the torus `ℂ² ⧸ Λ_Ω`. -/
theorem thetaConst_eq_riemannTheta (m : Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ) (hΩ : Ωᵀ = Ω) :
    thetaConst m Ω =
      exp (Real.pi * I * (charHalf m.1 ⬝ᵥ (Ω *ᵥ charHalf m.1)) +
          2 * Real.pi * I * (charHalf m.1 ⬝ᵥ charHalf m.2)) *
        riemannTheta Ω (Ω *ᵥ charHalf m.1 + charHalf m.2) := by
  rw [thetaConst_eq_thetaChar, thetaChar_eq _ _ _ hΩ]

/-- The point `Ω(a/2) + b/2` is 2-torsion on `ℂ² ⧸ Λ_Ω`. -/
theorem two_nsmul_proj_charPoint (m : Char2) (Ω : Matrix (Fin 2) (Fin 2) ℂ)
    (hΩ : (Ω.map Complex.im).det ≠ 0) :
    (2 : ℕ) • proj (periodLattice Ω hΩ) (Ω *ᵥ charHalf m.1 + charHalf m.2) = 0 := by
  rw [proj, ← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff]
  show _ ∈ periodLattice Ω hΩ
  rw [mem_periodLattice_iff]
  refine ⟨fun k => ((m.1 k : ℕ) : ℤ), fun k => ((m.2 k : ℕ) : ℤ), ?_⟩
  have h2 : ∀ a : Fin 2 → Fin 2, (2 : ℕ) • charHalf a = fun k => (((a k : ℕ) : ℤ) : ℂ) := by
    intro a; funext k; simp [charHalf]; ring
  rw [nsmul_add, ← mulVec_smul, h2, h2]

end Theta


/-! ## §6. Linear changes of coordinates: biholomorphic group isomorphisms of tori -/

section Iso

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']

/-- A `ℂ`-linear isomorphism `T : E ≃ E'` with `T(Λ) = Λ'` induces a group isomorphism
`E ⧸ Λ ≃ E' ⧸ Λ'`. -/
def torusAddEquiv (Λ' : Submodule ℤ E') (T : E ≃L[ℂ] E')
    (hT : Λ.map (T.toLinearEquiv.toLinearMap.restrictScalars ℤ) = Λ') :
    Torus Λ ≃+ Torus Λ' :=
  QuotientAddGroup.congr _ _ T.toLinearEquiv.toAddEquiv (by
    rw [← hT]
    ext v
    simp [AddSubgroup.mem_map, Submodule.mem_map])

theorem torusAddEquiv_proj (Λ' : Submodule ℤ E') (T : E ≃L[ℂ] E')
    (hT : Λ.map (T.toLinearEquiv.toLinearMap.restrictScalars ℤ) = Λ') (v : E) :
    torusAddEquiv Λ Λ' T hT (proj Λ v) = proj Λ' (T v) := rfl

theorem torusAddEquiv_symm_proj (Λ' : Submodule ℤ E') (T : E ≃L[ℂ] E')
    (hT : Λ.map (T.toLinearEquiv.toLinearMap.restrictScalars ℤ) = Λ') (v : E') :
    (torusAddEquiv Λ Λ' T hT).symm (proj Λ' v) = proj Λ (T.symm v) := rfl

/-- **The induced map is biholomorphic**: an analytic diffeomorphism `E ⧸ Λ ≃ E' ⧸ Λ'`, additive
by `torusAddEquiv`. -/
def torusDiffeo (Λ' : Submodule ℤ E') [DiscreteTopology Λ'] (T : E ≃L[ℂ] E')
    (hT : Λ.map (T.toLinearEquiv.toLinearMap.restrictScalars ℤ) = Λ') :
    Torus Λ ≃ₘ^ω⟮𝓘(ℂ, E), 𝓘(ℂ, E')⟯ Torus Λ' where
  toEquiv := (torusAddEquiv Λ Λ' T hT).toEquiv
  contMDiff_toFun := contMDiff_of_comp_proj Λ
    ((contMDiff_proj Λ').comp (contMDiff_iff_contDiff.mpr T.contDiff))
  contMDiff_invFun := contMDiff_of_comp_proj Λ'
    ((contMDiff_proj Λ).comp (contMDiff_iff_contDiff.mpr T.symm.contDiff))

theorem torusDiffeo_apply (Λ' : Submodule ℤ E') [DiscreteTopology Λ'] (T : E ≃L[ℂ] E')
    (hT : Λ.map (T.toLinearEquiv.toLinearMap.restrictScalars ℤ) = Λ') (q : Torus Λ) :
    torusDiffeo Λ Λ' T hT q = torusAddEquiv Λ Λ' T hT q := rfl

end Iso


/-! ## §7. pkg-I1's QM lattice `ι(𝒪)(τ, 1)ᵀ` and its period matrix `Ω(τ)`

The definitions `B`, `oBasis`, `Mi`, `Mj`, `iota`, `latVec`, `Emat`, `F0mat`, `Pinv`, `Omega` are
copied verbatim from `scratch/pkg-I1/I1.lean` (§1, §2, §4). We prove: for `Im τ ≠ 0`,
* `Λ_τ = ι(𝒪)(τ, 1)ᵀ` is a full lattice in `ℂ²`;
* `F'(τ) = F₀(τ)P⁻¹` is invertible and carries `Ω(τ)ℤ² + ℤ²` onto `Λ_τ`;
* hence `det Im Ω(τ) ≠ 0` and `F'(τ)` induces a biholomorphic group isomorphism
  `ℂ² ⧸ Λ_{Ω(τ)} ≃ ℂ² ⧸ Λ_τ`: `Ω(τ)` is a period matrix of the QM torus `A_τ = ℂ² ⧸ Λ_τ`
  (pkg-I1 §4 claimed this from numerical checks; the polarization is not treated here). -/

namespace QM

open Matrix

/-- (pkg-I1) `B = (2,-3)`. -/
abbrev B := QuaternionAlgebra ℚ 2 0 (-3)

/-- (pkg-I1) N5's ordered basis `(1, i, (1+j)/2, (i+ij)/2)` of the maximal order `𝒪`. -/
def oBasis : Fin 4 → B := ![⟨1, 0, 0, 0⟩, ⟨0, 1, 0, 0⟩, ⟨1/2, 0, 1/2, 0⟩, ⟨0, 1/2, 0, 1/2⟩]

/-- (pkg-I1) `ι(i) = [[√2,0],[0,-√2]]`. -/
def Mi : Matrix (Fin 2) (Fin 2) ℝ := !![√2, 0; 0, -√2]
/-- (pkg-I1) `ι(j) = [[0,-3],[1,0]]`. -/
def Mj : Matrix (Fin 2) (Fin 2) ℝ := !![0, -3; 1, 0]

/-- (pkg-I1) The real embedding `ι : B → M₂(ℝ)`. -/
def iota (x : B) : Matrix (Fin 2) (Fin 2) ℝ :=
  (x.re : ℝ) • 1 + (x.imI : ℝ) • Mi + (x.imJ : ℝ) • Mj + (x.imK : ℝ) • (Mi * Mj)

/-- (pkg-I1) `ι(x)·(τ, 1)ᵀ`. -/
def latVec (x : B) (τ : ℂ) : Fin 2 → ℂ := (iota x).map (fun r : ℝ => (r : ℂ)) *ᵥ ![τ, 1]

/-- (pkg-I1) `E(τ)`: columns `ι(1)v_τ`, `ι(i)v_τ`. -/
def Emat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 0) τ, latVec (oBasis 1) τ] c r

/-- (pkg-I1) `F₀(τ)`: columns `ι((1+j)/2)v_τ`, `ι((i+ij)/2)v_τ`. -/
def F0mat (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun r c => ![latVec (oBasis 2) τ, latVec (oBasis 3) τ] c r

/-- (pkg-I1) `P⁻¹` for `P = [[-1,1],[1,-2]]`. -/
def Pinv : Matrix (Fin 2) (Fin 2) ℂ := !![-2, -1; -1, -1]

/-- (pkg-I1) The period matrix `Ω(τ) = (F₀(τ)P⁻¹)⁻¹E(τ)`. -/
def Omega (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := (F0mat τ * Pinv)⁻¹ * Emat τ

theorem latVec0 (τ : ℂ) : latVec (oBasis 0) τ = ![τ, 1] := by
  ext i; fin_cases i <;> simp [latVec, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two]

theorem latVec1 (τ : ℂ) : latVec (oBasis 1) τ = ![√2 * τ, -√2] := by
  ext i; fin_cases i <;> simp [latVec, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two]

theorem latVec2 (τ : ℂ) : latVec (oBasis 2) τ = ![(τ - 3) / 2, (τ + 1) / 2] := by
  ext i; fin_cases i <;>
    simp [latVec, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two] <;> ring

theorem latVec3 (τ : ℂ) : latVec (oBasis 3) τ = ![√2 * (τ - 3) / 2, -(√2 * (τ + 1)) / 2] := by
  ext i; fin_cases i <;>
    simp [latVec, iota, oBasis, Mi, Mj, mulVec, dotProduct, Fin.sum_univ_two] <;>
    ring


theorem Emat_eq (τ : ℂ) : Emat τ = !![τ, √2 * τ; 1, -√2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [Emat, latVec0, latVec1]

theorem F0mat_eq (τ : ℂ) :
    F0mat τ = !![(τ - 3) / 2, √2 * (τ - 3) / 2; (τ + 1) / 2, -(√2 * (τ + 1)) / 2] := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [F0mat, latVec2, latVec3]

/-- `F'(τ) = F₀(τ)P⁻¹`. -/
def Fp (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := F0mat τ * Pinv

theorem det_Fp (τ : ℂ) : (Fp τ).det = -((√2 : ℂ) * (τ - 3) * (τ + 1)) / 2 := by
  rw [Fp, det_mul, F0mat_eq, Pinv, det_fin_two_of, det_fin_two_of]
  ring

theorem sqrt2_ne_zero : (√2 : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr two_pos)

theorem det_Fp_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) : (Fp τ).det ≠ 0 := by
  rw [det_Fp]
  have h3 : τ - 3 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have h1 : τ + 1 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have := sqrt2_ne_zero
  field_simp
  simp [this, h3, h1]

theorem Fp_mul_Omega {τ : ℂ} (hτ : τ.im ≠ 0) : Fp τ * Omega τ = Emat τ := by
  rw [Omega, ← Fp, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (Ne.isUnit (det_Fp_ne_zero hτ)),
    Matrix.one_mul]

/-- The four generators `ι(b_k)(τ, 1)ᵀ` of `Λ_τ`. -/
def qmVec (τ : ℂ) (k : Fin 4) : Fin 2 → ℂ := latVec (oBasis k) τ


theorem qmVec_linearIndependent {τ : ℂ} (hτ : τ.im ≠ 0) : LinearIndependent ℝ (qmVec τ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have e0 := congrFun hc 0
  have e1 := congrFun hc 1
  simp only [qmVec, Fin.sum_univ_four, latVec0, latVec1, latVec2, latVec3, Finset.sum_apply,
    Pi.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
    Complex.real_smul] at e0 e1
  have r0 := congrArg Complex.re e0
  have i0 := congrArg Complex.im e0
  have r1 := congrArg Complex.re e1
  have i1 := congrArg Complex.im e1
  simp at r0 i0 r1 i1
  set x := τ.re
  set y := τ.im
  have hs : √2 ≠ 0 := Real.sqrt_ne_zero'.mpr two_pos
  have hA : y * (c 2 - √2 * c 3) = 0 := by linear_combination 2 * i1
  have A : c 2 - √2 * c 3 = 0 := (mul_eq_zero.mp hA).resolve_left hτ
  have hK : y * (c 0 + √2 * c 1 + c 2 / 2 + √2 * c 3 / 2) = 0 := by linear_combination i0
  have K : c 0 + √2 * c 1 + c 2 / 2 + √2 * c 3 / 2 = 0 := (mul_eq_zero.mp hK).resolve_left hτ
  have Bq : c 2 + √2 * c 3 = 0 := by linear_combination (2 / 3 * x) * K - (2 / 3) * r0
  have h3' : √2 * c 3 = 0 := by linear_combination (Bq - A) / 2
  have h3 : c 3 = 0 := (mul_eq_zero.mp h3').resolve_left hs
  have h2 : c 2 = 0 := by linear_combination A + h3'
  have C : c 0 - √2 * c 1 = 0 := by linear_combination r1 - ((x + 1) / 2) * A
  have h1' : √2 * c 1 = 0 := by linear_combination (K - C) / 2 - Bq / 4
  have h1 : c 1 = 0 := (mul_eq_zero.mp h1').resolve_left hs
  have h0 : c 0 = 0 := by linear_combination C + h1'
  intro i; fin_cases i <;> assumption


/-- The ordered `ℝ`-basis `ι(b_k)(τ, 1)ᵀ` of `ℂ²` (for `Im τ ≠ 0`). -/
def qmBasis {τ : ℂ} (hτ : τ.im ≠ 0) : Module.Basis (Fin 4) ℝ (Fin 2 → ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank' _ (qmVec_linearIndependent hτ) (by
    rw [Module.finrank_pi_fintype]; simp [Complex.finrank_real_complex])

/-- **The QM lattice `Λ_τ = ι(𝒪)(τ, 1)ᵀ`**, the period lattice of N5's QM surface at `τ`. -/
def qmLattice {τ : ℂ} (hτ : τ.im ≠ 0) : Submodule ℤ (Fin 2 → ℂ) :=
  Submodule.span ℤ (Set.range (qmBasis hτ))

instance {τ : ℂ} (hτ : τ.im ≠ 0) : DiscreteTopology (qmLattice hτ) := by
  unfold qmLattice; infer_instance

instance {τ : ℂ} (hτ : τ.im ≠ 0) : IsZLattice ℝ (qmLattice hτ) := by
  unfold qmLattice; infer_instance

theorem qmLattice_eq {τ : ℂ} (hτ : τ.im ≠ 0) :
    qmLattice hτ = Submodule.span ℤ (Set.range (qmVec τ)) := by
  simp [qmLattice, qmBasis]

/-- The QM torus `A_τ = ℂ² ⧸ ι(𝒪)(τ, 1)ᵀ`: a compact connected complex Lie group of dimension 2. -/
abbrev QMTorus {τ : ℂ} (hτ : τ.im ≠ 0) := Torus (qmLattice hτ)

example {τ : ℂ} (hτ : τ.im ≠ 0) : LieAddGroup 𝓘(ℂ, Fin 2 → ℂ) ω (QMTorus hτ) := inferInstance
example {τ : ℂ} (hτ : τ.im ≠ 0) : CompactSpace (QMTorus hτ) := inferInstance

theorem mulVec_col (A M : Matrix (Fin 2) (Fin 2) ℂ) (j : Fin 2) :
    (A *ᵥ fun i => M i j) = fun i => (A * M) i j := by
  funext i; simp [mulVec, dotProduct, mul_apply]

/-- Images of the period vectors of `Ω(τ)` under `F'(τ)`. -/
theorem Fp_mulVec_periodVec {τ : ℂ} (hτ : τ.im ≠ 0) (k : Fin 2 ⊕ Fin 2) :
    Fp τ *ᵥ periodVec (Omega τ) k =
      match k with
      | Sum.inl 0 => qmVec τ 0
      | Sum.inl 1 => qmVec τ 1
      | Sum.inr 0 => -(2 : ℤ) • qmVec τ 2 - qmVec τ 3
      | Sum.inr 1 => -qmVec τ 2 - qmVec τ 3 := by
  rcases k with j | j
  · rw [periodVec, mulVec_col, Fp_mul_Omega hτ, Emat_eq]
    fin_cases j <;> funext i <;> fin_cases i <;> simp [qmVec, latVec0, latVec1]
  · rw [periodVec, mulVec_single_one]
    fin_cases j <;> funext i <;> fin_cases i <;>
      simp [Fp, F0mat_eq, Pinv, qmVec, latVec2, latVec3] <;> ring


/-- Conversely to `periodVec_linearIndependent`: if the period vectors of `Ω` are `ℝ`-independent,
then `det (Im Ω) ≠ 0`. -/
theorem det_im_ne_zero_of_linearIndependent {g : ℕ} (Ω : Matrix (Fin g) (Fin g) ℂ)
    (h : LinearIndependent ℝ (periodVec Ω)) : (Ω.map Complex.im).det ≠ 0 := by
  intro hdet
  obtain ⟨a, ha0, ha⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hrel := Fintype.linearIndependent_iff.mp h
    (Sum.elim a (fun i => -∑ j, (Ω i j).re * a j)) (by
      funext i
      have hi := congrFun ha i
      simp only [mulVec, dotProduct, Matrix.map_apply, Pi.zero_apply] at hi
      simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Finset.sum_apply,
        Pi.smul_apply, periodVec, Pi.zero_apply, Pi.single_apply, smul_ite, smul_zero]
      apply Complex.ext
      · simp [Complex.re_sum, mul_comm]
      · simpa [Complex.im_sum, mul_comm] using hi)
  exact ha0 (funext fun j => by simpa using hrel (Sum.inl j))

/-- The images `F'(τ)·(period vectors of Ω(τ))`, explicitly. -/
def imgVec (τ : ℂ) : Fin 2 ⊕ Fin 2 → (Fin 2 → ℂ) :=
  Sum.elim ![qmVec τ 0, qmVec τ 1] ![-(2 : ℤ) • qmVec τ 2 - qmVec τ 3, -qmVec τ 2 - qmVec τ 3]

theorem Fp_mulVec_periodVec' {τ : ℂ} (hτ : τ.im ≠ 0) (k : Fin 2 ⊕ Fin 2) :
    Fp τ *ᵥ periodVec (Omega τ) k = imgVec τ k := by
  rw [Fp_mulVec_periodVec hτ]
  rcases k with j | j <;> fin_cases j <;> rfl

theorem imgVec_linearIndependent {τ : ℂ} (hτ : τ.im ≠ 0) : LinearIndependent ℝ (imgVec τ) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set d : Fin 4 → ℝ := ![c (Sum.inl 0), c (Sum.inl 1), -2 * c (Sum.inr 0) - c (Sum.inr 1),
      -c (Sum.inr 0) - c (Sum.inr 1)] with hd
  have hsum : ∑ k, d k • qmVec τ k = ∑ i, c i • imgVec τ i := by
    have e : ∑ k, d k • qmVec τ k = c (Sum.inl 0) • qmVec τ 0 + c (Sum.inl 1) • qmVec τ 1 +
        (-2 * c (Sum.inr 0) - c (Sum.inr 1)) • qmVec τ 2 +
        (-c (Sum.inr 0) - c (Sum.inr 1)) • qmVec τ 3 := by
      simp [Fin.sum_univ_four, d]
    rw [e]
    simp only [Fintype.sum_sum_type, Fin.sum_univ_two, imgVec, Sum.elim_inl, Sum.elim_inr]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue]
    rw [← Int.cast_smul_eq_zsmul ℝ]
    module
  have key := Fintype.linearIndependent_iff.mp (qmVec_linearIndependent hτ) d (hsum.trans hc)
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have k3 := key 3
  simp [d] at k0 k1 k2 k3
  rintro (j | j) <;> fin_cases j
  · simpa using k0
  · simpa using k1
  · simp; linarith
  · simp; linarith

theorem span_imgVec {τ : ℂ} :
    Submodule.span ℤ (Set.range (imgVec τ)) = Submodule.span ℤ (Set.range (qmVec τ)) := by
  have hq : ∀ i, qmVec τ i ∈ Submodule.span ℤ (Set.range (qmVec τ)) :=
    fun i => Submodule.subset_span ⟨i, rfl⟩
  have hp : ∀ k, imgVec τ k ∈ Submodule.span ℤ (Set.range (imgVec τ)) :=
    fun k => Submodule.subset_span ⟨k, rfl⟩
  have i0 : imgVec τ (Sum.inr 0) = -(2 : ℤ) • qmVec τ 2 - qmVec τ 3 := rfl
  have i1 : imgVec τ (Sum.inr 1) = -qmVec τ 2 - qmVec τ 3 := rfl
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rcases k with j | j <;> fin_cases j
    · exact hq 0
    · exact hq 1
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ (hq 2)) (hq 3)
    · exact Submodule.sub_mem _ (Submodule.neg_mem _ (hq 2)) (hq 3)
  · rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    rw [SetLike.mem_coe]
    fin_cases k
    · exact hp (Sum.inl 0)
    · exact hp (Sum.inl 1)
    · have h := Submodule.add_mem _ (Submodule.neg_mem _ (hp (Sum.inr 0))) (hp (Sum.inr 1))
      have e : qmVec τ 2 = -imgVec τ (Sum.inr 0) + imgVec τ (Sum.inr 1) := by
        rw [i0, i1]; module
      show qmVec τ 2 ∈ _
      rw [e]; exact h
    · have h := Submodule.sub_mem _ (hp (Sum.inr 0)) (Submodule.smul_mem _ (2 : ℤ) (hp (Sum.inr 1)))
      have e : qmVec τ 3 = imgVec τ (Sum.inr 0) - (2 : ℤ) • imgVec τ (Sum.inr 1) := by
        rw [i0, i1]; module
      show qmVec τ 3 ∈ _
      rw [e]; exact h

end QM

end BPAnalytic
