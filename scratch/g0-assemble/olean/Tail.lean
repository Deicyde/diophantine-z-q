import LPrefix
import ZInQKernel.Multiplication.Certificate.ConstantsProperties
import ZInQKernel.Progressions.Final.Instance
import ZInQKernel.Size.Constants.T

/-! ## Kernel copy: ZInQKernel/HDecomp/Analytic/Torus.lean and QMLattice.lean (bp-analytic), verbatim minus imports; needed by g0-thetapoint -/
section BPAnalyticTorusSec

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/bp-analytic/Torus.lean`, §1-§6.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


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
    exp (Real.pi * I * ((intVec n + c) ⬝ᵥ (Ω *ᵥ (intVec n + c))) + 2 * Real.pi * I * ((intVec n + c)
        ⬝ᵥ d))

/-- **Theta constants are values of `θ` at torsion points**:
`θ[c, d](Ω) = exp(πi cᵀΩc + 2πi cᵀd) · θ(Ωc + d, Ω)`. -/
theorem thetaChar_eq (c d : Fin g → ℂ) (Ω : Matrix (Fin g) (Fin g) ℂ) (hΩ : Ωᵀ = Ω) :
    thetaChar c d Ω =
      exp (Real.pi * I * (c ⬝ᵥ (Ω *ᵥ c)) + 2 * Real.pi * I * (c ⬝ᵥ d)) * riemannTheta Ω (Ω *ᵥ c + d)
          := by
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

end BPAnalytic
end
end BPAnalyticTorusSec
section BPAnalyticQMLatticeSec

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/bp-analytic/Torus.lean`, §7.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/

open scoped Manifold ContDiff Topology
open Set Filter

set_option linter.unusedSectionVars false

noncomputable section

namespace BPAnalytic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

variable (Λ : Submodule ℤ E) [DiscreteTopology Λ]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] {H' : Type*} [TopologicalSpace H']
  {I' : ModelWithCorners ℂ F H'} {M : Type*} [TopologicalSpace M] [ChartedSpace H' M]

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

/-- `F'(τ)` as a continuous `ℂ`-linear automorphism of `ℂ²`. -/
def FpEquiv {τ : ℂ} (hτ : τ.im ≠ 0) : (Fin 2 → ℂ) ≃L[ℂ] (Fin 2 → ℂ) :=
  (Matrix.toLinearEquiv' (Fp τ)
    (Matrix.invertibleOfIsUnitDet _ (Ne.isUnit (det_Fp_ne_zero hτ)))).toContinuousLinearEquiv

theorem FpEquiv_apply {τ : ℂ} (hτ : τ.im ≠ 0) (v : Fin 2 → ℂ) : FpEquiv hτ v = Fp τ *ᵥ v := rfl

/-- **`det Im Ω(τ) ≠ 0`** for `Im τ ≠ 0` (so `Ω(τ)ℤ² + ℤ²` is a full lattice). -/
theorem det_im_Omega_ne_zero {τ : ℂ} (hτ : τ.im ≠ 0) : ((Omega τ).map Complex.im).det ≠ 0 := by
  apply det_im_ne_zero_of_linearIndependent
  apply LinearIndependent.of_comp ((Matrix.toLin' (Fp τ)).restrictScalars ℝ)
  have : ((Matrix.toLin' (Fp τ)).restrictScalars ℝ) ∘ periodVec (Omega τ) = imgVec τ := by
    funext k
    simp only [Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.toLin'_apply]
    exact Fp_mulVec_periodVec' hτ k
  rw [this]
  exact imgVec_linearIndependent hτ

/-- **`F'(τ)` carries the Siegel lattice `Ω(τ)ℤ² + ℤ²` onto the QM lattice `ι(𝒪)(τ, 1)ᵀ`.** -/
theorem map_periodLattice_Omega {τ : ℂ} (hτ : τ.im ≠ 0) :
    (periodLattice (Omega τ) (det_im_Omega_ne_zero hτ)).map
      ((FpEquiv hτ).toLinearEquiv.toLinearMap.restrictScalars ℤ) = qmLattice hτ := by
  rw [periodLattice, coe_periodBasis, Submodule.map_span, ← Set.range_comp, qmLattice_eq,
    ← span_imgVec]
  congr 2
  funext k
  exact Fp_mulVec_periodVec' hτ k

/-- **`Ω(τ)` is a period matrix of the QM torus**: `F'(τ)` induces a biholomorphic group
isomorphism `ℂ² ⧸ (Ω(τ)ℤ² + ℤ²) ≃ ℂ² ⧸ ι(𝒪)(τ, 1)ᵀ`. -/
def qmPeriodDiffeo {τ : ℂ} (hτ : τ.im ≠ 0) :
    SiegelTorus (Omega τ) (det_im_Omega_ne_zero hτ) ≃ₘ^ω⟮𝓘(ℂ, Fin 2 → ℂ), 𝓘(ℂ, Fin 2 → ℂ)⟯
      QMTorus hτ :=
  torusDiffeo _ _ (FpEquiv hτ) (map_periodLattice_Omega hτ)

/-- It is additive (a group isomorphism). -/
theorem qmPeriodDiffeo_add {τ : ℂ} (hτ : τ.im ≠ 0) (p q : SiegelTorus (Omega τ)
    (det_im_Omega_ne_zero hτ)) :
    qmPeriodDiffeo hτ (p + q) = qmPeriodDiffeo hτ p + qmPeriodDiffeo hτ q :=
  map_add (torusAddEquiv _ _ (FpEquiv hτ) (map_periodLattice_Omega hτ)) p q

theorem qmPeriodDiffeo_proj {τ : ℂ} (hτ : τ.im ≠ 0) (v : Fin 2 → ℂ) :
    qmPeriodDiffeo hτ (proj _ v) = proj (qmLattice hτ) (Fp τ *ᵥ v) := rfl

theorem sqrt2_sq : (√2 : ℂ) ^ 2 = 2 := by
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]; norm_num

/-- The compatibility `F' Eᵀ = E F'ᵀ` (the Riemann form is alternating in N5's basis). -/
theorem Fp_mul_Emat_transpose (τ : ℂ) : Fp τ * (Emat τ)ᵀ = Emat τ * (Fp τ)ᵀ := by
  have h2 := sqrt2_sq
  rw [Fp, F0mat_eq, Emat_eq, Pinv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply] <;> ring_nf <;>
    simp only [h2] <;> ring_nf

/-- **`Ω(τ)` is symmetric** (for `Im τ ≠ 0`). -/
theorem Omega_transpose {τ : ℂ} (hτ : τ.im ≠ 0) : (Omega τ)ᵀ = Omega τ := by
  have hu : IsUnit (Fp τ).det := Ne.isUnit (det_Fp_ne_zero hτ)
  have hut : IsUnit (Fp τ)ᵀ.det := by rwa [det_transpose]
  have key := Fp_mul_Emat_transpose τ
  rw [Omega, ← Fp, transpose_mul, transpose_nonsing_inv]
  calc (Emat τ)ᵀ * ((Fp τ)ᵀ)⁻¹
      = (Fp τ)⁻¹ * (Fp τ * (Emat τ)ᵀ) * ((Fp τ)ᵀ)⁻¹ := by
        rw [← Matrix.mul_assoc (Fp τ)⁻¹, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = (Fp τ)⁻¹ * (Emat τ * (Fp τ)ᵀ) * ((Fp τ)ᵀ)⁻¹ := by rw [key]
    _ = (Fp τ)⁻¹ * Emat τ := by
        rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hut, Matrix.mul_one]

/-- Hence `θ(·, Ω(τ))` is quasi-periodic for `Ω(τ)ℤ² + ℤ² = F'(τ)⁻¹Λ_τ`: it is a section of a
line bundle on the QM torus (via `qmPeriodDiffeo`). -/
theorem riemannTheta_Omega_add_period {τ : ℂ} (hτ : τ.im ≠ 0) (z : Fin 2 → ℂ) (m n : Fin 2 → ℤ) :
    riemannTheta (Omega τ) (z + (Omega τ *ᵥ intVec m + intVec n)) =
      Complex.exp (-(Real.pi * Complex.I * (intVec m ⬝ᵥ (Omega τ *ᵥ intVec m))) -
          2 * Real.pi * Complex.I * (intVec m ⬝ᵥ z)) * riemannTheta (Omega τ) z :=
  riemannTheta_add_period _ (Omega_transpose hτ) z m n

/-! #### `Ω(τ)` lies in the Siegel space for `Im τ > 0` -/

/-- Partial fractions: `Ω(τ) = A₀ + C/(τ+1) + B/(τ−3)` (found with sympy). -/
def OmegaPF (τ : ℂ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (!![-1 + (√2 : ℂ) / 2, 1 - (√2 : ℂ); 1 - (√2 : ℂ), -2 + (√2 : ℂ)] :
      Matrix (Fin 2) (Fin 2) ℂ) +
    (τ + 1)⁻¹ • !![-((√2 : ℂ) + 2) / 2, 1 + (√2 : ℂ); 1 + (√2 : ℂ), -((√2 : ℂ) + 2)] +
    (τ - 3)⁻¹ • !![3 * ((√2 : ℂ) - 2) / 2, -3 * ((√2 : ℂ) - 1); -3 * ((√2 : ℂ) - 1),
      3 * ((√2 : ℂ) - 2)]

theorem Fp_mul_OmegaPF {τ : ℂ} (hτ : τ.im ≠ 0) : Fp τ * OmegaPF τ = Emat τ := by
  have h2 := sqrt2_sq
  have h3 : τ - 3 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  have h1 : τ + 1 ≠ 0 := fun h => hτ (by simpa using congrArg Complex.im h)
  rw [Fp, F0mat_eq, Pinv, Emat_eq, OmegaPF]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring_nf <;>
    simp only [h2] <;> ring_nf

theorem Omega_eq_PF {τ : ℂ} (hτ : τ.im ≠ 0) : Omega τ = OmegaPF τ := by
  have hu : IsUnit (Fp τ).det := Ne.isUnit (det_Fp_ne_zero hτ)
  rw [Omega, ← Fp, ← Fp_mul_OmegaPF hτ, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu,
    Matrix.one_mul]

/-- **`Ω(τ) ∈ 𝔥₂` for `Im τ > 0`.** `Im Ω(τ) = y·(C'/|τ+1|² + B'/|τ−3|²)` with `C'`, `B'` positive
semidefinite of rank one with different kernels. -/
theorem Omega_mem_siegelSpace {τ : ℂ} (hτ : 0 < τ.im) : Omega τ ∈ SiegelSpace 2 := by
  have hτ' : τ.im ≠ 0 := hτ.ne'
  refine ⟨Omega_transpose hτ', ?_⟩
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · show ((Omega τ).map Complex.im)ᴴ = (Omega τ).map Complex.im
    rw [Matrix.conjTranspose_eq_transpose_of_trivial, ← Matrix.transpose_map,
      Omega_transpose hτ']
  · intro x hx
    rw [Omega_eq_PF hτ']
    have hs : (√2 : ℝ) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hp : 0 < Complex.normSq (τ + 1) :=
      Complex.normSq_pos.mpr fun h => hτ' (by simpa using congrArg Complex.im h)
    have hq : 0 < Complex.normSq (τ - 3) :=
      Complex.normSq_pos.mpr fun h => hτ' (by simpa using congrArg Complex.im h)
    simp [OmegaPF, dotProduct, mulVec, Fin.sum_univ_two, Complex.inv_im, Complex.inv_re]
    set y := τ.im
    set P := Complex.normSq (τ + 1)
    set Q := Complex.normSq (τ - 3)
    set r := √2
    rw [show x 0 * ((-y / P * ((-2 + -r) / 2) + -y / Q * (3 * (r - 2) / 2)) * x 0 +
          (-y / P * (1 + r) + -(-y / Q * (3 * (r - 1)))) * x 1) +
        x 1 * ((-y / P * (1 + r) + -(-y / Q * (3 * (r - 1)))) * x 0 +
          (-y / P * (-2 + -r) + -y / Q * (3 * (r - 2))) * x 1) =
        y / P * ((r + 2) / 2 * (x 0 - r * x 1) ^ 2) + y / Q * (3 * (2 - r) / 2 * (x 0 + r * x 1) ^
            2)
      by linear_combination (x 1 * y * (3 * r * x 1 + 6 * x 0 - 6 * x 1) / (2 * Q) +
        x 1 * y * (-r * x 1 + 2 * x 0 - 2 * x 1) / (2 * P)) * hs]
    have hr0 : 0 < r := Real.sqrt_pos.mpr two_pos
    have hr2 : r < 2 := by nlinarith
    have hA : 0 < y / P * ((r + 2) / 2) := mul_pos (div_pos hτ hp) (by linarith)
    have hB : 0 < y / Q * (3 * (2 - r) / 2) := mul_pos (div_pos hτ hq) (by linarith)
    by_contra hle
    push Not at hle
    have hu : (x 0 - r * x 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - r * x 1), sq_nonneg (x 0 + r * x 1),
        mul_nonneg hA.le (sq_nonneg (x 0 - r * x 1)), mul_nonneg hB.le (sq_nonneg (x 0 + r * x 1))]
    have hw : (x 0 + r * x 1) ^ 2 = 0 := by
      nlinarith [sq_nonneg (x 0 - r * x 1), sq_nonneg (x 0 + r * x 1),
        mul_nonneg hA.le (sq_nonneg (x 0 - r * x 1)), mul_nonneg hB.le (sq_nonneg (x 0 + r * x 1))]
    have hu' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hu
    have hw' := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hw
    have hx1 : x 1 = 0 := by
      have : r * x 1 = 0 := by linarith
      exact (mul_eq_zero.mp this).resolve_left hr0.ne'
    have hx0 : x 0 = 0 := by linarith
    exact hx (funext fun i => by fin_cases i <;> simp [hx0, hx1])

end QM

end BPAnalytic
end
end BPAnalyticQMLatticeSec


/-! ## g0-dim: `DimFinite` and `DimBaseChange` proved (task g0-dim; body of `scratch/g0-dim/Dim.lean` §1-§2) -/

section G0DimSec

set_option linter.style.haveILetI false

open Order TensorProduct

namespace G0Dim

/-! ## §1. Commutative algebra -/


/-- Integral injective extensions have the same Krull dimension (going up + incomparability;
Stacks 00OK, Matsumura Thm 9.4 — STANDARD). -/
theorem ringKrullDim_eq_of_isIntegral_of_injective {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.IsIntegral A B] (hinj : Function.Injective (algebraMap A B)) :
    ringKrullDim B = ringKrullDim A := by
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A B)) ?_
    intro P Q hPQ
    have h : P.asIdeal < Q.asIdeal := hPQ
    exact Ideal.IsIntegral.under_lt_under (R := A) h
  · refine iSup_le fun l => ?_
    obtain ⟨P, -, hP, hPl⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (S := B)
      l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A B x = 0 := by simpa using hx
        have : x = 0 := hinj (by simpa using this)
        simp [this])
    haveI : P.LiesOver l.head.asIdeal := ⟨hPl.symm⟩
    obtain ⟨L, hlen, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact L.length_le_krullDim

theorem ringKrullDim_mvPolynomial_field (k : Type*) [Field k] (s : ℕ) :
    ringKrullDim (MvPolynomial (Fin s) k) = s := by
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field]
  simp

/-- **Stacks 00P4 (affine case), proved.** For a finitely generated algebra `R` over a field `K`
and any field extension `L/K`, `dim (R ⊗_K L) = dim R`. Proof: Noether normalization
`K[X_1..X_s] → R` (finite, injective) base-changes to `L[X_1..X_s] → R ⊗ L` (finite, injective
since `L` is flat over `K`). -/
theorem ringKrullDim_tensor_field (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] (L : Type*) [Field L] [Algebra K L] :
    ringKrullDim (R ⊗[K] L) = ringKrullDim R := by
  rcases subsingleton_or_nontrivial R with h | h
  · haveI : Subsingleton (R ⊗[K] L) := by
      have h1 : (1 : R ⊗[K] L) = 0 := by
        rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, TensorProduct.zero_tmul]
      exact subsingleton_of_zero_eq_one h1.symm
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton]
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    have hR : ringKrullDim R = s := by
      letI := g.toRingHom.toAlgebra
      haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
      rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
        ringKrullDim_mvPolynomial_field]
    let g' := Algebra.TensorProduct.map g (AlgHom.id K L)
    have g'inj : Function.Injective g' :=
      Module.Flat.rTensor_preserves_injective_linearMap (M := L) g.toLinearMap ginj
    have g'fin : g'.toRingHom.Finite := RingHom.Finite.tensorProductMap gfin (by exact RingHom.Finite.id L)
    have hP : ringKrullDim (MvPolynomial (Fin s) K ⊗[K] L) = s := by
      rw [ringKrullDim_eq_of_ringEquiv ((Algebra.TensorProduct.comm K _ L).toRingEquiv.trans
        (MvPolynomial.algebraTensorAlgEquiv K L).toRingEquiv), ringKrullDim_mvPolynomial_field]
    rw [hR, ← hP]
    letI := g'.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K ⊗[K] L) (R ⊗[K] L) := ⟨g'fin.to_isIntegral⟩
    exact ringKrullDim_eq_of_isIntegral_of_injective g'inj

/-- A finitely generated algebra over a field has finite Krull dimension (or is zero). -/
theorem ringKrullDim_le_of_finiteType (K : Type*) [Field K] (R : Type*) [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] : ∃ n : ℕ, ringKrullDim R ≤ n := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le⟩
  · obtain ⟨s, g, ginj, gfin⟩ := exists_finite_inj_algHom_of_fg K R
    letI := g.toRingHom.toAlgebra
    haveI : Algebra.IsIntegral (MvPolynomial (Fin s) K) R := ⟨gfin.to_isIntegral⟩
    refine ⟨s, le_of_eq ?_⟩
    rw [ringKrullDim_eq_of_isIntegral_of_injective (A := MvPolynomial (Fin s) K) ginj,
      ringKrullDim_mvPolynomial_field]


/-! ## §2. Topology and schemes -/

open TopologicalSpace Topology


/-- The Krull dimension of a space is the supremum of the dimensions of the members of a cover
by open embeddings (Stacks 0055 for open covers; STANDARD). -/
theorem topologicalKrullDim_eq_iSup_of_openEmbedding {X : Type*} [TopologicalSpace X] {ι : Type*}
    {Y : ι → Type*} [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X)
    (hf : ∀ i, IsOpenEmbedding (f i)) (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (Y i) := by
  apply le_antisymm
  · refine iSup_le fun p => ?_
    obtain ⟨x, hx⟩ := p.head.isIrreducible.nonempty
    obtain ⟨i, y, rfl⟩ := hcov x
    let e := IrreducibleCloseds.orderIsoOfIsOpenEmbedding (f i) (hf i)
    have hmem : ∀ j, (f i ⁻¹' (p j : Set X)).Nonempty := fun j =>
      ⟨y, p.monotone (Fin.zero_le j) hx⟩
    let q : LTSeries {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} :=
      { length := p.length
        toFun := fun j => ⟨p j, hmem j⟩
        step := fun j => p.step j }
    calc (p.length : WithBot ℕ∞) = q.length := rfl
      _ ≤ krullDim {V : IrreducibleCloseds X | (f i ⁻¹' V).Nonempty} := q.length_le_krullDim
      _ = topologicalKrullDim (Y i) := (Order.krullDim_eq_of_orderIso e).symm
      _ ≤ ⨆ i, topologicalKrullDim (Y i) := le_iSup (fun i => topologicalKrullDim (Y i)) i
  · exact iSup_le fun i => (hf i).isInducing.topologicalKrullDim_le

open AlgebraicGeometry CategoryTheory Limits

theorem scheme_dim_eq_iSup_cover {X : Scheme} (𝒰 : X.OpenCover) :
    topologicalKrullDim X = ⨆ i, topologicalKrullDim (𝒰.X i) :=
  topologicalKrullDim_eq_iSup_of_openEmbedding (fun i => 𝒰.f i) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩)

theorem scheme_dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

theorem spec_dim (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R


/-- **Stacks 00P4, affine piece over `Spec K`.** For `m : Spec R → Spec K` locally of finite
type, `Spec R ×_K Spec L ≅ Spec (R ⊗_K L)` has the dimension of `Spec R`. -/
theorem dim_pullback_spec {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType m] :
    topologicalKrullDim (pullback m (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim (Spec R) := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  have e := scheme_dim_eq_of_iso (pullbackSpecIso K R L)
  refine e.trans ?_
  rw [spec_dim, spec_dim]
  exact ringKrullDim_tensor_field K R L

/-- A scheme of finite type over a field: each affine piece `Spec R → Spec K` has bounded
dimension. -/
theorem dim_spec_le {K : Type} [Field K] (R : CommRingCat.{0}) (m : Spec R ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType m] : ∃ n : ℕ, topologicalKrullDim (Spec R) ≤ n := by
  obtain ⟨φ, rfl⟩ : ∃ φ, Spec.map φ = m := ⟨Spec.preimage m, Spec.map_preimage m⟩
  have hφ : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp inferInstance
  letI : Algebra K R := φ.hom.toAlgebra
  haveI : Algebra.FiniteType K R := hφ
  rw [spec_dim]
  exact ringKrullDim_le_of_finiteType K R

/-- **Dimension is invariant under field base change** (Stacks 00P4 globalized; proved). For a
scheme `X` locally of finite type over a field `K` and any field extension `L/K`,
`dim (X ×_K L) = dim X`. -/
theorem dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L] (X : Scheme.{0})
    (h : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType h] :
    topologicalKrullDim (pullback h (Spec.map (CommRingCat.ofHom (algebraMap K L))) : Scheme) =
      topologicalKrullDim X := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap K L))
  let 𝒰 := X.affineCover
  rw [scheme_dim_eq_iSup_cover 𝒰, scheme_dim_eq_iSup_cover (𝒰.pullback₁ (pullback.fst h g))]
  refine iSup_congr fun i => ?_
  have e : (𝒰.pullback₁ (pullback.fst h g)).X i ≅ pullback (𝒰.f i ≫ h) g :=
    (pullbackSymmetry _ _).trans (pullbackRightPullbackFstIso h g (𝒰.f i))
  rw [scheme_dim_eq_of_iso e]
  haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
  have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
  exact @dim_pullback_spec K _ L _ _ _ (𝒰.f i ≫ h) hc

theorem exists_nat_of_le (x : WithBot ℕ∞) (h0 : x ≠ ⊥) (N : ℕ) (h : x ≤ N) :
    ∃ n : ℕ, x = n := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd rfl h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top =>
      have h' : ((⊤ : ℕ∞) : WithBot ℕ∞) ≤ ((N : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast h
      exact absurd (WithBot.coe_le_coe.mp h') (by simp)
    | coe n => exact ⟨n, rfl⟩

/-- **A nonempty scheme of finite type over a field has finite dimension** (proved). -/
theorem dim_finite {K : Type} [Field K] (X : Scheme.{0}) (h : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType h] [QuasiCompact h] [Nonempty X] :
    ∃ n : ℕ, topologicalKrullDim X = n := by
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace h
  let 𝒰 := X.affineCover.finiteSubcover
  have hb : ∀ i, ∃ n : ℕ, topologicalKrullDim (𝒰.X i) ≤ n := fun i => by
    haveI : IsOpenImmersion (𝒰.f i) := 𝒰.map_prop i
    have hc : LocallyOfFiniteType (𝒰.f i ≫ h) := locallyOfFiniteType_comp _ _
    exact @dim_spec_le K _ _ (𝒰.f i ≫ h) hc
  choose n hn using hb
  have hle : topologicalKrullDim X ≤ ((∑ i, n i : ℕ) : WithBot ℕ∞) := by
    rw [scheme_dim_eq_iSup_cover 𝒰]
    refine iSup_le fun i => (hn i).trans ?_
    exact_mod_cast Finset.single_le_sum (fun j _ => Nat.zero_le (n j)) (Finset.mem_univ i)
  have hne : topologicalKrullDim X ≠ ⊥ := by
    obtain ⟨x⟩ := ‹Nonempty X›
    haveI : Nonempty (IrreducibleCloseds X) :=
      ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    exact Order.krullDim_ne_bot_iff.mpr inferInstance
  exact exists_nat_of_le _ hne _ hle

end G0Dim

namespace HSyn.G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **`DimBaseChange` (missing piece 2), proved** from `G0Dim.dim_baseChange`. -/
theorem dimBaseChange : DimBaseChange := by
  intro K _ L _ _ A
  exact G0Dim.dim_baseChange L A.X.left A.X.hom

/-- **`DimFinite` (missing piece 1), proved** from `G0Dim.dim_finite`. -/
theorem dimFinite : DimFinite := by
  intro K _ A
  haveI : Nonempty A.X.left :=
    ⟨η[A.X].left (Nonempty.some (inferInstance : Nonempty (Spec (CommRingCat.of K))))⟩
  exact G0Dim.dim_finite A.X.left A.X.hom

end HSyn.G0Split

/-- `dim (A_L) = dim A` for I3's `PkgI3.AbVar.baseChange` (the same proof as `dimBaseChange`). -/
theorem G0Dim.pkgI3_dim_baseChange {K : Type} [Field K] (L : Type) [Field L] [Algebra K L]
    (A : PkgI3.AbVar K) : (A.baseChange L).dim = A.dim :=
  G0Dim.dim_baseChange L A.X.left A.X.hom

end G0DimSec

/-! ## g0-product: §2-§5 of scratch/g0-product/Product.lean (names moved to HSyn.G0Split, as in its mkcheck.sh) -/
section G0ProductSec
noncomputable section
/-! ## §2. The product is an abelian variety (proved, Mathlib only) -/

namespace G0Product

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

/-- **Glue (proved).** Geometric integrality is stable under composition `X → Y → S` when the
first map is geometrically integral, flat and universally open and the second is geometrically
integral and locally of finite type. For a field `K` and `Spec K → S`, the base change
`X ×_S K = X ×_Y (Y ×_S K)` is integral by Mathlib's
`AlgebraicGeometry.GeometricallyIntegral.isIntegral_of_isLocallyNoetherian` applied over the
integral, locally noetherian scheme `Y ×_S K`. -/
theorem geometricallyIntegral_comp {X Y S : Scheme} (g : X ⟶ Y) (h : Y ⟶ S)
    [GeometricallyIntegral g] [Flat g] [UniversallyOpen g]
    [GeometricallyIntegral h] [LocallyOfFiniteType h] :
    GeometricallyIntegral (g ≫ h) := by
  refine ⟨fun K _ y Z fst snd hP => ?_⟩
  have : IsIntegral (pullback h y) := pullback_of_geometrically
    (GeometricallyIntegral.geometrically_isIntegral (f := h)) K y
  have : IsLocallyNoetherian (pullback h y) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd h y)
  have hI : IsIntegral (pullback g (pullback.fst h y)) := inferInstance
  let e : Z ≅ pullback g (pullback.fst h y) :=
    hP.isoPullback ≪≫ (pullbackRightPullbackFstIso h y g).symm
  have : Nonempty Z := ⟨e.inv (Nonempty.some inferInstance)⟩
  exact isIntegral_of_isOpenImmersion e.hom

/-- **Glue (proved).** The fibre product `A ×_K Z` of two abelian varieties over a field `K`
(Mathlib's cartesian monoidal product `A.X ⊗ Z.X` in `Over (Spec K)`, with the product group
structure `GrpObj.tensorObj.instTensorObj`) is an abelian variety in the sense of
`ZInQ.DefFaltings.AbVar`: proper and smooth (composition and base change) and geometrically
integral (`geometricallyIntegral_comp`). -/
def prodAbVar {K : Type} [Field K] (A Z : PkgI3.AbVar K) : ZInQ.DefFaltings.AbVar K :=
  haveI : IsProper (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : Smooth (A.X ⊗ Z.X).hom := by dsimp; infer_instance
  haveI : GeometricallyIntegral (A.X ⊗ Z.X).hom := by
    rw [Over.tensorObj_hom]; exact geometricallyIntegral_comp _ _
  { X := A.X ⊗ Z.X }

@[simp] lemma prodAbVar_X {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    (prodAbVar A Z).X = A.X ⊗ Z.X := rfl

/-- **Glue (proved).** `prodAbVar A Z` is the product of `A` and `Z` in the sense of
`HSyn.G0Split.IsProductOf`, via the two projections (homomorphisms for the product group law;
`(fst, snd) = 𝟙`). -/
theorem isProductOf_prodAbVar {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    HSyn.G0Split.IsProductOf (prodAbVar A Z).X A.X Z.X := by
  change HSyn.G0Split.IsProductOf (A.X ⊗ Z.X) A.X Z.X
  exact ⟨fst A.X Z.X, snd A.X Z.X, inferInstance, inferInstance, by
    rw [lift_fst_snd]; infer_instance⟩

/-- The dimension of `prodAbVar A Z` is the Krull dimension of the fibre product scheme. -/
lemma prodAbVar_dim {K : Type} [Field K] (A Z : PkgI3.AbVar K) :
    (prodAbVar A Z).dim = topologicalKrullDim (pullback (C := Scheme) A.X.hom Z.X.hom) := rfl

end G0Product

/-! ## §3. `ProductExists` from the dimension formula -/

namespace G0Product

open CategoryTheory AlgebraicGeometry Limits

/-- **Glue, proved in §4-§5 (dimension of a product over a field).** For schemes `X`, `Y` of finite
type over a field `K`, `dim (X ×_K Y) = dim X + dim Y` (Krull dimensions of the underlying
spaces, in `WithBot ℕ∞`; both sides are `⊥` if `X` or `Y` is empty). Source: Stacks Project,
Varieties, Lemma 33.20.5 (Tag 0B2L?, UNVERIFIED number); Görtz-Wedhorn, *Algebraic Geometry I*,
Prop. 5.37 (UNVERIFIED number); for integral `X`, `Y` over an algebraically closed field,
Hartshorne II Ex. 3.20 / I Prop. 1.10 style transcendence-degree argument. STANDARD. -/
def DimProductOverField : Prop :=
  ∀ (K : Type) [Field K] (X Y : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K))
    (g : Y ⟶ Spec (CommRingCat.of K)), LocallyOfFiniteType f → QuasiCompact f →
    LocallyOfFiniteType g → QuasiCompact g →
    topologicalKrullDim (pullback (C := Scheme) f g) = topologicalKrullDim X + topologicalKrullDim Y

/-- **G17, `ProductExists`, proved from `DimProductOverField`.** -/
theorem productExists_of_dimProduct (hD : DimProductOverField) : HSyn.G0Split.ProductExists := by
  intro L _ _ A Z
  refine ⟨prodAbVar A Z, isProductOf_prodAbVar A Z, ?_⟩
  rw [prodAbVar_dim]
  exact hD L A.X.left Z.X.left A.X.hom Z.X.hom inferInstance inferInstance inferInstance
    inferInstance

end G0Product


/-! ## §4. `DimProductOverField` from the ring-level formula `DimTensorFG` (proved glue) -/

namespace G0Product

open Order

/-- **Glue (proved, topology).** If open embeddings `f i : Y i → X` cover `X` and `X` has a chain
of `n + 1` irreducible closed subsets, so does some `Y i`: pull the chain back along an `f i`
whose image meets the smallest member (a nonempty open subset of an irreducible set is dense,
so the pulled-back chain stays strict). -/
theorem exists_le_dim_of_cover {X : Type*} [TopologicalSpace X] {ι : Type*} {Y : ι → Type*}
    [∀ i, TopologicalSpace (Y i)] (f : ∀ i, Y i → X) (hf : ∀ i, Topology.IsOpenEmbedding (f i))
    (hcov : ∀ x, ∃ i, x ∈ Set.range (f i)) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ i, (n : WithBot ℕ∞) ≤ topologicalKrullDim (Y i) := by
  obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hn
  obtain ⟨x, hx⟩ := (l 0).isIrreducible'.nonempty
  obtain ⟨i, y, rfl⟩ := hcov x
  have hmem : ∀ k, f i y ∈ (l k : Set X) := fun k => (l.monotone (Fin.zero_le k)) hx
  let g : Fin (l.length + 1) → TopologicalSpace.IrreducibleCloseds (Y i) := fun k =>
    ⟨f i ⁻¹' l k, ⟨⟨y, hmem k⟩, (l k).isIrreducible'.2.preimage (hf i)⟩,
      (l k).isClosed'.preimage (hf i).continuous⟩
  refine ⟨i, Order.le_krullDim_iff.mpr ⟨{ length := l.length, toFun := g, step := fun k => ?_ }, hl⟩⟩
  have hlt : l k.castSucc < l k.succ := l.step k
  have hsub : (l k.castSucc : Set X) ⊆ l k.succ := SetLike.coe_subset_coe.mpr hlt.le
  have hle : g k.castSucc ≤ g k.succ := by
    rw [← SetLike.coe_subset_coe]
    exact fun z hz => hsub hz
  refine lt_of_le_not_ge hle (fun h => hlt.not_ge ?_)
  rw [← SetLike.coe_subset_coe]
  intro z hz
  have h1 := subset_closure_inter_of_isPreirreducible_of_isOpen (l k.succ).isIrreducible'.2
    (hf i).isOpen_range ⟨f i y, hmem k.succ, y, rfl⟩ hz
  refine closure_minimal ?_ (l k.castSucc).isClosed' h1
  rintro _ ⟨hw, w, rfl⟩
  exact (SetLike.coe_subset_coe.mpr h) (show w ∈ (g k.succ : Set (Y i)) from hw)

open CategoryTheory AlgebraicGeometry Limits

/-- **Glue (proved).** The scheme version of `exists_le_dim_of_cover` for an open cover. -/
theorem Scheme.exists_le_dim_of_openCover {X : Scheme} (𝒰 : X.OpenCover) (n : ℕ)
    (hn : (n : WithBot ℕ∞) ≤ topologicalKrullDim X) :
    ∃ i, (n : WithBot ℕ∞) ≤ topologicalKrullDim (𝒰.X i) :=
  exists_le_dim_of_cover (fun i => ⇑(𝒰.f i)) (fun i => (𝒰.f i).isOpenEmbedding)
    (fun x => ⟨𝒰.idx x, 𝒰.covers x⟩) n hn

/-- An open immersion does not increase dimension. -/
theorem dim_le_of_isOpenImmersion {X Y : Scheme} (f : X ⟶ Y) [IsOpenImmersion f] :
    topologicalKrullDim X ≤ topologicalKrullDim Y :=
  f.isOpenEmbedding.isInducing.topologicalKrullDim_le

/-- `dim Spec R = dim R`. -/
theorem dim_Spec (R : CommRingCat) : topologicalKrullDim (Spec R) = ringKrullDim R :=
  PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim R

/-- Isomorphic schemes have equal dimension. -/
theorem dim_eq_of_iso {X Y : Scheme} (e : X ≅ Y) :
    topologicalKrullDim X = topologicalKrullDim Y :=
  IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph

/-- `Spec R ×_{Spec K} Spec S = Spec (R ⊗_K S)` has dimension `dim (R ⊗_K S)`. -/
theorem dim_pullback_Spec (K : Type) [Field K] (R S : CommRingCat.{0})
    (φ : CommRingCat.of K ⟶ R) (ψ : CommRingCat.of K ⟶ S) :
    letI := φ.hom.toAlgebra; letI := ψ.hom.toAlgebra
    topologicalKrullDim (pullback (C := Scheme) (Spec.map φ) (Spec.map ψ)) =
      ringKrullDim (TensorProduct K R S) := by
  let _ := φ.hom.toAlgebra; let _ := ψ.hom.toAlgebra
  exact (dim_eq_of_iso (pullbackSpecIso K R S)).trans (dim_Spec _)
/-- Order lemma in `WithBot ℕ∞`: `c ≤ d` if every natural number below `c` is below `d`. -/
theorem wb_le_of_forall_nat {c d : WithBot ℕ∞}
    (h : ∀ n : ℕ, (n : WithBot ℕ∞) ≤ c → (n : WithBot ℕ∞) ≤ d) : c ≤ d := by
  induction c using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe x =>
    induction x using ENat.recTopCoe with
    | top =>
      have : d = ⊤ := ENat.WithBot.eq_top_iff_forall_ge.mpr fun m => h m (by
        rw [← ENat.WithBot.coe_eq_natCast]; exact WithBot.coe_le_coe.mpr le_top)
      rw [this]; exact le_top
    | coe k => exact h k le_rfl

/-- Order lemma in `WithBot ℕ∞`: `a + b ≤ c` if `n + m ≤ c` whenever `n ≤ a`, `m ≤ b`. -/
theorem wb_add_le_of_forall {a b c : WithBot ℕ∞}
    (h : ∀ n m : ℕ, (n : WithBot ℕ∞) ≤ a → (m : WithBot ℕ∞) ≤ b →
      ((n + m : ℕ) : WithBot ℕ∞) ≤ c) : a + b ≤ c := by
  induction a using WithBot.recBotCoe with
  | bot => simp
  | coe x =>
  induction b using WithBot.recBotCoe with
  | bot => simp
  | coe y =>
  refine wb_le_of_forall_nat fun k hk => ?_
  rw [← WithBot.coe_add, ← ENat.WithBot.coe_eq_natCast, WithBot.coe_le_coe] at hk
  by_cases hkx : (k : ℕ∞) ≤ x
  · have := h k 0 (by rw [← ENat.WithBot.coe_eq_natCast]; exact WithBot.coe_le_coe.mpr hkx)
      (by rw [← ENat.WithBot.coe_eq_natCast]; exact WithBot.coe_le_coe.mpr (by simp))
    simpa using this
  · push Not at hkx
    obtain ⟨x0, rfl⟩ : ∃ x0 : ℕ, (x0 : ℕ∞) = x := ⟨x.toNat, ENat.natCast_toNat (ne_top_of_lt hkx)⟩
    have hx0 : x0 < k := by exact_mod_cast hkx
    have hm : ((k - x0 : ℕ) : ℕ∞) ≤ y := by
      rw [ENat.natCast_sub]
      exact tsub_le_iff_left.mpr hk
    have := h x0 (k - x0) le_rfl
      (by rw [← ENat.WithBot.coe_eq_natCast]; exact WithBot.coe_le_coe.mpr hm)
    rwa [Nat.add_sub_cancel' hx0.le] at this

/-- **Glue, proved below (`dimTensorFG`, §5): the dimension of a tensor product of finitely
generated algebras over a field.** For finitely generated algebras `R`, `S` over a field `K`,
`dim (R ⊗_K S) = dim R + dim S` (Krull dimensions in `WithBot ℕ∞`; both sides are `⊥` when
`R = 0` or `S = 0`). Source: Stacks Project, Algebra, Lemma 10.116.? (section "Dimension of
finite type algebras over fields", reprise; tag UNVERIFIED); classical via Noether
normalization: `R ⊗ S` is finite over `K[x₁..x_a, y₁..y_b]` (`a = dim R`, `b = dim S`),
injectively. STANDARD. Proved in §5 from Mathlib's Noether normalization
(`exists_integral_inj_algHom_of_fg`), `MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite`
and going up; the invariance of Krull dimension under integral injective extensions is proved
there (`ringKrullDim_eq_of_integral_injective`). -/
def DimTensorFG : Prop :=
  ∀ (K : Type) [Field K] (R S : Type) [CommRing R] [CommRing S] [Algebra K R] [Algebra K S],
    Algebra.FiniteType K R → Algebra.FiniteType K S →
    ringKrullDim (TensorProduct K R S) = ringKrullDim R + ringKrullDim S

/-- **Glue (proved).** `DimProductOverField` from `DimTensorFG`: cover `X` and `Y` by affine
opens `Spec R_i`, `Spec S_j` (Mathlib's `affineOpenCover`); `X ×_K Y` is covered by the
`Spec R_i ×_K Spec S_j = Spec (R_i ⊗_K S_j)` (`Scheme.Pullback.openCoverOfLeftRight`,
`pullbackSpecIso`); each `R_i` is of finite type over `K` because `Spec R_i → Spec K` is locally
of finite type; dimensions of covers are suprema (`Scheme.exists_le_dim_of_openCover`). The
quasi-compactness hypotheses are not used. -/
theorem dimProductOverField_of_dimTensorFG (hT : DimTensorFG) : DimProductOverField := by
  intro K _ X Y f g hf _ hg _
  let 𝒱X := X.affineOpenCover
  let 𝒱Y := Y.affineOpenCover
  let 𝒲 := Scheme.Pullback.openCoverOfLeftRight 𝒱X.openCover 𝒱Y.openCover f g
  have key : ∀ (i : 𝒱X.I₀) (j : 𝒱Y.I₀),
      topologicalKrullDim (pullback (C := Scheme) (𝒱X.f i ≫ f) (𝒱Y.f j ≫ g)) =
      ringKrullDim (𝒱X.X i) + ringKrullDim (𝒱Y.X j) := by
    intro i j
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (𝒱X.f i ≫ f)
    obtain ⟨ψ, hψ⟩ := Spec.map_surjective (𝒱Y.f j ≫ g)
    have hφ' : LocallyOfFiniteType (Spec.map φ) := by rw [hφ]; infer_instance
    have hψ' : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hφ' hψ'
    refine (dim_eq_of_iso (pullback.congrHom hφ.symm hψ.symm)).trans ?_
    refine (dim_pullback_Spec K _ _ φ ψ).trans ?_
    let _ := φ.hom.toAlgebra; let _ := ψ.hom.toAlgebra
    exact hT K _ _ hφ' hψ'
  apply le_antisymm
  · refine wb_le_of_forall_nat fun n hn => ?_
    obtain ⟨⟨i, j⟩, hij⟩ := Scheme.exists_le_dim_of_openCover 𝒲 n hn
    refine hij.trans ?_
    change topologicalKrullDim (pullback (C := Scheme) (𝒱X.f i ≫ f) (𝒱Y.f j ≫ g)) ≤ _
    refine (key i j).trans_le ?_
    have : IsOpenImmersion (𝒱X.f i) := 𝒱X.map_prop i
    have : IsOpenImmersion (𝒱Y.f j) := 𝒱Y.map_prop j
    exact add_le_add ((dim_Spec _).symm.trans_le (dim_le_of_isOpenImmersion (𝒱X.f i)))
      ((dim_Spec _).symm.trans_le (dim_le_of_isOpenImmersion (𝒱Y.f j)))
  · refine wb_add_le_of_forall fun n m hn hm => ?_
    obtain ⟨i, hi⟩ := Scheme.exists_le_dim_of_openCover 𝒱X.openCover n hn
    obtain ⟨j, hj⟩ := Scheme.exists_le_dim_of_openCover 𝒱Y.openCover m hm
    have : IsOpenImmersion (𝒲.f (i, j)) := 𝒲.map_prop (i, j)
    refine le_trans ?_ (dim_le_of_isOpenImmersion (𝒲.f (i, j)))
    change _ ≤ topologicalKrullDim (pullback (C := Scheme) (𝒱X.f i ≫ f) (𝒱Y.f j ≫ g))
    refine le_trans ?_ (key i j).ge
    rw [Nat.cast_add]
    exact add_le_add (hi.trans_eq (dim_Spec _)) (hj.trans_eq (dim_Spec _))

/-- **G17, `ProductExists`, proved from the ring-level textbook leaf `DimTensorFG`.** -/
theorem productExists_of_dimTensorFG (hT : DimTensorFG) : HSyn.G0Split.ProductExists :=
  productExists_of_dimProduct (dimProductOverField_of_dimTensorFG hT)

end G0Product

/-! ## §5. `DimTensorFG` proved from Mathlib; `ProductExists` unconditionally -/

namespace G0Product

open TensorProduct

/-- **Glue (proved, commutative algebra).** Krull dimension is invariant under an injective
integral ring map `A → R`: `≤` by incomparability (`Ideal.IsIntegral.under_lt_under`), `≥` by
lying over and going up (`Ideal.exists_ideal_over_prime_of_isIntegral`,
`Ideal.exists_ltSeries_of_hasGoingUp`). -/
theorem ringKrullDim_eq_of_integral_injective {A R : Type*} [CommRing A] [CommRing R]
    (f : A →+* R) (hinj : Function.Injective f) (hint : f.IsIntegral) :
    ringKrullDim R = ringKrullDim A := by
  let _ := f.toAlgebra
  have : Algebra.IsIntegral A R := ⟨hint⟩
  apply le_antisymm
  · refine Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap A R)) ?_
    intro p q hpq
    exact Ideal.IsIntegral.under_lt_under (R := A) (I := p.asIdeal) (J := q.asIdeal) hpq
  · refine wb_le_of_forall_nat fun n hn => ?_
    obtain ⟨l, hl⟩ := Order.le_krullDim_iff.mp hn
    obtain ⟨P, -, hP, hPo⟩ := Ideal.exists_ideal_over_prime_of_isIntegral
      (S := R) l.head.asIdeal ⊥ (by
        intro x hx
        have : algebraMap A R x = 0 := hx
        rw [show x = 0 from hinj (show f x = f 0 by rw [map_zero]; exact this)]
        exact zero_mem _)
    have : P.LiesOver l.head.asIdeal := ⟨hPo.symm⟩
    obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    exact Order.le_krullDim_iff.mpr ⟨L, hL.trans hl⟩

/-- **Glue (proved).** The tensor product `g ⊗ h` of integral algebra maps is integral. -/
theorem tensorMap_isIntegral {K A B R S : Type*} [CommRing K] [CommRing A] [CommRing B]
    [CommRing R] [CommRing S] [Algebra K A] [Algebra K B] [Algebra K R] [Algebra K S]
    (g : A →ₐ[K] R) (h : B →ₐ[K] S) (hg : g.IsIntegral) (hh : h.IsIntegral) :
    (Algebra.TensorProduct.map g h).toRingHom.IsIntegral := by
  set F := (Algebra.TensorProduct.map g h).toRingHom
  have hL : ∀ r : R, F.IsIntegralElem (r ⊗ₜ[K] (1 : S)) := by
    intro r
    have e : (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[K] S).comp g.toRingHom =
        F.comp Algebra.TensorProduct.includeLeftRingHom := by
      ext a; simp [F]
    have := (hg r).map (Algebra.TensorProduct.includeLeftRingHom : R →+* R ⊗[K] S)
    rw [e] at this
    exact this.of_comp
  have hR : ∀ s : S, F.IsIntegralElem ((1 : R) ⊗ₜ[K] s) := by
    intro s
    have e : (Algebra.TensorProduct.includeRight : S →ₐ[K] R ⊗[K] S).toRingHom.comp
        h.toRingHom = F.comp (Algebra.TensorProduct.includeRight : B →ₐ[K] A ⊗[K] B).toRingHom := by
      ext b; simp [F]
    have := (hh s).map (Algebra.TensorProduct.includeRight : S →ₐ[K] R ⊗[K] S).toRingHom
    rw [e] at this
    exact this.of_comp
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul r s =>
    have : r ⊗ₜ[K] s = (r ⊗ₜ[K] (1:S)) * ((1:R) ⊗ₜ[K] s) := by
      simp [Algebra.TensorProduct.tmul_mul_tmul]
    rw [this]; exact RingHom.IsIntegralElem.mul F (hL r) (hR s)
  | add x y hx hy => exact RingHom.IsIntegralElem.add F hx hy

/-- `dim K[X₀..X_{a-1}] = a` over a field (Mathlib). -/
theorem dim_mvPolynomial_fin (K : Type*) [Field K] (a : ℕ) :
    ringKrullDim (MvPolynomial (Fin a) K) = a := by
  simp [ringKrullDim_eq_zero_of_field]

/-- **`DimTensorFG`, proved.** Noether normalization (Mathlib's `exists_integral_inj_algHom_of_fg`)
gives injective integral `K[X₀..X_{a-1}] → R`, `K[Y₀..Y_{b-1}] → S`; their tensor product
`K[X] ⊗ K[Y] → R ⊗ S` is injective (flatness over a field) and integral, so
`dim (R ⊗ S) = dim (K[X] ⊗ K[Y]) = dim K[X][Y] = a + b = dim R + dim S`. The cases `R = 0`,
`S = 0` give `⊥ = ⊥`. -/
theorem dimTensorFG : DimTensorFG := by
  intro K _ R S _ _ _ _ hR hS
  by_cases hR0 : Subsingleton R
  · have : Subsingleton (R ⊗[K] S) := subsingleton_of_zero_eq_one (by
      rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : R) 0, zero_tmul])
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton, WithBot.bot_add]
  by_cases hS0 : Subsingleton S
  · have : Subsingleton (R ⊗[K] S) := subsingleton_of_zero_eq_one (by
      rw [Algebra.TensorProduct.one_def, Subsingleton.elim (1 : S) 0, tmul_zero])
    rw [ringKrullDim_eq_bot_of_subsingleton, ringKrullDim_eq_bot_of_subsingleton (R := S),
      WithBot.add_bot]
  rw [not_subsingleton_iff_nontrivial] at hR0 hS0
  obtain ⟨a, g, hginj, hgint⟩ := exists_integral_inj_algHom_of_fg K R
  obtain ⟨b, h, hhinj, hhint⟩ := exists_integral_inj_algHom_of_fg K S
  have dR : ringKrullDim R = a :=
    (ringKrullDim_eq_of_integral_injective g.toRingHom hginj hgint).trans (dim_mvPolynomial_fin K a)
  have dS : ringKrullDim S = b :=
    (ringKrullDim_eq_of_integral_injective h.toRingHom hhinj hhint).trans (dim_mvPolynomial_fin K b)
  have hFinj : Function.Injective (Algebra.TensorProduct.map g h) :=
    TensorProduct.map_injective_of_flat_flat g.toLinearMap h.toLinearMap hginj hhinj
  have dT : ringKrullDim (R ⊗[K] S) =
      ringKrullDim (MvPolynomial (Fin a) K ⊗[K] MvPolynomial (Fin b) K) :=
    ringKrullDim_eq_of_integral_injective _ hFinj (tensorMap_isIntegral g h hgint hhint)
  have dP : ringKrullDim (MvPolynomial (Fin a) K ⊗[K] MvPolynomial (Fin b) K) = a + b := by
    rw [ringKrullDim_eq_of_ringEquiv
      (MvPolynomial.algebraTensorAlgEquiv (σ := Fin b) K (MvPolynomial (Fin a) K)).toRingEquiv,
      MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, dim_mvPolynomial_fin]
    simp
  rw [dT, dP, dR, dS]
/-- **G17, `ProductExists` (`HSyn.G0Split.ProductExists`, verbatim statement), proved with no
hypotheses**, from Mathlib only. -/
theorem productExists : HSyn.G0Split.ProductExists :=
  productExists_of_dimTensorFG dimTensorFG

end G0Product

end
end G0ProductSec


noncomputable section

namespace HSyn

/-! ## §3″. g0-reverseisog (2026-11-13): `ReverseIsogeny` proved (task g0-reverseisog)

Appended to a verbatim copy of `scratch/g0-split/Split.lean` (wip/g0-split c20fa62b). Route A: the
textbook leaf `IsogenyQuasiInverse`. Route B (no new leaf): the bundle's R19 (Gaudron-Rémond),
H5's finiteness (`r.h5.1`) and piece 1 `DimFinite`. -/

namespace G0RevIsog

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open Topology

/-- **LEAF (Mumford; Milne).** An isogeny `φ : A → B` of abelian varieties over a field `K` (a
homomorphism of group schemes that is finite and surjective) has a quasi-inverse: an isogeny
`ψ : B → A` and an integer `n ≥ 1` (the degree of `φ`) with `ψ ∘ φ = [n]_A` and `φ ∘ ψ = [n]_B`.
Here `[n]_A` is `(𝟙 A)ⁿ` in Mathlib's group of morphisms into the group object `A`.
Sources (numbers UNVERIFIED, from memory, no network): Mumford, *Abelian Varieties*, §7 Remark after
Thm 4 / §8 (over an algebraically closed field); Milne, *Abelian Varieties* (in Cornell-Silverman,
*Arithmetic Geometry*, 1986), §8, Prop. 8.1/Remark 8.2? and Milne's course notes *Abelian
Varieties* (2008) I, Prop. 7.1 and Remark 7.2 (over an arbitrary field `k`). The proof there: `ker φ`
is a finite group scheme of order `n = deg φ`, hence killed by `n` (Deligne, commutative case), so
`[n]_A` factors through the quotient `A/ker φ ≅ B` (Mumford §7 Thm 4 / §12). -/
def IsogenyQuasiInverse : Prop :=
  ∀ (K : Type) [Field K] (A B : ZInQ.DefFaltings.AbVar K) (φ : A.X ⟶ B.X),
    ZInQ.DefFaltings.IsIsogeny φ →
    ∃ (ψ : B.X ⟶ A.X) (n : ℕ), 0 < n ∧ ZInQ.DefFaltings.IsIsogeny ψ ∧
      φ ≫ ψ = (𝟙 A.X) ^ n ∧ ψ ≫ φ = (𝟙 B.X) ^ n

/-- **Glue interface (the property `ReverseIsogeny` actually uses).** Over a number field, an
isogeny `A → B` of abelian varieties has an isogeny `B → A` in the other direction. It follows from
the textbook leaf `IsogenyQuasiInverse` (`isogenyReverseExists_of_quasiInverse`) and, in
`SplitRev.lean`, from the bundle's research leaf R19 (Gaudron-Rémond) with H5's finiteness and
`DimFinite` (`isogenyReverseExists_of_r19`). -/
def IsogenyReverseExists : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : ZInQ.DefFaltings.AbVar K) (φ : A.X ⟶ B.X),
    ZInQ.DefFaltings.IsIsogeny φ → ∃ ψ : B.X ⟶ A.X, ZInQ.DefFaltings.IsIsogeny ψ

/-- **Proved.** The leaf gives the interface. -/
theorem isogenyReverseExists_of_quasiInverse (hQ : IsogenyQuasiInverse) : IsogenyReverseExists := by
  intro K _ _ A B φ hφ
  obtain ⟨ψ, -, -, hψ, -, -⟩ := hQ K A B φ hφ
  exact ⟨ψ, hψ⟩

/-! ### Glue (proved): a closed surjective map does not lower the Krull dimension -/

section Topo

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- `closure {x}` as an irreducible closed set. -/
def closureIC (x : X) : TopologicalSpace.IrreducibleCloseds X :=
  ⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩

/-- Chains of irreducible closed sets lift along a continuous, specializing map, ending at the
closure of any point over the generic point of the last member. -/
theorem lift_series [QuasiSober Y] (f : X → Y) (hc : Continuous f) (hs : SpecializingMap f)
    (p : LTSeries (TopologicalSpace.IrreducibleCloseds Y)) :
    ∀ x : X, IsGenericPoint (f x) (p.last : Set Y) →
      ∃ q : LTSeries (TopologicalSpace.IrreducibleCloseds X), q.length = p.length ∧
        q.last = closureIC x := by
  induction p using RelSeries.inductionOn' with
  | singleton W =>
    intro x _
    exact ⟨RelSeries.singleton _ (closureIC x), rfl, rfl⟩
  | snoc p W hW ih =>
    intro x hx
    rw [RelSeries.last_snoc] at hx
    obtain ⟨w', hw'⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
    have hsub : (p.last : Set Y) ⊆ W := SetLike.coe_subset_coe.mpr hW.le
    have hspec : f x ⤳ w' := hx.specializes (hsub hw'.mem)
    obtain ⟨x', hxx', hfx'⟩ := hs hspec
    obtain ⟨q, hql, hqlast⟩ := ih x' (hfx' ▸ hw')
    have hlt : q.last < closureIC x := by
      rw [hqlast]
      refine lt_of_le_of_ne ?_ ?_
      · show closure {x'} ⊆ closure {x}
        exact specializes_iff_closure_subset.mp hxx'
      · intro heq
        have h1 : closure ({x'} : Set X) = closure {x} := congrArg SetLike.coe heq
        have h2 : x' ⤳ x := specializes_iff_closure_subset.mpr h1.symm.le
        have h3 : w' ⤳ f x := hfx' ▸ h2.map hc
        have h4 : (W : Set Y) ⊆ p.last := by
          rw [← hx.def, ← hw'.def]
          exact specializes_iff_closure_subset.mp h3
        exact hW.ne (SetLike.coe_injective (subset_antisymm hsub h4))
    refine ⟨q.snoc (closureIC x) hlt, ?_, RelSeries.last_snoc _ _ _⟩
    simp [hql]

/-- **Glue (proved).** A continuous, specializing (e.g. closed), surjective map `f : X → Y` to a
quasi-sober space does not lower the Krull dimension: `dim Y ≤ dim X`. -/
theorem topologicalKrullDim_le_of_specializing [QuasiSober Y] (f : X → Y) (hc : Continuous f)
    (hs : SpecializingMap f) (hsurj : Function.Surjective f) :
    topologicalKrullDim Y ≤ topologicalKrullDim X := by
  unfold topologicalKrullDim Order.krullDim
  refine iSup_le fun p => ?_
  obtain ⟨y, hy⟩ := QuasiSober.sober p.last.isIrreducible p.last.isClosed
  obtain ⟨x, rfl⟩ := hsurj y
  obtain ⟨q, hql, -⟩ := lift_series f hc hs p x hy
  rw [← hql]
  exact le_iSup (fun q : LTSeries (TopologicalSpace.IrreducibleCloseds X) =>
    ((q.length : ℕ∞) : WithBot ℕ∞)) q

end Topo

/-- **Glue (proved).** A finite surjective morphism of schemes does not lower the dimension of the
target: `dim Y ≤ dim X` (finite ⇒ integral ⇒ universally closed ⇒ closed, Mathlib). -/
theorem dim_le_of_finite_surjective {X Y : Scheme} (f : X ⟶ Y) [IsFinite f] [Surjective f] :
    topologicalKrullDim Y ≤ topologicalKrullDim X :=
  topologicalKrullDim_le_of_specializing f f.continuous f.isClosedMap.specializingMap f.surjective

/-- **Glue (proved).** Two isogenies in opposite directions force equal dimensions. -/
theorem dim_eq_of_isogenies {K : Type} [Field K] {A B : ZInQ.DefFaltings.AbVar K}
    (φ : A.X ⟶ B.X) (ψ : B.X ⟶ A.X) (hφ : ZInQ.DefFaltings.IsIsogeny φ)
    (hψ : ZInQ.DefFaltings.IsIsogeny ψ) : B.dim = A.dim := by
  obtain ⟨-, hφf, hφs⟩ := hφ
  obtain ⟨-, hψf, hψs⟩ := hψ
  exact le_antisymm (dim_le_of_finite_surjective φ.left) (dim_le_of_finite_surjective ψ.left)

/-- **Glue (proved): the map `P → J`.** If `(p₁, p₂) : P → A × Z` is an isomorphism of group
schemes and `(f, g) : A × Z → J` is finite and surjective, then `h = f ∘ p₁ + g ∘ p₂ : P → J` is an
isogeny. -/
theorem isogeny_of_product {L : Type} [Field L] (A J Z : PkgI3.AbVar L)
    (P : ZInQ.DefFaltings.AbVar L) (f : PkgI3.AbVar.Hom A J) (g : PkgI3.AbVar.Hom Z J)
    (hP : G0Split.IsProductOf P.X A.X Z.X)
    (hiso : PkgI3.AbVar.IsIsogenyMor (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom)) :
    ∃ h : P.X ⟶ J.X, IsMonHom h ∧ IsFinite h.left ∧ Surjective h.left := by
  obtain ⟨p₁, p₂, hp₁, hp₂, hlift⟩ := hP
  obtain ⟨hfin, hsurj⟩ := hiso
  have hm : lift p₁ p₂ ≫ (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom) =
      p₁ ≫ f.hom * p₂ ≫ g.hom := by
    simp only [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc]
  have hmon : IsMonHom (p₁ ≫ f.hom * p₂ ≫ g.hom) := by
    change IsMonHom (lift (p₁ ≫ f.hom) (p₂ ≫ g.hom) ≫ μ[J.X])
    infer_instance
  refine ⟨lift p₁ p₂ ≫ (fst A.X Z.X ≫ f.hom * snd A.X Z.X ≫ g.hom), ?_, ?_, ?_⟩
  · rw [hm]; exact hmon
  · rw [Over.comp_left]
    infer_instance
  · rw [Over.comp_left]
    infer_instance

/-- **`ReverseIsogeny` (G17 after Poincaré), proved from the interface `IsogenyReverseExists`.**
The map `h = f ∘ p₁ + g ∘ p₂ : P → J` is an isogeny (`isogeny_of_product`); the interface gives an
isogeny `ψ : J → P`; `h` and `ψ` give `dim J = dim P` (`dim_eq_of_isogenies`). -/
theorem reverseIsogeny_of_exists (hE : IsogenyReverseExists) : G0Split.ReverseIsogeny := by
  intro L _ _ A J Z P f g hP hiso
  obtain ⟨h, hh⟩ := isogeny_of_product A J Z P f g hP hiso
  replace hh : ZInQ.DefFaltings.IsIsogeny (A := P) (B := (LeafAdopt.abVarEquiv L).symm J) h := hh
  obtain ⟨ψ, hψ⟩ := hE L P ((LeafAdopt.abVarEquiv L).symm J) h hh
  exact ⟨ψ, hψ, dim_eq_of_isogenies h ψ hh hψ⟩

/-- **`ReverseIsogeny`, proved from the textbook leaf `IsogenyQuasiInverse`.** -/
theorem reverseIsogeny (hQ : IsogenyQuasiInverse) : G0Split.ReverseIsogeny :=
  reverseIsogeny_of_exists (isogenyReverseExists_of_quasiInverse hQ)


/-- **Proved (Route B, no new leaf).** Gaudron-Rémond (R19, already a field of `ResearchLeaves`)
gives isogenies in both directions between isogenous abelian varieties over a number field; its
inputs `dim A = g ∈ ℕ` and `h_F(A) = x ∈ ℝ` come from piece 1 `DimFinite` and H5's finiteness. -/
theorem isogenyReverseExists_of_r19 (r19 : ZInQ.DefFaltings.R19_GaudronRemond)
    (hfin : ZInQ.DefFaltings.StableHeightFinite) (hDimF : G0Split.DimFinite) :
    IsogenyReverseExists := by
  intro K _ _ A B φ hφ
  obtain ⟨g, hg⟩ := hDimF K (LeafAdopt.abVarEquiv K A)
  obtain ⟨-, ψ, hψ, -⟩ := r19 K A B g (ZInQ.DefFaltings.faltingsHeight A) hg
    (ZInQ.DefFaltings.faltingsHeight_coe hfin A).symm ⟨φ, hφ⟩
  exact ⟨ψ, hψ⟩

/-- **`ReverseIsogeny` from the leaf bundle and piece 1 (proved).** -/
theorem reverseIsogeny_of_leaves (r : ResearchLeaves) (hDimF : G0Split.DimFinite) :
    G0Split.ReverseIsogeny :=
  reverseIsogeny_of_exists (isogenyReverseExists_of_r19 r.r19 r.h5.1 hDimF)

end G0RevIsog

end HSyn

end




/-!
# g0-fibresimple: g0-split's missing piece 4, `FibreSimple`, from strictly smaller named Props

`HSyn.G0Split.FibreSimple` (scratch/g0-split/Split.lean, copied verbatim with everything it
depends on in `FSPrefix.lean`) is proved below (`fibreSimple_of_pieces`) from

* the leaves T27 (`PkgI3.QMDichotomyYu`, Yu 2013 Thm 1.1) and T6 (`PkgI3.HomFreeFinite`,
  Mumford §19 Thm 3), fields `t27`, `t6` of `TextbookLeaves`, and
* the textbook leaves `MulIsogeny` (Mumford §4: `[n]` is an isogeny) and `RigidityHom`
  (Mumford §4 Cor. 1: a morphism preserving `0` is a homomorphism), and
* two named glue Props: `FiniteDescends` (finiteness descends along a field extension; scheme
  theory, FS1b′) and `FibreComTrivial` (NoCM on the fibre, FS5),

with proved glue lemmas: base change along `Spec L → Spec K` is faithful
(`baseChangeFaithful_proof`, from Mathlib's fpqc descent), simplicity descends along field
extensions (`endDivisionDescent_of`, `isogenyDescends_of`, from FS1b′), simplicity is invariant under isomorphism of `k`-schemes
(`endDivisionOfSchemeIso_of_rigidity`, from `RigidityHom`), `End⁰(A)` a division algebra ⇒ nonzero endomorphisms are isogenies
(`end0Division_of_homFree`, from T6 and `MulIsogeny`), the QM structure gives `B = ℍ[ℚ,2,-3] →ₐ[ℚ] End⁰(A)`
(`qm_embeds_end0`), `B` is a division algebra (`B6_isUnit`), and the CM case of Yu's dichotomy
has a non-integral `𝒪`-centralizer (`centralizerOfMatrixEnd0_of_homFree`, from T6).

§5 records a finding: `R1fpProps`, `R2fpProps` do not determine `Φ` on closed points
(`r1fpProps_twistBy`, `r2fpProps_twistBy`), so `FibreComTrivial` (and `FibreSimple` itself) is
stronger than NoCM for the true moduli data; see docs/research/g0-fibresimple.md §2.
-/

noncomputable section

namespace G0FibreSimple

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings
open HSyn HSyn.G0Split
open scoped Quaternion TensorProduct

/-! ## §1 Proved glue: `B` is a division algebra -/

/-- `B = (2, -3)_ℚ` is a division algebra: every nonzero element is a unit (the norm form
`a² - 2b² + 3c² - 6d²` is anisotropic, `GlueDescent.aniso_rat`). -/
theorem B6_isUnit (x : ℍ[ℚ, 2, -3]) (hx : x ≠ 0) : IsUnit x := by
  set n := x.re ^ 2 - 2 * x.imI ^ 2 + 3 * x.imJ ^ 2 - 6 * x.imK ^ 2 with hn_def
  have hn : n ≠ 0 := fun h0 => by
    obtain ⟨h1, h2, h3, h4⟩ := GlueDescent.aniso_rat _ _ _ _ h0
    exact hx (QuaternionAlgebra.ext h1 h2 h3 h4)
  have hs : star x * x = algebraMap ℚ ℍ[ℚ, 2, -3] n := GlueDescent.B6_star_mul x
  have hs' : x * star x = algebraMap ℚ ℍ[ℚ, 2, -3] n := by
    rw [QuaternionAlgebra.mul_star_eq_coe]
    congr 1
    simp [QuaternionAlgebra.re_mul]
    ring
  refine ⟨⟨x, n⁻¹ • star x, ?_, ?_⟩, rfl⟩
  · rw [mul_smul_comm, hs', Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]
  · rw [smul_mul_assoc, hs, Algebra.smul_def, ← map_mul, inv_mul_cancel₀ hn, map_one]

/-- Division transported along an algebra isomorphism. -/
theorem division_of_algEquiv {D E : Type*} [Ring D] [Ring E] [Algebra ℚ D] [Algebra ℚ E]
    (e : D ≃ₐ[ℚ] E) (hE : ∀ x : E, x ≠ 0 → IsUnit x) : ∀ x : D, x ≠ 0 → IsUnit x := by
  intro x hx
  have h1 : e x ≠ 0 := by
    intro h; apply hx; rw [← e.symm_apply_apply x, h, map_zero]
  have := (hE (e x) h1).map e.symm
  rwa [e.symm_apply_apply] at this

/-! ## §2 Proved glue: a QM structure gives `B →ₐ[ℚ] End⁰(A)` -/

/-- `i ∈ 𝒪`. -/
def oi : LeafQM.O := ⟨LeafQM.ofInt ![0, 1, 0, 0], ⟨_, rfl⟩⟩
/-- `j = 2·(1+j)/2 - 1 ∈ 𝒪`. -/
def oj : LeafQM.O := ⟨LeafQM.ofInt ![-1, 0, 2, 0], ⟨_, rfl⟩⟩

theorem coe_two_O : ((2 : LeafQM.O) : LeafQM.B) = 2 := map_ofNat LeafQM.O.subtype 2
theorem coe_three_O : ((3 : LeafQM.O) : LeafQM.B) = 3 := map_ofNat LeafQM.O.subtype 3

theorem oi_mul_oi : oi * oi = 2 := by
  apply Subtype.ext
  rw [coe_two_O, Subring.coe_mul]
  ext <;> simp [oi, LeafQM.ofInt] <;> rfl

theorem oj_mul_oj : oj * oj = -3 := by
  apply Subtype.ext
  rw [Subring.coe_neg, coe_three_O, Subring.coe_mul]
  ext <;> simp [oj, LeafQM.ofInt] <;> rfl

theorem oj_mul_oi : oj * oi = -(oi * oj) := by
  apply Subtype.ext
  rw [Subring.coe_neg, Subring.coe_mul, Subring.coe_mul]
  ext <;> simp [oi, oj, LeafQM.ofInt]

/-- **Glue (proved): the QM structure gives `B ↪ End⁰(A)`.** For a QM structure
`ι : 𝒪 → End_k(A)` (`LeafQM.AV.QMStr`), the elements `1 ⊗ ι(i)`, `1 ⊗ ι(j)` of
`End⁰(A) = ℚ ⊗ End(A)` satisfy `i² = 2`, `j² = -3`, `ji = -ij`, so `B = ℍ[ℚ,2,-3]` maps to
`End⁰(A)` (`QuaternionAlgebra.Basis.liftHom`). This is Yu's hypothesis "`B` embeds in `End⁰(A)`"
(injectivity is automatic: `B` is simple and `End⁰(A) ≠ 0` when a QM structure exists). -/
def qmBasis {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    QuaternionAlgebra.Basis (PkgI3.AbVar.End0 A) (2 : ℚ) 0 (-3) :=
  let g : LeafQM.O →+* PkgI3.AbVar.End0 A :=
    (Algebra.TensorProduct.includeRight : PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A).toRingHom.comp
      q.iota
  { i := g oi
    j := g oj
    k := g oi * g oj
    i_mul_i := by
      rw [← map_mul, oi_mul_oi, map_ofNat, zero_smul, add_zero, Algebra.smul_def, _root_.mul_one,
        map_ofNat]
    j_mul_j := by
      rw [← map_mul, oj_mul_oj, map_neg, map_ofNat, Algebra.smul_def, _root_.mul_one, map_neg,
        map_ofNat]
    i_mul_j := rfl
    j_mul_i := by
      rw [← map_mul, oj_mul_oi, map_neg, map_mul, zero_smul, zero_sub] }

theorem qm_embeds_end0 {k : Type} [Field k] {A : PkgI3.AbVar k} (q : QMStr A) :
    Nonempty (ℍ[ℚ, 2, -3] →ₐ[ℚ] PkgI3.AbVar.End0 A) :=
  ⟨(qmBasis q).liftHom⟩

/-! ## §3 The named glue pieces (unproved; each true by the cited textbook argument) -/

/-- **Glue piece FS1 (descent of simplicity along a field extension; G5-G6 on the model `A/K`).**
If every nonzero endomorphism of `A_L` is an isogeny, the same holds for `A` over `K`.
*Why true* (STANDARD): `End_K(A) → End_L(A_L)` is injective (`Spec L → Spec K` is faithfully
flat and quasi-compact, so base change is faithful on morphisms, EGA IV₂ 2.7 / Stacks 023Q,
UNVERIFIED numbers), and "finite and surjective" descends along such base change (finiteness:
Stacks 02L4, UNVERIFIED; surjectivity: `A_L → A` is surjective). Glue. -/
def EndDivisionDescent : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (A : ZInQ.DefFaltings.AbVar K),
    PkgI3.EndDivision (LeafAdopt.abVarEquiv L (A.baseChange L)) →
      PkgI3.EndDivision (LeafAdopt.abVarEquiv K A)

/-- **Glue piece FS2 (rigidity: simplicity is invariant under scheme isomorphism).** If two
abelian varieties over `k` have isomorphic underlying `k`-schemes, and every nonzero endomorphism
of one is an isogeny, the same holds for the other. *Why true* (STANDARD): by rigidity
(Mumford, *Abelian varieties*, §4 Cor. 1, UNVERIFIED number) a `k`-isomorphism `φ` followed by the
translation by `-φ(0)` is an isomorphism of group schemes, and conjugation by it identifies the
endomorphism rings, preserving "finite and surjective". `FibreOver` gives only an isomorphism of
`ℚ̄`-schemes, so this step is needed. Glue. -/
def EndDivisionOfSchemeIso : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k), Nonempty (A.X ≅ B.X) →
    PkgI3.EndDivision B → PkgI3.EndDivision A

/-- **Glue piece FS3 (`End⁰(A)` a division algebra ⇒ every nonzero endomorphism is an isogeny;
Mumford §19 Cor. 2 direction "End⁰ division ⇒ simple", UNVERIFIED number).** *Why true*
(STANDARD): `End(A)` is torsion-free (Mumford §19 Thm 3), so `f ≠ 0` gives `1 ⊗ f ≠ 0` in
`End⁰(A)`; a unit there gives `g` with `g ∘ f = [n]`, `n ≠ 0`; `[n]` is an isogeny (Mumford §4),
so `ker f` is finite, `f(A)` is closed of dimension `dim A`, hence `f` is surjective, and
proper quasi-finite, hence finite. Glue (textbook). -/
def EndDivisionOfEnd0Division : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k),
    (∀ x : PkgI3.AbVar.End0 A, x ≠ 0 → IsUnit x) → PkgI3.EndDivision A

/-- **Glue piece FS4 (the CM case of Yu's dichotomy has a non-integral `𝒪`-centralizer).** If
`End⁰(A) ≅ M₂(ℚ(√d))`, `d < 0`, for an abelian variety with QM by `𝒪`, then the centralizer
`End_𝒪(A) = com q` contains a non-integer. *Why true* (STANDARD linear algebra): the image of
`B` in `M₂(k)`, `k = ℚ(√d)`, spans `M₂(k)` over `k` (`B ⊗ k` is simple of `k`-dimension 4), so
its centralizer is the centre `k`; `n√d` lies in the image of `End(A)` for some `n ≥ 1`, and
commutation and non-integrality pass from `End⁰(A)` to `End(A)` because `End(A)` is torsion-free
(Mumford §19 Thm 3). Glue. -/
def CentralizerOfMatrixEnd0 : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (q : QMStr A) (d : ℚ), d < 0 →
    Nonempty (PkgI3.AbVar.End0 A ≃ₐ[ℚ]
      Matrix (Fin 2) (Fin 2) (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d))) →
    ∃ φ ∈ com q, ∀ n : ℤ, φ ≠ (n : PkgI3.AbVar.End A)

/-- **Glue piece FS5 = G6 (NoCM, rv-h-cm §7.2, on the actual fibre object).** For `u ∉ 𝒞` and an
object `P` of `Y₃` at a `ℚ̄`-point over `J(u)`, the centralizer `End_𝒪(P.A)` is `ℤ` (the point is
not a CM point). *Why true* (rv-h-cm §7.2, model-checked, no human review): `R1fpProps`,
`R2fpProps` pin down `Y₃` and the Hauptmodul (g0-split §3); the fibre of `X₆ → P¹` over `t(u)` is
a free `W`-orbit with residue field `ℚ(i)` (Elkies' model; `GlueRepo.PR.fibre_free`, proved); a CM
order `R` has conductor prime to 6 with 2, 3 non-split (Vignéras, (Emb)); González–Rotger
Thm 5.12 (leaf R5, `LeafQM.AV.R5ptProps`) and Prop. 5.6 then force `R = ℤ[i]` (excluded since
`t(u) ≠ 1`, `F(u) ≠ 0`) or `#CM(R) = 2 < 4 = #W·x`. Unproved: the Kummer model of `X₆ → P¹`
(function-field Galois theory), the identification of an arbitrary `(Y, Φ, π)` with the bundle's
`X₆`, the class-number arithmetic. Glue, using the leaves R1, R2, R5. -/
def FibreComTrivial : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar), Φ LeafQM.AV.Qbar y = M3.mk P →
      π.val (K := LeafQM.AV.Qbar) y.left = OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u)) →
      ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A)

/-! ## §4 The piece, from T27 and FS1-FS5 -/

/-- **`FibreSimple` (g0-split's missing piece 4), from the leaf T27 and the glue FS1-FS5.** -/
theorem fibreSimple_of_pieces (t27 : PkgI3.QMDichotomyYu) (h1 : EndDivisionDescent)
    (h2 : EndDivisionOfSchemeIso) (h3 : EndDivisionOfEnd0Division)
    (h4 : CentralizerOfMatrixEnd0) (h5 : FibreComTrivial) : FibreSimple := by
  intro Y Φ π hR1 hR2 u hu K A hF
  obtain ⟨emb, y, P, hP, hval, hiso⟩ := hF
  let _ : Algebra K.K LeafQM.AV.Qbar := emb.toAlgebra
  -- G5 (T27 at `B = (2,-3)`): `End⁰(P.A) ≅ B` or `≅ M₂(ℚ(√d))`.
  have hY := PkgI3.qmDichotomy_B6 t27 LeafQM.AV.Qbar P.A P.surface B6_isUnit (qm_embeds_end0 P.q)
  -- G6 (NoCM): the second case is excluded.
  have hB : Nonempty (PkgI3.AbVar.End0 P.A ≃ₐ[ℚ] ℍ[ℚ, 2, -3]) := by
    rcases hY with hB | ⟨d, hd, hM⟩
    · exact hB
    · exfalso
      obtain ⟨φ, hφ, hne⟩ := h4 LeafQM.AV.Qbar P.A P.q d hd hM
      obtain ⟨n, hn⟩ := h5 Y Φ π hR1 hR2 u hu y P hP hval φ hφ
      exact hne n hn
  obtain ⟨e⟩ := hB
  have hPdiv : PkgI3.EndDivision P.A := h3 LeafQM.AV.Qbar P.A (division_of_algEquiv e B6_isUnit)
  have hAbar : PkgI3.EndDivision (LeafAdopt.abVarEquiv LeafQM.AV.Qbar (A.baseChange LeafQM.AV.Qbar)) :=
    h2 LeafQM.AV.Qbar _ P.A hiso hPdiv
  exact h1 K.K LeafQM.AV.Qbar A hAbar


/-! ## §4′ Proved: `CentralizerOfMatrixEnd0` from the leaf T6 (`PkgI3.HomFreeFinite`) -/

/-- **FS4 is proved from T6** (`PkgI3.HomFreeFinite`, Mumford §19 Thm 3: `Hom(A, B)` is a free
`ℤ`-module; `TextbookLeaves.t6`). Proof: the scalar matrix `√d` is central in `M₂(ℚ(√d))`, so
`c' = e⁻¹(√d)` is central in `End⁰(A)` and is not a rational scalar (`(√d)² = d < 0`); `ℚ ⊗ End(A)`
is the localization of `End(A)` at `ℤ \ {0}`, so `s • c' = 1 ⊗ φ` for some `φ ∈ End(A)`,
`s ≠ 0`; freeness makes `m ↦ 1 ⊗ m` injective, so `φ` commutes with `ι(𝒪)` and is not an
integer. -/
theorem centralizerOfMatrixEnd0_of_homFree (hHF : PkgI3.HomFreeFinite) :
    CentralizerOfMatrixEnd0 := by
  intro k _ _ A q d hd hM
  obtain ⟨e⟩ := hM
  set c' : PkgI3.AbVar.End0 A :=
    e.symm (Matrix.scalar (Fin 2) (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d))) with hc'
  have hcen : ∀ x : PkgI3.AbVar.End0 A, c' * x = x * c' := by
    intro x
    apply e.injective
    rw [map_mul, map_mul, hc', e.apply_symm_apply]
    exact (Matrix.scalar_commute _ (fun r' => Commute.all _ r') (e x)).eq
  have hnq : ∀ t : ℚ, c' ≠ algebraMap ℚ _ t := by
    intro t ht
    have h1 : Matrix.scalar (Fin 2) (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d)) =
        algebraMap ℚ _ t := by
      rw [← AlgEquiv.commutes e t, ← ht, hc', e.apply_symm_apply]
    have h2 : AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d) =
        AdjoinRoot.of (Polynomial.X ^ 2 - Polynomial.C d) t := by
      have := congrFun (congrFun h1 0) 0
      simpa [Matrix.scalar_apply, Matrix.algebraMap_eq_diagonal, AdjoinRoot.algebraMap_eq]
        using this
    have hdeg : (Polynomial.X ^ 2 - Polynomial.C d : Polynomial ℚ).degree ≠ 0 := by
      rw [Polynomial.degree_X_pow_sub_C (by norm_num)]; norm_num
    have h3 := AdjoinRoot.eval₂_root (Polynomial.X ^ 2 - Polynomial.C d)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C] at h3
    rw [h2, ← map_pow, ← map_sub] at h3
    have h4 : t ^ 2 - d = 0 :=
      (AdjoinRoot.of.injective_of_degree_ne_zero hdeg) (h3.trans (map_zero _).symm)
    nlinarith [sq_nonneg t]
  have hfree : Module.Free ℤ (PkgI3.AbVar.End A) := (hHF k A A).1
  let f := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) f :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ f).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  obtain ⟨⟨φ, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) f c'
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] φ = (s : ℤ) • c' := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) f).mp hm
    rw [Submonoid.smul_def] at hs'
    exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')
  refine ⟨φ, ?_, ?_⟩
  · rw [com, Subring.mem_centralizer_iff]
    rintro _ ⟨a, rfl⟩
    have key : (1 : ℚ) ⊗ₜ[ℤ] (q.iota a * φ - φ * q.iota a) = 0 := by
      have e1 : ∀ x y : PkgI3.AbVar.End A,
          (1 : ℚ) ⊗ₜ[ℤ] (x * y) = ((1 : ℚ) ⊗ₜ[ℤ] x) * ((1 : ℚ) ⊗ₜ[ℤ] y) := by
        intro x y; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
      rw [TensorProduct.tmul_sub, e1, e1, hs', mul_smul_comm, smul_mul_assoc, ← smul_sub,
        hcen, sub_self, smul_zero]
    exact sub_eq_zero.mp (hinj _ key)
  · intro n hn
    apply hnq ((n : ℚ) / (s : ℤ))
    have h1 : algebraMap ℚ (PkgI3.AbVar.End0 A) ((s : ℤ) : ℚ) * c' =
        algebraMap ℚ (PkgI3.AbVar.End0 A) (n : ℚ) := by
      rw [map_intCast, map_intCast, ← zsmul_eq_mul, ← hs', hn]
      exact map_intCast (Algebra.TensorProduct.includeRight :
        PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) n
    have hs1 : ((s : ℤ) : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hs0
    calc c' = algebraMap ℚ (PkgI3.AbVar.End0 A) (((s : ℤ) : ℚ)⁻¹) *
          (algebraMap ℚ (PkgI3.AbVar.End0 A) ((s : ℤ) : ℚ) * c') := by
          rw [← _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ hs1, map_one, _root_.one_mul]
      _ = algebraMap ℚ _ ((n : ℚ) / (s : ℤ)) := by
          rw [h1, ← map_mul, div_eq_inv_mul]

/-- `FibreSimple` from the two leaves T6, T27 and the four remaining glue pieces. -/
theorem fibreSimple_of_pieces' (t6 : PkgI3.HomFreeFinite) (t27 : PkgI3.QMDichotomyYu)
    (h1 : EndDivisionDescent) (h2 : EndDivisionOfSchemeIso) (h3 : EndDivisionOfEnd0Division)
    (h5 : FibreComTrivial) : FibreSimple :=
  fibreSimple_of_pieces t27 h1 h2 h3 (centralizerOfMatrixEnd0_of_homFree t6) h5


/-! ## §4″ FS3 from T6 and the textbook leaf `MulIsogeny` -/

/-- **Textbook leaf (Mumford, *Abelian varieties*, §4, Application 2 / §6, over an algebraically
closed field; Milne, *Abelian varieties* (Cornell–Silverman 1986), Thm 8.2, over any field;
locators UNVERIFIED): multiplication by `n ≠ 0` is an isogeny** (finite and surjective, of degree
`n^{2g}`), stated in characteristic `0`. The degree is dropped, so this is a consequence of the
published statement. -/
def MulIsogeny : Prop :=
  ∀ (k : Type) [Field k] [CharZero k] (A : PkgI3.AbVar k) (n : ℤ), n ≠ 0 →
    PkgI3.AbVar.IsIsogenyMor ((n : PkgI3.AbVar.End A).hom)

/-- **FS3 is proved from T6 (`PkgI3.HomFreeFinite`) and `MulIsogeny`.** If `1 ⊗ f` is a unit of
`End⁰(A)` with inverse `u⁻¹`, clearing denominators gives `g` and `s ≠ 0` with `g ∘ f = [s]` and
`f ∘ g = [s]` (freeness of `End(A)` makes `m ↦ 1 ⊗ m` injective). `[s]` is finite and surjective,
so `f` is finite (Mathlib `IsFinite.of_comp`, `g` separated since `A` is proper) and surjective
(`Surjective.of_comp`). -/
theorem end0Division_of_homFree (hHF : PkgI3.HomFreeFinite) (hMul : MulIsogeny) :
    EndDivisionOfEnd0Division := by
  intro k _ _ A hdiv f hf
  have hfree : Module.Free ℤ (PkgI3.AbVar.End A) := (hHF k A A).1
  let F := TensorProduct.mk ℤ ℚ (PkgI3.AbVar.End A) 1
  have hloc : IsLocalizedModule (nonZeroDivisors ℤ) F :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors ℤ) ℚ F).mpr
      (TensorProduct.isBaseChange (R := ℤ) (M := PkgI3.AbVar.End A) (S := ℚ))
  have hinj : ∀ m : PkgI3.AbVar.End A, (1 : ℚ) ⊗ₜ[ℤ] m = 0 → m = 0 := by
    intro m hm
    obtain ⟨s', hs'⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors ℤ) F).mp hm
    rw [Submonoid.smul_def] at hs'
    exact (smul_eq_zero.mp hs').resolve_left (nonZeroDivisors.coe_ne_zero s')
  have e1 : ∀ x y : PkgI3.AbVar.End A,
      (1 : ℚ) ⊗ₜ[ℤ] (x * y) = ((1 : ℚ) ⊗ₜ[ℤ] x) * ((1 : ℚ) ⊗ₜ[ℤ] y) := by
    intro x y; rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one]
  have hx : (1 : ℚ) ⊗ₜ[ℤ] f ≠ 0 := fun h => hf (hinj f h)
  obtain ⟨u, hu⟩ := hdiv _ hx
  obtain ⟨⟨g, s⟩, hs⟩ := IsLocalizedModule.surj (nonZeroDivisors ℤ) F (↑u⁻¹ : PkgI3.AbVar.End0 A)
  have hs' : (1 : ℚ) ⊗ₜ[ℤ] g = (s : ℤ) • (↑u⁻¹ : PkgI3.AbVar.End0 A) := by
    rw [Submonoid.smul_def] at hs; exact hs.symm
  have hs0 : (s : ℤ) ≠ 0 := nonZeroDivisors.coe_ne_zero s
  have hcast : (1 : ℚ) ⊗ₜ[ℤ] ((s : ℤ) : PkgI3.AbVar.End A) = ((s : ℤ) : PkgI3.AbVar.End0 A) :=
    map_intCast (Algebra.TensorProduct.includeRight :
      PkgI3.AbVar.End A →ₐ[ℤ] ℚ ⊗[ℤ] PkgI3.AbVar.End A) _
  have hgf : g * f = ((s : ℤ) : PkgI3.AbVar.End A) := by
    apply sub_eq_zero.mp; apply hinj
    rw [TensorProduct.tmul_sub, e1, hs', ← hu, smul_mul_assoc, Units.inv_mul, hcast,
      zsmul_eq_mul, _root_.mul_one, sub_self]
  have hfg : f * g = ((s : ℤ) : PkgI3.AbVar.End A) := by
    apply sub_eq_zero.mp; apply hinj
    rw [TensorProduct.tmul_sub, e1, hs', ← hu, mul_smul_comm, Units.mul_inv, hcast,
      zsmul_eq_mul, _root_.mul_one, sub_self]
  obtain ⟨hfin, hsurj⟩ := hMul k A (s : ℤ) hs0
  rw [← hgf] at hfin
  rw [← hfg] at hsurj
  change IsFinite (f.hom ≫ g.hom).left at hfin
  change Surjective (g.hom ≫ f.hom).left at hsurj
  rw [Over.comp_left] at hfin hsurj
  have hsep : IsSeparated (g.hom.left ≫ A.X.hom) := by rw [Over.w g.hom]; infer_instance
  have : IsSeparated g.hom.left := IsSeparated.of_comp (f := g.hom.left) (g := A.X.hom)
  exact ⟨IsFinite.of_comp f.hom.left g.hom.left, Surjective.of_comp g.hom.left f.hom.left⟩

/-- `FibreSimple` from the leaves T6, T27, `MulIsogeny` and the three glue pieces FS1, FS2, FS5. -/
theorem fibreSimple_of_pieces'' (t6 : PkgI3.HomFreeFinite) (t27 : PkgI3.QMDichotomyYu)
    (hMul : MulIsogeny) (h1 : EndDivisionDescent) (h2 : EndDivisionOfSchemeIso)
    (h5 : FibreComTrivial) : FibreSimple :=
  fibreSimple_of_pieces' t6 t27 h1 h2 (end0Division_of_homFree t6 hMul) h5


/-! ## §4‴ FS2 from the textbook leaf `RigidityHom` -/

/-- **Textbook leaf (rigidity; Mumford, *Abelian varieties*, §4 Cor. 1; Milne, *Abelian
varieties* (Cornell–Silverman 1986), Cor. 2.2, over any field; locators UNVERIFIED).** A morphism
of `k`-schemes between abelian varieties that sends the identity to the identity is a
homomorphism. -/
def RigidityHom : Prop :=
  ∀ (k : Type) [Field k] (A B : PkgI3.AbVar k) (h : A.X ⟶ B.X), η[A.X] ≫ h = η[B.X] → IsMonHom h

/-- **FS2 is proved from `RigidityHom`.** For a `k`-isomorphism `e : A.X ≅ B.X`, put
`b = e(0)`, `ψ = e - b` and `ψ' = e⁻¹ ∘ (· + b)` (translations, in the group of morphisms into
the group object). They are inverse, preserve the identity, hence are homomorphisms by rigidity;
conjugation by them carries nonzero endomorphisms of `A` to nonzero endomorphisms of `B`, and
"finite and surjective" back. -/
theorem endDivisionOfSchemeIso_of_rigidity (hR : RigidityHom) : EndDivisionOfSchemeIso := by
  intro k _ A B ⟨e⟩ hB
  set b : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ B.X := η[A.X] ≫ e.hom with hb
  set ψ : A.X ⟶ B.X := e.hom * (toUnit A.X ≫ b⁻¹) with hψdef
  set ψ' : B.X ⟶ A.X := (𝟙 B.X * (toUnit B.X ≫ b)) ≫ e.inv with hψ'def
  have hu : η[A.X] ≫ toUnit A.X = 𝟙 _ := toUnit_unique _ _
  have hu' : η[B.X] ≫ toUnit B.X = 𝟙 _ := toUnit_unique _ _
  have h1 : ψ ≫ ψ' = 𝟙 A.X := by
    rw [hψ'def, ← Category.assoc, MonObj.comp_mul, Category.comp_id,
      ← Category.assoc, toUnit_unique (ψ ≫ toUnit B.X) (toUnit A.X), hψdef, _root_.mul_assoc,
      ← MonObj.comp_mul, inv_mul_cancel, MonObj.comp_one, _root_.mul_one, e.hom_inv_id]
  have h2 : ψ' ≫ ψ = 𝟙 B.X := by
    have k1 : ψ' ≫ e.hom = 𝟙 B.X * (toUnit B.X ≫ b) := by
      rw [hψ'def, Category.assoc, e.inv_hom_id, Category.comp_id]
    have k2 : ψ' ≫ toUnit A.X ≫ b⁻¹ = toUnit B.X ≫ b⁻¹ := by
      rw [← Category.assoc, toUnit_unique (ψ' ≫ toUnit A.X) (toUnit B.X)]
    rw [hψdef, MonObj.comp_mul, k1, k2, _root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel,
      MonObj.comp_one, _root_.mul_one]
  have h3 : η[A.X] ≫ ψ = η[B.X] := by
    rw [hψdef, MonObj.comp_mul, ← Category.assoc, hu, Category.id_comp, ← hb, mul_inv_cancel,
      MonObj.one_eq_one]
  have h4 : η[B.X] ≫ ψ' = η[A.X] := by
    rw [hψ'def, ← Category.assoc, MonObj.comp_mul, Category.comp_id, ← Category.assoc, hu',
      Category.id_comp, MonObj.one_eq_one, _root_.one_mul, hb, Category.assoc, e.hom_inv_id,
      Category.comp_id]
  have hψ : IsMonHom ψ := hR k A B ψ h3
  have hψ' : IsMonHom ψ' := hR k B A ψ' h4
  intro f hf
  let g : PkgI3.AbVar.End B := PkgI3.AbVar.Hom.mk' (ψ' ≫ f.hom ≫ ψ)
  have hfg : f.hom = ψ ≫ g.hom ≫ ψ' := by
    change f.hom = ψ ≫ (ψ' ≫ f.hom ≫ ψ) ≫ ψ'
    simp only [Category.assoc, h1, Category.comp_id]
    rw [← Category.assoc, h1, Category.id_comp]
  have hg0 : g ≠ 0 := by
    intro hg
    apply hf
    apply PkgI3.AbVar.Hom.ext'
    rw [hfg, hg, PkgI3.AbVar.Hom.hom_zero, MonObj.one_comp, MonObj.comp_one,
      PkgI3.AbVar.Hom.hom_zero]
  obtain ⟨hfin, hsurj⟩ := hB g hg0
  have : IsIso ψ.left := ⟨ψ'.left, by rw [← Over.comp_left, h1]; rfl,
    by rw [← Over.comp_left, h2]; rfl⟩
  have : IsIso ψ'.left := ⟨ψ.left, by rw [← Over.comp_left, h2]; rfl,
    by rw [← Over.comp_left, h1]; rfl⟩
  rw [hfg]
  show IsFinite (ψ ≫ g.hom ≫ ψ').left ∧ Surjective (ψ ≫ g.hom ≫ ψ').left
  rw [Over.comp_left, Over.comp_left]
  exact ⟨inferInstance, inferInstance⟩


/-! ## §4⁗ FS1 from two scheme-theoretic descent statements -/

/-- **Glue piece FS1a (base change along a field extension is faithful).** For `L/K` a field
extension, `Over.pullback (Spec L → Spec K)` is faithful. *Why true* (STANDARD): `X_L → X` is
faithfully flat and quasi-compact, hence an epimorphism of schemes (Mathlib's
`AlgebraicGeometry.effectiveEpi_base_of_flat` covers the base map; the general statement is EGA
IV₂ 2.7 / Stacks 023Q, UNVERIFIED numbers). Glue (scheme theory). -/
def BaseChangeFaithful : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (X Y : Over (Spec (CommRingCat.of K)))
    (g h : X ⟶ Y),
    (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g =
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map h → g = h

/-- **Glue piece FS1b ("finite and surjective" descends along a field extension).** *Why true*
(STANDARD): finiteness is fpqc local on the target (EGA IV₂ 2.7.1, UNVERIFIED number) and the
base change square of `g` along the surjection `Y_L → Y` is a pullback; surjectivity descends
because `X_L → X` is surjective. Mathlib has the fpqc descent machinery
(`Morphisms/FlatDescent.lean`) but not this instance. Glue (scheme theory). -/
def IsogenyDescends : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (X Y : Over (Spec (CommRingCat.of K)))
    (g : X ⟶ Y),
    PkgI3.AbVar.IsIsogenyMor
        ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g) →
      PkgI3.AbVar.IsIsogenyMor g

open scoped CategoryTheory.Obj in
/-- **FS1 is proved from FS1a and FS1b.** A nonzero `f ∈ End_K(A)` base-changes to
`f_L = F(f)`, a homomorphism for the transported group structure; `f_L ≠ 0` because `F` is
faithful and `F(1) = 1` (`Functor.map_one`); `f_L` is an isogeny by hypothesis, and this
descends. -/
theorem endDivisionDescent_of (hFa : BaseChangeFaithful) (hDe : IsogenyDescends) :
    EndDivisionDescent := by
  intro K L _ _ _ A hL f hf
  let F := Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))
  have hmon : @IsMonHom _ _ _ _ _ (LeafAdopt.abVarEquiv L (A.baseChange L)).grp.toMonObj
      (LeafAdopt.abVarEquiv L (A.baseChange L)).grp.toMonObj (F.map f.hom) :=
    Functor.map.instIsMonHom (F := F) (f := f.hom)
  let fL : PkgI3.AbVar.End (LeafAdopt.abVarEquiv L (A.baseChange L)) :=
    @PkgI3.AbVar.Hom.mk' _ _ _ _ (F.map f.hom) hmon
  have hfL : fL ≠ 0 := by
    intro h
    apply hf
    apply PkgI3.AbVar.Hom.ext'
    apply hFa K L _ _ f.hom 1
    have h1 : F.map f.hom = (0 : PkgI3.AbVar.End (LeafAdopt.abVarEquiv L (A.baseChange L))).hom :=
      congrArg PkgI3.AbVar.Hom.hom h
    have h2 : F.map (1 : A.X ⟶ A.X) =
        (0 : PkgI3.AbVar.End (LeafAdopt.abVarEquiv L (A.baseChange L))).hom :=
      Functor.map_one F
    exact h1.trans h2.symm
  exact hDe K L _ _ f.hom (hL fL hfL :)


/-- `Spec L → Spec K` is flat and surjective (`L/K` is faithfully flat). -/
theorem specMap_flat_surjective (K L : Type) [Field K] [Field L] [Algebra K L] :
    Flat (Spec.map (CommRingCat.ofHom (algebraMap K L))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap K L))) := by
  apply (flat_and_surjective_SpecMap_iff _).mpr
  rw [CommRingCat.hom_ofHom, RingHom.faithfullyFlat_algebraMap_iff]
  infer_instance

/-- **FS1a is proved (Mathlib's fpqc descent):** `Over.pullback` along a surjective, flat,
quasi-compact morphism is faithful (`AlgebraicGeometry` instance in
`Morphisms/FlatDescent.lean`), and `Spec L → Spec K` is one. -/
theorem baseChangeFaithful_proof : BaseChangeFaithful := by
  intro K L _ _ _ X Y g h hgh
  obtain ⟨h1, h2⟩ := specMap_flat_surjective K L
  exact (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map_injective hgh

/-- **Glue piece FS1b′ (finiteness descends along a field extension).** *Why true* (STANDARD):
finiteness is fpqc local on the target (EGA IV₂ 2.7.1, UNVERIFIED number). Mathlib v4.35 has
`RingHom.Finite.codescendsAlong_faithfullyFlat` and `HasAffineProperty.descendsAlong_of_affineAnd`,
but not the descent of `IsAffineHom` that the latter needs. Glue (scheme theory). -/
def FiniteDescends : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L] (X Y : Over (Spec (CommRingCat.of K)))
    (g : X ⟶ Y),
    IsFinite ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map g).left →
      IsFinite g.left

/-- **FS1b from FS1b′:** surjectivity descends (`X_L → X` is surjective). -/
theorem isogenyDescends_of (hFin : FiniteDescends) : IsogenyDescends := by
  intro K L _ _ _ X Y g ⟨hf, hs⟩
  refine ⟨hFin K L X Y g hf, ?_⟩
  obtain ⟨h1, h2⟩ := specMap_flat_surjective K L
  set φ := Spec.map (CommRingCat.ofHom (algebraMap K L))
  have hsq : ((Over.pullback φ).map g).left ≫ pullback.fst Y.hom φ =
      pullback.fst X.hom φ ≫ g.left := by
    simp
  have : Surjective (pullback.fst X.hom φ ≫ g.left) := by
    rw [← hsq]; infer_instance
  exact Surjective.of_comp (pullback.fst X.hom φ) g.left

/-- The unproved glue pieces as one bundle: FS1b′ (finiteness descends along a field
extension; scheme theory) and FS5 (NoCM on the fibre). FS1 is proved from FS1a (proved, Mathlib)
and FS1b (from FS1b′); FS2 from `RigidityHom`; FS3 from T6 and `MulIsogeny`; FS4 from T6. -/
structure FibreSimplePieces : Prop where
  finiteDescends : FiniteDescends
  comTrivial : FibreComTrivial

/-- **`FibreSimple` from the leaf bundle** (`TextbookLeaves.t6` = Mumford §19 Thm 3,
`TextbookLeaves.t27` = Yu Thm 1.1), **the textbook leaves `MulIsogeny` (Mumford §4) and
`RigidityHom` (Mumford §4 Cor. 1), and the glue pieces FS1b′ (finiteness descends along field
extensions) and FS5 (NoCM on the fibre).** -/
theorem fibreSimple_of_leaves (t : HSyn.TextbookLeaves) (hMul : MulIsogeny) (hRig : RigidityHom)
    (p : FibreSimplePieces) : FibreSimple :=
  fibreSimple_of_pieces'' t.t6 t.t27 hMul
    (endDivisionDescent_of baseChangeFaithful_proof (isogenyDescends_of p.finiteDescends))
    (endDivisionOfSchemeIso_of_rigidity hRig) p.comTrivial

/-! ## §5 Finding: `R1fpProps`, `R2fpProps` do not determine `Φ` on closed points

`FibreSimple` (and `FibreComTrivial`) quantify over every `(Y, Φ, π)` with `R1fpProps`,
`R2fpProps`. Composing `Φ` with any natural automorphism `σ` of the field-point functor of `Y`
that permutes the `π`-fibres and fixes the three CM fibres gives new data satisfying both clause
lists (`r1fpProps_twistBy`, `r2fpProps_twistBy`, proved). For such `σ`, the object attached to
a point `y` over `J(u)` is the object of the point `σ y`, which lies over `π(σ y)`. -/

/-- A natural automorphism of the field-valued points of `Y` (natural in `ℚ`-embeddings of
fields). Example: a bijection of closed points of `Y` together with `ℚ`-isomorphisms of their
residue fields (a `K`-point is a point `p` with `κ(p) → K`). -/
structure PtAuto (Y : Over (Spec (CommRingCat.of ℚ))) where
  σ : ∀ (K : Type) [Field K] [Algebra ℚ K], (fieldPt K ⟶ Y) ≃ (fieldPt K ⟶ Y)
  natural : ∀ (K L : Type) [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L] (f : K →ₐ[ℚ] L)
    (y : fieldPt K ⟶ Y), σ L (fieldMap f ≫ y) = fieldMap f ≫ σ K y

/-- `Φ ∘ σ`. -/
def twistBy {Y : Over (Spec (CommRingCat.of ℚ))} (Φ : PtEquiv Y) (s : PtAuto Y) : PtEquiv Y :=
  fun K _ _ => (s.σ K).trans (Φ K)

/-- **Proved: `R1fpProps` is invariant under `Φ ↦ Φ ∘ σ`.** -/
theorem r1fpProps_twistBy {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    (h1 : R1fpProps Y Φ) (s : PtAuto Y) : R1fpProps Y (twistBy Φ s) := by
  obtain ⟨hp, hs, hq, hnat⟩ := h1
  refine ⟨hp, hs, hq, ?_⟩
  intro K L _ _ _ _ f y P hP
  obtain ⟨Q, hQ, hb⟩ := hnat K L f (s.σ K y) P hP
  refine ⟨Q, ?_, hb⟩
  change Φ L (s.σ L (fieldMap f ≫ y)) = M3.mk Q
  rw [s.natural]
  exact hQ

/-- **Proved: `R2fpProps` is invariant under `Φ ↦ Φ ∘ σ`** when `σ` permutes the `π`-fibres of
`ℚ̄`-points and fixes the fibres over `0, ∞, −16/27` (no other condition). -/
theorem r2fpProps_twistBy {Y : Over (Spec (CommRingCat.of ℚ))} {Φ : PtEquiv Y}
    {π : ToP1 Y.left} (h2 : R2fpProps Y Φ π) (s : PtAuto Y)
    (hfib : ∀ y y' : fieldPt LeafQM.AV.Qbar ⟶ Y,
      π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y).left =
          π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y').left ↔
        π.val (K := LeafQM.AV.Qbar) y.left = π.val (K := LeafQM.AV.Qbar) y'.left)
    (hcm : ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (c : OnePoint LeafQM.AV.Qbar),
      (c = OnePoint.some 0 ∨ c = OnePoint.infty ∨ c = OnePoint.some (-16 / 27)) →
      π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y).left = c →
        π.val (K := LeafQM.AV.Qbar) y.left = c) :
    R2fpProps Y (twistBy Φ s) π := by
  intro y y' P Q hP hQ
  obtain ⟨hf, h4, h3, h24⟩ := h2 (s.σ LeafQM.AV.Qbar y) (s.σ LeafQM.AV.Qbar y') P Q hP hQ
  refine ⟨(hfib y y').symm.trans hf, fun c => hcm y _ (Or.inl rfl) (h4 c),
    fun c => hcm y _ (Or.inr (Or.inl rfl)) (h3 c), fun c => hcm y _ (Or.inr (Or.inr rfl)) (h24 c)⟩

/-- **Proved: what `FibreComTrivial` asserts about the given data.** Applied to `(Y, Φ ∘ σ, π)`,
it asserts that the object at `σ y` has trivial `𝒪`-centralizer for every `y` over `J(u)` and
every fibre-permuting `σ` fixing the CM fibres: that is, NoCM over every rational value `t₂`
whose fibre `σ` can exchange with the fibre over `J(u)`. -/
theorem fibreComTrivial_twisted (h5 : FibreComTrivial)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left)
    (h1 : R1fpProps Y Φ) (h2 : R2fpProps Y Φ π) (s : PtAuto Y)
    (hfib : ∀ y y' : fieldPt LeafQM.AV.Qbar ⟶ Y,
      π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y).left =
          π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y').left ↔
        π.val (K := LeafQM.AV.Qbar) y.left = π.val (K := LeafQM.AV.Qbar) y'.left)
    (hcm : ∀ (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (c : OnePoint LeafQM.AV.Qbar),
      (c = OnePoint.some 0 ∨ c = OnePoint.infty ∨ c = OnePoint.some (-16 / 27)) →
      π.val (K := LeafQM.AV.Qbar) (s.σ LeafQM.AV.Qbar y).left = c →
        π.val (K := LeafQM.AV.Qbar) y.left = c)
    (u : ℚ) (hu : u ∉ contactSet) (y : fieldPt LeafQM.AV.Qbar ⟶ Y) (P : QML3 LeafQM.AV.Qbar)
    (hP : Φ LeafQM.AV.Qbar (s.σ LeafQM.AV.Qbar y) = M3.mk P)
    (hy : π.val (K := LeafQM.AV.Qbar) y.left =
      OnePoint.some (algebraMap ℚ LeafQM.AV.Qbar (Jmap u))) :
    ∀ φ ∈ com P.q, ∃ n : ℤ, φ = (n : PkgI3.AbVar.End P.A) :=
  h5 Y (twistBy Φ s) π (r1fpProps_twistBy h1 s) (r2fpProps_twistBy h2 s hfib hcm) u hu y P hP hy

end G0FibreSimple

end


section G0StableBCSec
noncomputable section

/-! ## g0-stablebc: the piece `StableHeightBaseChange` -/

namespace G0StableBC

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField ZInQ.DefFaltings

-- The following definition (docstring and body) is copied verbatim from scratch/g0-split/Split.lean.
/-- **Missing piece 6 (definition-level glue; used by E3-E4).** The *stable* Faltings
height is invariant under finite extension of the number field (Faltings 1983 §1; Deligne,
Sém. Bourbaki 616). For def-faltings' infimum this needs semistable reduction and the Néron
models of H5 (`NeronModelMinimal`); it is a property of the definition, not a literature leaf. -/
def StableHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (L : Type) [Field L] [NumberField L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K),
    stableFaltingsHeight (A.baseChange L) = stableFaltingsHeight A

/-! ### Glue statements copied from `scratch/h5-neron/Reduction.lean` (verbatim, over this file's
`AbVar`; h5-neron states them over the kernel's `PkgI3.AbVar`, the same structure) -/

section H5NeronCopies

variable {K : Type} [Field K] {A : AbVar K}

/-- `𝒢'` (over `𝓞_{L'}`) is the base change of `𝒢` (over `𝓞_L`) along `𝓞_L → 𝓞_{L'}`, as a group
scheme: an isomorphism of group objects `𝒢' ≅ 𝒢 ×_{𝓞_L} 𝓞_{L'}`. (The identifications with
`A_{L'}` are not compared; the height does not use them.) (copied from h5-neron) -/
def IsBaseChangeOf {L L' : Type} [Field L] [NumberField L] [Algebra K L] [Field L']
    [NumberField L'] [Algebra K L'] [Algebra L L'] (𝒢' : GroupModel A L') (𝒢 : GroupModel A L) :
    Prop :=
  letI : GrpObj ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G) := Functor.grpObjObj
  ∃ e : 𝒢'.G ≅ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G,
    IsMonHom e.hom

end H5NeronCopies

/-- **Glue H4a** (h5-neron). The height of a fixed smooth model is invariant under base change:
`ω_{𝒢_{L'}} = ω_𝒢 ⊗ 𝓞_{L'}` (flat base change of the conormal sheaf), the Arakelov degree is
multiplied by `[L':L]`, and each `τ' : L' → ℂ` restricts to `τ = τ'|_L` with the same
uniformization. (copied from h5-neron) -/
def ModelHeightBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height = 𝒢.height

/-- **Glue H4a, the inequality half (used here).** `h(𝒢_{L'}) ≤ h(𝒢)` for a group model `𝒢` and
a base change `𝒢'` of it. Implied by `ModelHeightBaseChange` (`modelHeightBaseChangeLE`
below). Same justification (h5-neron §2): `ω` of a smooth model commutes with base change, the
Arakelov degree is multiplied by `[L':L]`, and `𝒢'(ℂ)_{τ'} = 𝒢(ℂ)_{τ'|_L}`. -/
def ModelHeightBaseChangeLE : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → 𝒢'.height ≤ 𝒢.height

theorem modelHeightBaseChangeLE (h : ModelHeightBaseChange) : ModelHeightBaseChangeLE :=
  fun K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 => (h K A L L' 𝒢 𝒢' h𝒢).le

/-- **Glue H4b** (h5-neron). A group model base-changes to a group model (smoothness,
separatedness and quasi-compactness are stable under base change; the group structure is
transported by the monoidal functor `Over.pullback`; the generic fibre is `A_L ×_L L' ≅ A_{L'}` by
pullback pasting). (copied from h5-neron) -/
def GroupModelBaseChangeExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L), ∃ 𝒢' : GroupModel A L', IsBaseChangeOf 𝒢' 𝒢

/-- **The compositum** (proved in h5-neron; proof copied). Two number fields `L, L₀` over a
number field `K` embed `K`-linearly in a common number field `L'`. -/
theorem compositum (K : Type) [Field K] [NumberField K] (L L₀ : Type) [Field L] [NumberField L]
    [Algebra K L] [Field L₀] [NumberField L₀] [Algebra K L₀] :
    ∃ (L' : Type) (_ : Field L') (_ : NumberField L') (_ : Algebra K L') (_ : Algebra L L')
      (_ : Algebra L₀ L'), IsScalarTower K L L' ∧ IsScalarTower K L₀ L' := by
  let Ω := AlgebraicClosure K
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  haveI : Module.Finite K L₀ := Module.Finite.of_restrictScalars_finite ℚ K L₀
  let eL : L →ₐ[K] Ω := IsAlgClosed.lift
  let eL₀ : L₀ →ₐ[K] Ω := IsAlgClosed.lift
  let E : IntermediateField K Ω := eL.fieldRange ⊔ eL₀.fieldRange
  haveI : FiniteDimensional K eL.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField eL).toLinearEquiv
  haveI : FiniteDimensional K eL₀.fieldRange :=
    LinearEquiv.finiteDimensional (AlgEquiv.ofInjectiveField eL₀).toLinearEquiv
  haveI : FiniteDimensional K E := IntermediateField.finiteDimensional_sup _ _
  haveI : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  haveI : FiniteDimensional ℚ E := Module.Finite.trans K E
  haveI : NumberField E := ⟨⟩
  let f : L →ₐ[K] E := (IntermediateField.inclusion le_sup_left).comp
    (AlgEquiv.ofInjectiveField eL).toAlgHom
  let f₀ : L₀ →ₐ[K] E := (IntermediateField.inclusion le_sup_right).comp
    (AlgEquiv.ofInjectiveField eL₀).toAlgHom
  letI : Algebra L E := f.toRingHom.toAlgebra
  letI : Algebra L₀ E := f₀.toRingHom.toAlgebra
  refine ⟨E, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · exact IsScalarTower.of_algebraMap_eq fun x => (f.commutes x).symm
  · exact IsScalarTower.of_algebraMap_eq fun x => (f₀.commutes x).symm

/-! ### New glue: pullback pasting for abelian varieties -/

/-- **Glue (pullback pasting, `(A_L)_M ≅ A_M`).** For fields `K → L → M` (a scalar tower), the
iterated base change `(A ×_K L) ×_L M` is isomorphic to `A ×_K M` as a group scheme over `M`
(`Over.pullbackComp`, and `Spec` of the tower `K → L → M`). Category theory, no arithmetic. -/
def BaseChangeCompIso : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L M : Type) [Field L] [Algebra K L] [Field M]
    [Algebra K M] [Algebra L M] [IsScalarTower K L M],
    ∃ e : ((A.baseChange L).baseChange M).X ≅ (A.baseChange M).X, IsMonHom e.hom

/-! ### Pullback pasting and base change of group models (proved)

The kernel timeout met by h5-neron (`bcGen_isMonHom`) is avoided by proving the pasting lemmas
for an arbitrary scheme square (`exists_pbPaste`, `exists_pbSquare`, where the equation of the
square is eliminated by `subst`) and only then instantiating them; the last composition is
assembled with an explicit `instIsMonHomComp`, so that unification (not instance search) matches
the instance terms of `AbVar.baseChange`. -/

section PbPaste

open scoped Obj

/-- `f^* g^* G → (f ≫ g)^* G` (h5-neron). -/
noncomputable def pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z) :
    (Over.pullback f).obj ((Over.pullback g).obj G) ⟶ (Over.pullback (f ≫ g)).obj G :=
  (Over.pullbackComp f g).inv.app G

theorem isMonHom_pbCompInv {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (G : Over Z)
    [MonObj G] : IsMonHom (pbCompInv f g G) := by
  have h := ((Functor.mapMonCompIso (F := Over.pullback g) (G := Over.pullback f)).inv.app
      (Mon.mk G) ≫ (Functor.mapMonNatIso (Over.pullbackComp f g)).inv.app (Mon.mk G)).isMonHom_hom
  have e : pbCompInv f g G = 𝟙 _ ≫ pbCompInv f g G := (Category.id_comp _).symm
  rw [e]
  exact h

/-- Pullback pasting for group objects, with an arbitrary third side `h = f ≫ g`. -/
theorem exists_pbPaste {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (h : X ⟶ Z) (sq : f ≫ g = h)
    (G : Over Z) [GrpObj G] :
    letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback h).obj G) := Functor.grpObjObj
    ∃ e : (Over.pullback f).obj ((Over.pullback g).obj G) ≅ (Over.pullback h).obj G,
      IsMonHom e.hom := by
  subst sq
  letI : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback f).obj ((Over.pullback g).obj G)) := Functor.grpObjObj
  letI : GrpObj ((Over.pullback (f ≫ g)).obj G) := Functor.grpObjObj
  exact ⟨(Over.pullbackComp f g).symm.app G, isMonHom_pbCompInv f g G⟩

/-- **`BaseChangeCompIso`, proved.** -/
theorem baseChangeCompIso : BaseChangeCompIso := by
  intro K _ A L M _ _ _ _ _ _
  have sq : Spec.map (CommRingCat.ofHom (algebraMap L M)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap K L)) =
      Spec.map (CommRingCat.ofHom (algebraMap K M)) := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  exact exists_pbPaste _ _ _ sq A.X

/-- Pasting two pullback squares, with a group-scheme iso on one leg. -/
theorem exists_pbSquare {X Y₁ Y₂ Z : Scheme.{0}} (f₁ : X ⟶ Y₁) (g₁ : Y₁ ⟶ Z) (f₂ : X ⟶ Y₂)
    (g₂ : Y₂ ⟶ Z) (sq : f₁ ≫ g₁ = f₂ ≫ g₂) (G : Over Z) [GrpObj G] (H : Over Y₂) [GrpObj H]
    (u : (Over.pullback g₂).obj G ≅ H)
    (hu : letI : GrpObj ((Over.pullback g₂).obj G) := Functor.grpObjObj; IsMonHom u.hom) :
    letI : GrpObj ((Over.pullback g₁).obj G) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f₁).obj ((Over.pullback g₁).obj G)) := Functor.grpObjObj
    letI : GrpObj ((Over.pullback f₂).obj H) := Functor.grpObjObj
    ∃ e : (Over.pullback f₁).obj ((Over.pullback g₁).obj G) ≅ (Over.pullback f₂).obj H,
      IsMonHom e.hom := by
  obtain ⟨e₁, he₁⟩ := exists_pbPaste f₁ g₁ (f₁ ≫ g₁) rfl G
  obtain ⟨e₂, he₂⟩ := exists_pbPaste f₂ g₂ (f₁ ≫ g₁) sq.symm G
  have hu' : IsMonHom ((Over.pullback f₂).map u.hom) := inferInstance
  exact ⟨e₁ ≪≫ e₂.symm ≪≫ (Over.pullback f₂).mapIso u,
    (inferInstance : IsMonHom (e₁.hom ≫ e₂.inv ≫ (Over.pullback f₂).map u.hom))⟩

/-- The square `Spec L' → Spec 𝓞_{L'} → Spec 𝓞_L = Spec L' → Spec L → Spec 𝓞_L` (h5-neron). -/
theorem square1 (L L' : Type) [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L'] :
    Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L') L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))) =
      Spec.map (CommRingCat.ofHom (algebraMap L L')) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- **Glue H4b (`GroupModelBaseChangeExists`), proved**: `𝒢 ×_{𝓞_L} 𝓞_{L'}` with the generic
fibre identification `(𝒢 ×_{𝓞_L} 𝓞_{L'})_{L'} ≅ (𝒢_L)_{L'} ≅ (A_L)_{L'} ≅ A_{L'}`. -/
theorem groupModelBaseChangeExists : GroupModelBaseChangeExists := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢
  haveI : Smooth ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj
    𝒢.G).hom := by dsimp; infer_instance
  haveI : IsSeparated ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  haveI : QuasiCompact ((Over.pullback (Spec.map (CommRingCat.ofHom
    (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G).hom := by dsimp; infer_instance
  obtain ⟨c, hc⟩ := baseChangeCompIso K A L L'
  obtain ⟨e, he⟩ := exists_pbSquare _ _ _ _ (square1 L L') 𝒢.G (A.baseChange L).X 𝒢.gen 𝒢.gen_hom
  refine ⟨⟨_, e ≪≫ c, ?_⟩, Iso.refl _, ?_⟩
  · exact @CategoryTheory.instIsMonHomComp _ _ _ _ _ _ _ _ _ e.hom c.hom he hc
  · exact (inferInstance : IsMonHom (𝟙 ((Over.pullback
      (Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L'))))).obj 𝒢.G)))

end PbPaste

/-! ### Transport of (metrized) group models along an isomorphism of generic fibres (proved) -/

section Transport

variable {K K' : Type} [Field K] [Field K'] {A : AbVar K} {B : AbVar K'}
  {L : Type} [Field L] [NumberField L] [Algebra K L] [Algebra K' L]

/-- A group model of `A_L` is a group model of `B_L` for any group-scheme isomorphism
`A_L ≅ B_L`: same `𝒢`, generic-fibre identification composed with the isomorphism. -/
noncomputable def transportModel (e : (A.baseChange L).X ≅ (B.baseChange L).X)
    (he : IsMonHom e.hom) (𝒢 : GroupModel A L) : GroupModel B L where
  G := 𝒢.G
  gen := 𝒢.gen ≪≫ e
  gen_hom := by
    letI : GrpObj (genericFibre L 𝒢.G) := Functor.grpObjObj
    haveI := 𝒢.gen_hom
    exact (inferInstance : IsMonHom (𝒢.gen.hom ≫ e.hom))

/-- The same Hodge data metrize the transported model (the Hodge line, its lattice and the
complex points depend only on `𝒢`, not on the identification of the generic fibre). -/
noncomputable def transportMetrized (e : (A.baseChange L).X ≅ (B.baseChange L).X)
    (he : IsMonHom e.hom) {g : ℕ} (Mm : MetrizedModel A L g) : MetrizedModel B L g where
  model := transportModel e he Mm.model
  hodge := Mm.hodge
  lattice_eq := Mm.lattice_eq
  arch := Mm.arch

/-- Transport does not increase the height of a group model. Proved. -/
theorem transportModel_height_le (e : (A.baseChange L).X ≅ (B.baseChange L).X)
    (he : IsMonHom e.hom) (𝒢 : GroupModel A L) :
    (transportModel e he 𝒢).height ≤ 𝒢.height := by
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm => le_iInf fun hM => ?_
  subst hM
  exact iInf_le_of_le g (iInf_le_of_le (transportMetrized e he Mm) (iInf_le_of_le rfl le_rfl))

end Transport


/-! ### The Arakelov half of H4a (proved) and the geometric half (glue, stated)

`modelHeight_eq_of_isHodgeBaseChange`: if `D'` over `L'` is obtained from `D` over `L` by base
change (a semilinear injection `ψ` on the Hodge lines, with `⋀^g ω' = 𝓞_{L'} · ψ(⋀^g ω)`,
restricted period lattices and compatible coefficient maps), the model heights agree. The finite
part reduces to fractional ideals (`N(𝔞𝓞_{L'}) = N(𝔞)^{[L':L]}`, def-faltings'
`absNorm_extendedHom`) and the archimedean part to `sum_embeddings_comp`. -/

section ArakelovBC

open scoped nonZeroDivisors

/-- `secIndex` is invariant under an injective linear map. -/
theorem secIndex_map {K : Type*} [Field K] [NumberField K] {V W : Type*} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup W] [Module K W]
    [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W] (f : V →ₗ[𝓞 K] W) (hf : Function.Injective f)
    (Λ : Submodule (𝓞 K) V) (w : V) : secIndex (Λ.map f) (f w) = secIndex Λ w := by
  unfold secIndex
  rw [← Set.image_singleton, ← Submodule.map_span, Submodule.map_toAddSubgroup,
    Submodule.map_toAddSubgroup]
  exact AddSubgroup.relIndex_map_map_of_injective _ _ hf

/-- A finite index kills the quotient: `#(Λ/𝓞η) • x ∈ 𝓞η` for `x ∈ Λ`. -/
theorem secIndex_nsmul_mem {K : Type*} [Field K] [NumberField K] {V : Type*} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (Λ : Submodule (𝓞 K) V) (w : V)
    {x : V} (hx : x ∈ Λ) : secIndex Λ w • x ∈ Submodule.span (𝓞 K) {w} :=
  AddSubgroup.nsmul_relIndex_mem (Submodule.span (𝓞 K) {w}).toAddSubgroup hx

variable {L L' : Type} [Field L] [NumberField L] [Field L'] [NumberField L'] [Algebra L L']

/-- **The finite part of base change**: `#(Λ'/𝓞_{L'}ιη) = #(Λ/𝓞_Lη)^{[L':L]}` for
`Λ' = 𝓞_{L'} · ψ(Λ)`. -/
theorem secIndex_baseChange {V V' : Type*} [AddCommGroup V] [Module L V] [Module (𝓞 L) V]
    [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V'] [Module (𝓞 L') V']
    [IsScalarTower (𝓞 L') L' V'] (hV : Module.finrank L V = 1) (ψ : V →+ V')
    (hsmul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) (Λ : Submodule (𝓞 L) V)
    {w : V} (hηΛ : w ∈ Λ) (hη : w ≠ 0) (hη' : ψ w ≠ 0) (hi : secIndex Λ w ≠ 0) :
    secIndex (Submodule.span (𝓞 L') (ψ '' Λ)) (ψ w) = secIndex Λ w ^ Module.finrank L L' := by
  -- coordinates `c ↦ c • w` and `c ↦ c • ιη`
  let φ : L →ₗ[𝓞 L] V := (LinearMap.toSpanSingleton L V w).restrictScalars (𝓞 L)
  let φ' : L' →ₗ[𝓞 L'] V' := (LinearMap.toSpanSingleton L' V' (ψ w)).restrictScalars (𝓞 L')
  have hφ : ∀ c, φ c = c • w := fun c => rfl
  have hφ' : ∀ c, φ' c = c • ψ w := fun c => rfl
  have hφinj : Function.Injective φ := fun a b h => by
    rw [hφ, hφ] at h
    exact smul_left_injective L hη h
  have hφ'inj : Function.Injective φ' := fun a b h => by
    rw [hφ', hφ'] at h
    exact smul_left_injective L' hη' h
  have hφsurj : Function.Surjective φ := fun v => by
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w hη).mp hV v
    exact ⟨c, hc⟩
  set I : Submodule (𝓞 L) L := Λ.comap φ with hI
  have hΛ : Λ = I.map φ := (Submodule.map_comap_eq_of_surjective hφsurj Λ).symm
  have h1I : (1 : L) ∈ I := by simpa [hI, hφ] using hηΛ
  have hidx : secIndex I 1 = secIndex Λ w := by
    conv_rhs => rw [hΛ, show w = φ 1 by simp [hφ]]
    exact (secIndex_map φ hφinj I 1).symm
  -- `ψ(Λ) = φ'(L'-image of I)`
  have himg : ψ '' (Λ : Set V) = φ' '' (algebraMap L L' '' (I : Set L)) := by
    rw [hΛ, Submodule.map_coe, Set.image_image, Set.image_image]
    refine Set.image_congr fun c _ => ?_
    rw [hφ, hφ', hsmul]
  have hspan : Submodule.span (𝓞 L') (ψ '' (Λ : Set V)) =
      (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))).map φ' := by
    rw [himg, Submodule.map_span]
  have hidx' : secIndex (Submodule.span (𝓞 L') (ψ '' (Λ : Set V))) (ψ w) =
      secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 := by
    rw [hspan, show ψ w = φ' 1 by simp [hφ']]
    exact secIndex_map φ' hφ'inj _ 1
  -- `I` is a fractional ideal
  set N := secIndex I 1 with hN
  have hN0 : N ≠ 0 := hidx ▸ hi
  have hfrac : IsFractional (𝓞 L)⁰ I := by
    refine ⟨(N : 𝓞 L), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast hN0), fun b hb => ?_⟩
    have hm := secIndex_nsmul_mem I 1 hb
    rw [Submodule.mem_span_singleton] at hm
    obtain ⟨a, ha⟩ := hm
    refine ⟨a, ?_⟩
    rw [Nat.cast_smul_eq_nsmul, ← ha, Algebra.smul_def, _root_.mul_one]
  let I₀ : FractionalIdeal (𝓞 L)⁰ L := ⟨I, hfrac⟩
  have hI₀ : (I₀ : Submodule (𝓞 L) L) = I := rfl
  have e1 := secIndex_mul_absNorm I₀ (x := 1) h1I one_ne_zero
  have e2 := secIndex_mul_absNorm (FractionalIdeal.extendedHom L' (𝓞 L') I₀) (x := 1)
    (by
      rw [← FractionalIdeal.mem_coe, FractionalIdeal.coe_extendedHom_eq_span]
      exact Submodule.subset_span ⟨1, h1I, map_one _⟩) one_ne_zero
  rw [FractionalIdeal.coe_extendedHom_eq_span, absNorm_extendedHom, map_one, abs_one] at e2
  rw [map_one, abs_one] at e1
  have e1' : (secIndex I 1 : ℚ) * FractionalIdeal.absNorm I₀ = 1 := e1
  have e2' : (secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 : ℚ) *
      FractionalIdeal.absNorm I₀ ^ Module.finrank L L' = 1 := e2
  rw [← hidx, hidx']
  have key : (secIndex (Submodule.span (𝓞 L') (algebraMap L L' '' (I : Set L))) 1 : ℚ) =
      (secIndex I 1 : ℚ) ^ Module.finrank L L' := by
    rw [eq_inv_of_mul_eq_one_left e1', eq_inv_of_mul_eq_one_left e2', inv_pow]
  exact_mod_cast key

/-- **Base change data for Hodge data** `D/L ↦ D'/L'` along a semilinear injection `ψ`. -/
structure IsHodgeBaseChange {g : ℕ} {V V' : Type*} [AddCommGroup V] [Module L V]
    [Module (𝓞 L) V] [AddCommGroup V'] [Module L' V'] [Module (𝓞 L') V']
    (D : HodgeData L g V) (D' : HodgeData L' g V') (ψ : V →+ V') : Prop where
  smul : ∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v
  ne_zero : ∀ v, v ≠ 0 → ψ v ≠ 0
  lattice : D'.lattice = Submodule.span (𝓞 L') (ψ '' D.lattice)
  periods : ∀ τ' : L' →+* ℂ, D'.periods τ' = D.periods (τ'.comp (algebraMap L L'))
  coeff : ∀ (τ' : L' →+* ℂ) v, D'.coeff τ' (ψ v) = D.coeff (τ'.comp (algebraMap L L')) v

/-- **The model height is invariant under base change of Hodge data.** Proved. -/
theorem modelHeight_eq_of_isHodgeBaseChange {g : ℕ} {V V' : Type*} [AddCommGroup V]
    [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] [AddCommGroup V'] [Module L' V']
    [Module (𝓞 L') V'] [IsScalarTower (𝓞 L') L' V'] (D : HodgeData L g V) (D' : HodgeData L' g V')
    (ψ : V →+ V') (h : IsHodgeBaseChange D D' ψ) : D'.modelHeight = D.modelHeight := by
  obtain ⟨w, hηM, hη, hi⟩ := D.isLattice
  have hη' : ψ w ≠ 0 := h.ne_zero w hη
  have hηM' : ψ w ∈ D'.lattice := by
    rw [h.lattice]; exact Submodule.subset_span ⟨w, hηM, rfl⟩
  rw [D.modelHeight_eq hηM hη, D'.modelHeight_eq hηM' hη']
  have hsec : secIndex D'.lattice (ψ w) = secIndex D.lattice w ^ Module.finrank L L' := by
    rw [h.lattice]
    exact secIndex_baseChange D.finrank_eq_one ψ h.smul D.lattice hηM hη hη' hi
  have hsum : ∑ τ' : L' →+* ℂ, Real.log (torusMetricSq (D'.periods τ') (D'.coeff τ' (ψ w))) =
      Module.finrank L L' *
        ∑ σ : L →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)) := by
    simp only [h.periods, h.coeff]
    exact sum_embeddings_comp (fun σ => Real.log (torusMetricSq (D.periods σ) (D.coeff σ w)))
  rw [hsec, hsum, ← Module.finrank_mul_finrank ℚ L L']
  have hK : (0 : ℝ) < Module.finrank ℚ L := by exact_mod_cast Module.finrank_pos
  have hL : (0 : ℝ) < Module.finrank L L' := by exact_mod_cast Module.finrank_pos
  push_cast
  rw [Real.log_pow]
  field_simp

end ArakelovBC

/-- **Glue H4a, geometric half (stated).** A metrization of a group model `𝒢/𝓞_L` induces one of
its base change `𝒢'/𝓞_{L'}`, by base change of the Hodge data: `ψ` is the natural map
`⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (from `𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`), `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)`
(formation of `e*Ω¹` of a smooth group scheme commutes with base change; EGA IV 17.2.3,
UNVERIFIED locator), and at `τ' : L' → ℂ` the uniformization of `𝒢(ℂ)_{τ'|_L}` composed with the
bijection `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` (universal property of the pullback). Glue (a property of
def-faltings' definitions), STANDARD; not a literature leaf. -/
def MetrizationBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 →
    ∀ (g : ℕ) (Mm : MetrizedModel A L g), Mm.model = 𝒢 →
    ∃ (Mm' : MetrizedModel A L' g) (ψ : Mm.model.hodgeSpace g →+ Mm'.model.hodgeSpace g),
      Mm'.model = 𝒢' ∧ IsHodgeBaseChange Mm.hodge Mm'.hodge ψ

/-- **`ModelHeightBaseChangeLE` from the geometric half.** Proved. -/
theorem modelHeightBaseChangeLE_of_metrization (h : MetrizationBaseChange) :
    ModelHeightBaseChangeLE := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢
  unfold GroupModel.height
  refine le_iInf fun g => le_iInf fun Mm => le_iInf fun hM => ?_
  obtain ⟨Mm', ψ, hM', hι⟩ := h K A L L' 𝒢 𝒢' h𝒢 g Mm hM
  refine iInf_le_of_le g (iInf_le_of_le Mm' (iInf_le_of_le hM' ?_))
  rw [modelHeight_eq_of_isHodgeBaseChange Mm.hodge Mm'.hodge ψ hι]

/-- **Glue H4a, geometric content, stated without metrized models.** For a base change `𝒢'` of
`𝒢` and each `g`, the natural map `ψ : ⋀^g ω_{A_L} → ⋀^g ω_{A_{L'}}` (induced by
`𝒪_{𝒢,ξ} → 𝒪_{𝒢',ξ'}`):
* is `L`-semilinear over `L → L'` and injective on nonzero vectors, and the Hodge space of `𝒢'` is
  an `L'`-line when that of `𝒢` is an `L`-line (it is `L' ⊗_L` of it);
* carries the lattice: `⋀^g ω_{𝒢'} = 𝓞_{L'} · ψ(⋀^g ω_𝒢)` (formation of `e*Ω¹` of a smooth group
  scheme commutes with base change; EGA IV 17.2.3, UNVERIFIED locator);
* is compatible with uniformizations: an analytic uniformization `Φ` of `𝒢(ℂ)_{τ'|_L}` gives one
  `Φ'` of `𝒢'(ℂ)_{τ'}` with the same kernel (compose with the bijection
  `𝒢(ℂ)_{τ'|_L} ≅ 𝒢'(ℂ)_{τ'}` of the pullback), and if a coefficient map `c` is computed by `Φ` on
  wedges of germs, its `τ'`-semilinear extension `c'` (`c' ∘ ψ = c`) is computed by `Φ'` on wedges
  of germs of `𝒢'` (both sides are `τ'`-semilinear alternating functions of the differentials
  `df'_i`, and they agree on pulled-back germs, which span).
Glue (a property of def-faltings' definitions), STANDARD; not a literature leaf. -/
def HodgeLineBaseChange : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L L' : Type) [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L'] [IsScalarTower K L L']
    (𝒢 : GroupModel A L) (𝒢' : GroupModel A L'), IsBaseChangeOf 𝒢' 𝒢 → ∀ g : ℕ,
    ∃ ψ : 𝒢.hodgeSpace g →+ 𝒢'.hodgeSpace g,
      (∀ (c : L) v, ψ (c • v) = algebraMap L L' c • ψ v) ∧
      (∀ v, v ≠ 0 → ψ v ≠ 0) ∧
      (Module.finrank L (𝒢.hodgeSpace g) = 1 → Module.finrank L' (𝒢'.hodgeSpace g) = 1) ∧
      𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' 𝒢.detLattice g) ∧
      ∀ (τ' : L' →+* ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
        (Φ : (Fin g → ℂ) → 𝒢.Pts (τ'.comp (algebraMap L L'))),
        𝒢.IsAnalyticUniformization _ Λ Φ →
        ∃ Φ' : (Fin g → ℂ) → 𝒢'.Pts τ', 𝒢'.IsAnalyticUniformization τ' Λ Φ' ∧
          ∀ (c : 𝒢.hodgeSpace g →ₛₗ[τ'.comp (algebraMap L L')] ℂ)
            (c' : 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ),
            (∀ f, c (𝒢.wedge f) = 𝒢.jacDet Φ f) → (∀ v, c' (ψ v) = c v) →
            ∀ f', c' (𝒢'.wedge f') = 𝒢'.jacDet Φ' f'

/-- **`MetrizationBaseChange` from `HodgeLineBaseChange`.** The Hodge data of `𝒢'`: lattice
`⋀^g ω_{𝒢'}`, restricted period lattices, and the `τ'`-semilinear extension of the coefficient
maps along `ψ` (through the coordinate `c ↦ c · ψ(w)` on the `L'`-line). Proved. -/
theorem metrizationBaseChange_of_hodgeLine (h : HodgeLineBaseChange) :
    MetrizationBaseChange := by
  intro K _ A L L' _ _ _ _ _ _ _ _ 𝒢 𝒢' h𝒢 g Mm hM
  subst hM
  obtain ⟨ψ, hsmul, hne, hfin, hlat, harch⟩ := h K A L L' Mm.model 𝒢' h𝒢 g
  obtain ⟨w, hwM, hw, hi⟩ := Mm.hodge.isLattice
  have hw' : ψ w ≠ 0 := hne w hw
  have hfin' : Module.finrank L' (𝒢'.hodgeSpace g) = 1 := hfin Mm.hodge.finrank_eq_one
  -- the coordinate `c ↦ c • ψ w` on the `L'`-line
  have hinj : Function.Injective (LinearMap.toSpanSingleton L' (𝒢'.hodgeSpace g) (ψ w)) :=
    fun a b hab => smul_left_injective L' hw' hab
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton L' (𝒢'.hodgeSpace g) (ψ w)) :=
    fun v => (finrank_eq_one_iff_of_nonzero' (ψ w) hw').mp hfin' v
  let e : L' ≃ₗ[L'] 𝒢'.hodgeSpace g := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  have he : ∀ c, e c = c • ψ w := fun c => rfl
  -- the extended coefficient maps
  let lin : ∀ τ' : L' →+* ℂ, L' →ₛₗ[τ'] ℂ := fun τ' =>
    { toFun := fun c => τ' c * Mm.hodge.coeff (τ'.comp (algebraMap L L')) w
      map_add' := fun a b => by rw [map_add, add_mul]
      map_smul' := fun a b => by rw [smul_eq_mul, map_mul, smul_eq_mul, _root_.mul_assoc] }
  let coeff' : ∀ τ' : L' →+* ℂ, 𝒢'.hodgeSpace g →ₛₗ[τ'] ℂ := fun τ' =>
    (lin τ').comp e.symm.toLinearMap
  have hcoeff' : ∀ (τ' : L' →+* ℂ) v,
      coeff' τ' (ψ v) = Mm.hodge.coeff (τ'.comp (algebraMap L L')) v := by
    intro τ' v
    obtain ⟨a, rfl⟩ := (finrank_eq_one_iff_of_nonzero' w hw).mp Mm.hodge.finrank_eq_one v
    have h1 : e.symm (ψ (a • w)) = algebraMap L L' a := by
      rw [LinearEquiv.symm_apply_eq, he, hsmul]
    show lin τ' (e.symm (ψ (a • w))) = _
    rw [h1]
    show τ' (algebraMap L L' a) * _ = _
    rw [map_smulₛₗ, smul_eq_mul]
    rfl
  have hlat' : 𝒢'.detLattice g = Submodule.span (𝓞 L') (ψ '' Mm.hodge.lattice) := by
    rw [hlat, Mm.lattice_eq]
  let D' : HodgeData L' g (𝒢'.hodgeSpace g) :=
    { lattice := 𝒢'.detLattice g
      finrank_eq_one := hfin'
      isLattice := by
        refine ⟨ψ w, ?_, hw', ?_⟩
        · rw [hlat']; exact Submodule.subset_span ⟨w, hwM, rfl⟩
        · rw [hlat', secIndex_baseChange Mm.hodge.finrank_eq_one ψ hsmul _ hwM hw hw' hi]
          exact pow_ne_zero _ hi
      periods := fun τ' => Mm.hodge.periods (τ'.comp (algebraMap L L'))
      periods_discrete := fun τ' => Mm.hodge.periods_discrete _
      periods_isZLattice := fun τ' => Mm.hodge.periods_isZLattice _
      coeff := coeff'
      coeff_ne_zero := fun τ' h0 => by
        have h2 := hcoeff' τ' w
        rw [h0, LinearMap.zero_apply] at h2
        exact Mm.hodge.coeff_apply_ne_zero _ hw h2.symm }
  let Mm' : MetrizedModel A L' g :=
    { model := 𝒢'
      hodge := D'
      lattice_eq := rfl
      arch := fun τ' => by
        obtain ⟨Φ, hΦ, hc⟩ := Mm.arch (τ'.comp (algebraMap L L'))
        obtain ⟨Φ', hΦ', hc'⟩ := harch τ' _ Φ hΦ
        exact ⟨Φ', hΦ', hc' _ (coeff' τ') hc (hcoeff' τ')⟩ }
  exact ⟨Mm', ψ, rfl,
    { smul := hsmul
      ne_zero := hne
      lattice := hlat'
      periods := fun _ => rfl
      coeff := hcoeff' }⟩

/-! ### The piece, from the glue (proved) -/

/-- **`StableHeightBaseChange` from three glue statements** (`BaseChangeCompIso`, and h5-neron's
`GroupModelBaseChangeExists` (H4b) and the `≤` half `ModelHeightBaseChangeLE` of H4a) and the proved
`compositum`. `≥`: a model of `(A_L)_M` is a model of `A_M` (transport along `(A_L)_M ≅ A_M`).
`≤`: a model `𝒢` of `A_E` base-changes to a model of `A_M` over a compositum `M` of `E` and `L`,
with no larger height (H4a `≤`, H4b), and is then a model of `(A_L)_M`. -/
theorem stableHeightBaseChange_of_glue (hcomp : BaseChangeCompIso)
    (hbcE : GroupModelBaseChangeExists) (hbc : ModelHeightBaseChangeLE) :
    StableHeightBaseChange := by
  intro K _ _ L _ _ _ A
  rw [stableFaltingsHeight_eq_iInf_height, stableFaltingsHeight_eq_iInf_height]
  apply le_antisymm
  · refine le_iInf fun E => le_iInf fun 𝒢 => ?_
    obtain ⟨M, i1, i2, i3, i4, i5, t1, t2⟩ := compositum K E.L L
    obtain ⟨𝒢', h𝒢'⟩ := hbcE K A E.L M 𝒢
    obtain ⟨e, he⟩ := hcomp K A L M
    have he' : IsMonHom e.symm.hom := (inferInstance : IsMonHom e.inv)
    calc ⨅ (E' : FinExt L) (𝒢₁ : GroupModel (A.baseChange L) E'.L), 𝒢₁.height
        ≤ (transportModel e.symm he' 𝒢').height :=
          iInf_le_of_le (FinExt.mk M) (iInf_le_of_le _ le_rfl)
      _ ≤ 𝒢'.height := transportModel_height_le _ _ _
      _ ≤ 𝒢.height := hbc K A E.L M 𝒢 𝒢' h𝒢'
  · refine le_iInf fun E => le_iInf fun 𝒢 => ?_
    letI : Algebra K E.L := ((algebraMap L E.L).comp (algebraMap K L)).toAlgebra
    haveI : IsScalarTower K L E.L := IsScalarTower.of_algebraMap_eq fun _ => rfl
    obtain ⟨e, he⟩ := hcomp K A L E.L
    calc ⨅ (E' : FinExt K) (𝒢₁ : GroupModel A E'.L), 𝒢₁.height
        ≤ (transportModel e he 𝒢).height :=
          iInf_le_of_le (FinExt.mk E.L) (iInf_le_of_le _ le_rfl)
      _ ≤ 𝒢.height := transportModel_height_le _ _ _

/-- **`StableHeightBaseChange` from the inequality half of glue H4a alone** (`BaseChangeCompIso`
and H4b are proved above). -/
theorem stableHeightBaseChange_of_modelHeightBaseChangeLE (hbc : ModelHeightBaseChangeLE) :
    StableHeightBaseChange :=
  stableHeightBaseChange_of_glue baseChangeCompIso groupModelBaseChangeExists hbc

/-- **`StableHeightBaseChange` from h5-neron's glue H4a.** -/
theorem stableHeightBaseChange_of_modelHeightBaseChange (hbc : ModelHeightBaseChange) :
    StableHeightBaseChange :=
  stableHeightBaseChange_of_modelHeightBaseChangeLE (modelHeightBaseChangeLE hbc)

/-- **`StableHeightBaseChange` from the geometric half of H4a alone.** -/
theorem stableHeightBaseChange_of_metrization (h : MetrizationBaseChange) :
    StableHeightBaseChange :=
  stableHeightBaseChange_of_modelHeightBaseChangeLE (modelHeightBaseChangeLE_of_metrization h)

/-- **`StableHeightBaseChange` from `HodgeLineBaseChange` alone.** -/
theorem stableHeightBaseChange_of_hodgeLine (h : HodgeLineBaseChange) :
    StableHeightBaseChange :=
  stableHeightBaseChange_of_metrization (metrizationBaseChange_of_hodgeLine h)

end G0StableBC

end
end G0StableBCSec

/-! ## g0-heightadd: lines 390-473 of scratch/g0-heightadd/part_heightadd.lean and the G0HeightAdd section of part_prod.lean (lines 1-92) -/
section G0HeightAddSec
noncomputable section

/-! ## Glue P2 (`ProductModelHeight`) from four smaller Props

`ProductModelHeight` (h5-neron) compares, for a product model `𝒢P ≅ 𝒢₁ × 𝒢₂`, the heights of
the three group models (infima over metrizations). It follows from:
* `AnalyticUniformizationUnique` (def-faltings, already stated: the uniqueness half of AN3);
* `MetrizationDimUnique` (new glue): two metrizations of one group model have the same `g`;
* `MetrizationExists` (new glue): every group model has a metrization;
* `ProductMetrization` (new glue P2a): metrizations of `𝒢₁`, `𝒢₂` give one of `𝒢P` whose height
  is the sum (the construction direction; equality). -/

namespace ZInQ.G0HeightAdd

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings H5Neron

/-- **Glue P2a (product of metrized models).** If `𝒢P ≅ 𝒢₁ × 𝒢₂` (`IsProductModel`) and `M₁`, `M₂`
are metrizations of `𝒢₁`, `𝒢₂` of dimensions `g₁`, `g₂`, then `𝒢P` has a metrization of
dimension `g₁ + g₂` whose model height is the sum. Why true (STANDARD): the cotangent space at
the identity of `𝒢₁ ×_{𝓞_L} 𝒢₂` is `ω₁ ⊕ ω₂` (and `ω_{𝒢P} = ω_{𝒢₁} ⊕ ω_{𝒢₂}` as lattices),
`⋀^{g₁+g₂}(ω₁ ⊕ ω₂) = ⋀^{g₁}ω₁ ⊗ ⋀^{g₂}ω₂`, the product `Φ₁ × Φ₂ : ℂ^{g₁+g₂} → 𝒢₁(ℂ) × 𝒢₂(ℂ)`
is an analytic uniformization with kernel `Λ₁ × Λ₂` whose Jacobian determinant on product
wedges is the product, `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`, and the Arakelov degree of a
tensor product of Hermitian lines is the sum (Faltings 1983 §1; Deligne, Sém. Bourbaki 616, §1;
locators UNVERIFIED). Unproved: Mathlib has no computation of the stalk of a fibre product of
schemes. -/
def ProductMetrization : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ MP : MetrizedModel C L (g₁ + g₂), MP.model = 𝒢P ∧
        MP.hodge.modelHeight = M₁.hodge.modelHeight + M₂.hodge.modelHeight

/-- **Glue (existence of metrizations; correctness of def-faltings' definition).** Every smooth
group model `𝒢` of `A_L` carries a metrization (of dimension `dim A`). Why true (STANDARD): the
Hodge data of `𝒢` exist by `HodgeLatticeTheorem` and the uniformization of each `𝒢(ℂ)_τ` by
`AnalyticUniformizationExists` (Mumford, *Abelian varieties* §1, UNVERIFIED), with the
coefficient map `coeff_τ(1 ⊗ df) = jacDet Φ f`. This is the same caveat as on `LeafAdopt.H5`
(the index set of the infimum is nonempty), for each model separately. Unproved. -/
def MetrizationExists : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (𝒢 : GroupModel A L), ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒢

/-- **Glue (the dimension of a metrization).** Two metrizations of the same group model have
the same dimension (both equal `dim A`: the `MetrizedModel` docstring's argument: for
`0 < g ≠ dim A` the Hodge space is not a line, and `g = 0` is excluded for `dim A ≥ 1` by the
surjectivity of `Φ : ℂ⁰ → A_τ(ℂ)`; STANDARD, unproved). -/
def MetrizationDimUnique : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (L : Type) [Field L] [NumberField L] [Algebra K L]
    (g g' : ℕ) (M : MetrizedModel A L g) (M' : MetrizedModel A L g'), M.model = M'.model → g = g'

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- A metrization bounds the height of its model from above. -/
theorem height_le_of_model {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L}
    (h : M.model = 𝒢) : 𝒢.height ≤ (M.hodge.modelHeight : EReal) :=
  iInf_le_of_le g (iInf_le_of_le M (iInf_le_of_le h le_rfl))

/-- Given AN3-uniqueness and `MetrizationDimUnique`, a metrization computes the height of its
model (from below; with `height_le_of_model`, equality). -/
theorem le_height_of_model (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    {g : ℕ} (M : MetrizedModel A L g) {𝒢 : GroupModel A L} (h : M.model = 𝒢) :
    (M.hodge.modelHeight : EReal) ≤ 𝒢.height := by
  refine le_iInf fun g' => le_iInf fun M' => le_iInf fun hM' => ?_
  obtain rfl := hD K A L g g' M M' (h.trans hM'.symm)
  rw [MetrizedModel.modelHeight_eq_of_model_eq hU M M' (h.trans hM'.symm)]

/-- **Glue P2 (`ProductModelHeight`) from `AnalyticUniformizationUnique`,
`MetrizationDimUnique`, `MetrizationExists` and `ProductMetrization`.** -/
theorem productModelHeight_of (hU : AnalyticUniformizationUnique) (hD : MetrizationDimUnique)
    (hE : MetrizationExists) (hP : ProductMetrization) : ProductModelHeight := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hPM
  obtain ⟨g₁, M₁, h₁⟩ := hE K A L 𝒢₁
  obtain ⟨g₂, M₂, h₂⟩ := hE K B L 𝒢₂
  obtain ⟨MP, hMP, hh⟩ := hP K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hPM g₁ g₂ M₁ M₂ h₁ h₂
  calc 𝒢₁.height + 𝒢₂.height
      ≤ (M₁.hodge.modelHeight : EReal) + (M₂.hodge.modelHeight : EReal) :=
        add_le_add (height_le_of_model M₁ h₁) (height_le_of_model M₂ h₂)
    _ = (MP.hodge.modelHeight : EReal) := by rw [hh, EReal.coe_add]
    _ ≤ 𝒢P.height := le_height_of_model hU hD MP hMP

end ZInQ.G0HeightAdd

/-! ## P2a split: the Arakelov-degree half proved

`ProductMetrization` (P2a) = a geometric construction (`ProductMetrizationGeo`: the product
metrization with a product section `η = η₁ ∧ η₂` for which the index, the coefficients and the
covolumes are multiplicative) + the height computation (`modelHeight_add_of`, proved). -/

namespace ZInQ.G0HeightAdd

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField MeasureTheory DefFaltings H5Neron

section HodgeAdd

variable {K : Type*} [Field K] [NumberField K]
variable {V V₁ V₂ : Type*} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V₁] [Module K V₁] [Module (𝓞 K) V₁] [IsScalarTower (𝓞 K) K V₁]
  [AddCommGroup V₂] [Module K V₂] [Module (𝓞 K) V₂] [IsScalarTower (𝓞 K) K V₂]

/-- **Additivity of the model height (proved).** If the Hodge data `D` (dimension `g₁ + g₂`)
has a nonzero section `s` whose lattice index, coefficients and period covolumes are the
products of those of nonzero sections `s₁`, `s₂` of `D₁`, `D₂`, then
`h(D) = h(D₁) + h(D₂)` (Faltings' formula `HodgeData.modelHeight_eq` and `log` of products). -/
theorem modelHeight_add_of {g₁ g₂ : ℕ} (D : HodgeData K (g₁ + g₂) V) (D₁ : HodgeData K g₁ V₁)
    (D₂ : HodgeData K g₂ V₂) {s : V} {s₁ : V₁} {s₂ : V₂} (hs : s ∈ D.lattice) (hs0 : s ≠ 0)
    (hs₁ : s₁ ∈ D₁.lattice) (hs₁0 : s₁ ≠ 0) (hs₂ : s₂ ∈ D₂.lattice) (hs₂0 : s₂ ≠ 0)
    (hidx : secIndex D.lattice s = secIndex D₁.lattice s₁ * secIndex D₂.lattice s₂)
    (hcoeff : ∀ σ, D.coeff σ s = D₁.coeff σ s₁ * D₂.coeff σ s₂)
    (hcov : ∀ σ, ZLattice.covolume (D.periods σ) =
      ZLattice.covolume (D₁.periods σ) * ZLattice.covolume (D₂.periods σ)) :
    D.modelHeight = D₁.modelHeight + D₂.modelHeight := by
  rw [D.modelHeight_eq hs hs0, D₁.modelHeight_eq hs₁ hs₁0, D₂.modelHeight_eq hs₂ hs₂0]
  have ht : ∀ σ : K →+* ℂ, torusMetricSq (D.periods σ) (D.coeff σ s) =
      torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁) *
        torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂) := by
    intro σ
    simp only [torusMetricSq, hcoeff σ, hcov σ, norm_mul]
    ring
  have hlog : ∀ σ : K →+* ℂ, Real.log (torusMetricSq (D.periods σ) (D.coeff σ s)) =
      Real.log (torusMetricSq (D₁.periods σ) (D₁.coeff σ s₁)) +
        Real.log (torusMetricSq (D₂.periods σ) (D₂.coeff σ s₂)) := by
    intro σ
    rw [ht σ]
    have := D₁.periods_discrete σ
    have := D₁.periods_isZLattice σ
    have := D₂.periods_discrete σ
    have := D₂.periods_isZLattice σ
    exact Real.log_mul (torusMetricSq_pos _ (D₁.coeff_apply_ne_zero σ hs₁0)).ne'
      (torusMetricSq_pos _ (D₂.coeff_apply_ne_zero σ hs₂0)).ne'
  have hi₁ : (secIndex D₁.lattice s₁ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₁.hodgeBundle.secIndex_ne_zero hs₁ hs₁0)
  have hi₂ : (secIndex D₂.lattice s₂ : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (D₂.hodgeBundle.secIndex_ne_zero hs₂ hs₂0)
  rw [hidx, Nat.cast_mul, Real.log_mul hi₁ hi₂, Finset.sum_congr rfl (fun σ _ => hlog σ),
    Finset.sum_add_distrib]
  ring

end HodgeAdd

/-- **Glue P2a-geo (the product metrization, geometric half of P2a).** For `𝒢P ≅ 𝒢₁ × 𝒢₂` and
metrizations `M₁`, `M₂`, there is a metrization `MP` of `𝒢P` of dimension `g₁ + g₂` and nonzero
sections `s ∈ ⋀^{g₁+g₂}ω_{𝒢P}`, `sᵢ ∈ ⋀^{gᵢ}ω_{𝒢ᵢ}` such that the lattice index, the coefficients
and the period covolumes of `s` are the products of those of `s₁`, `s₂`. Why true (STANDARD):
take `s = p₁*s₁ ∧ p₂*s₂`; `ω_{𝒢P} = ω_{𝒢₁} ⊕ ω_{𝒢₂}` gives `⋀^{top}ω_{𝒢P} = ⋀ω_{𝒢₁} ⊗ ⋀ω_{𝒢₂}`, and
for invertible `𝓞_L`-modules the index of `𝓞s₁ ⊗ 𝓞s₂` is the product (norms of ideals are
multiplicative); `Φ₁ × Φ₂` (coordinates `Fin.append`) is an analytic uniformization of
`𝒢P(ℂ)_τ = 𝒢₁(ℂ)_τ × 𝒢₂(ℂ)_τ` with period lattice `Λ₁ × Λ₂`, block-diagonal Jacobian
(so `jacDet` multiplies), and `covol(Λ₁ × Λ₂) = covol Λ₁ · covol Λ₂`. Unproved (stalks of fibre
products of schemes are not in Mathlib). -/
def ProductMetrizationGeo : Prop :=
  ∀ (K : Type) [Field K] (A B C : AbVar K) (eC : C.X ≅ A.X ⊗ B.X) (L : Type) [Field L]
    [NumberField L] [Algebra K L] (𝒢P : GroupModel C L) (𝒢₁ : GroupModel A L)
    (𝒢₂ : GroupModel B L), IsProductModel eC 𝒢P 𝒢₁ 𝒢₂ →
    ∀ (g₁ g₂ : ℕ) (M₁ : MetrizedModel A L g₁) (M₂ : MetrizedModel B L g₂),
      M₁.model = 𝒢₁ → M₂.model = 𝒢₂ →
      ∃ (MP : MetrizedModel C L (g₁ + g₂)) (s : MP.model.hodgeSpace (g₁ + g₂))
        (s₁ : M₁.model.hodgeSpace g₁) (s₂ : M₂.model.hodgeSpace g₂),
        MP.model = 𝒢P ∧ s ∈ MP.hodge.lattice ∧ s ≠ 0 ∧ s₁ ∈ M₁.hodge.lattice ∧ s₁ ≠ 0 ∧
        s₂ ∈ M₂.hodge.lattice ∧ s₂ ≠ 0 ∧
        secIndex MP.hodge.lattice s = secIndex M₁.hodge.lattice s₁ * secIndex M₂.hodge.lattice s₂ ∧
        (∀ σ, MP.hodge.coeff σ s = M₁.hodge.coeff σ s₁ * M₂.hodge.coeff σ s₂) ∧
        (∀ σ, ZLattice.covolume (MP.hodge.periods σ) =
          ZLattice.covolume (M₁.hodge.periods σ) * ZLattice.covolume (M₂.hodge.periods σ))

/-- **P2a from P2a-geo (proved).** -/
theorem productMetrization_of_geo (h : ProductMetrizationGeo) : ProductMetrization := by
  intro K _ A B C eC L _ _ _ 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  obtain ⟨MP, s, s₁, s₂, hMP, hs, hs0, hs₁, hs₁0, hs₂, hs₂0, hidx, hc, hcov⟩ :=
    h K A B C eC L 𝒢P 𝒢₁ 𝒢₂ hP g₁ g₂ M₁ M₂ h₁ h₂
  exact ⟨MP, hMP, modelHeight_add_of MP.hodge M₁.hodge M₂.hodge hs hs0 hs₁ hs₁0 hs₂ hs₂0 hidx hc hcov⟩

end ZInQ.G0HeightAdd
end
end G0HeightAddSec

/-! ## Kernel copy: ZInQKernel/HDecomp/Descent/WP3.lean (verbatim minus imports). Needed by g0-mod-field (T14/T15 → LeafHasse/LeafLocalTwo). -/
section GlueWP3Sec

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt2 from
`scratch/glue-wp3/WP3.lean`.
The literature leaves are hypotheses (`def … : Prop`); no `sorry`, no `axiom`. -/


/-!
# glue-wp3: glue-descent's `LeafHasse`, `LeafLocalTwo` from the announced leaves T14-T15

The leaf bundle (`scratch/h-decomposition/Leaves.lean`, `HSyn` bundle fields `t14a`, `t14b`,
`t15`) announces the Brauer facts as pkg-I6's cochain forms I6.2a′-c′
(`PkgI6.BrauerHasse2C`, `PkgI6.BrauerReciprocity2C`, `PkgI6.LocalH2CardC`: continuous
inhomogeneous cochains `G × G → ZMod 2`, all places including `∞`).  glue-descent proved B2-B3
(`GlueDescent.B3Q.b3_degree_le_QM`) from its own forms `GlueDescent.B2Q.LeafHasse`,
`LeafLocalTwo` (locally constant `ℂˣ`-valued cochains with square `1`, finite places only).

This file proves (no sorry; axioms propext, Classical.choice, Quot.sound):

* `leafHasse_of_T14 : BrauerHasse2C → BrauerReciprocity2C → LeafHasse`
* `leafLocalTwo_of_T15 : LocalH2CardC → LeafLocalTwo`
* `b3_degree_le_QM_of_T14_T15`: glue-descent's B2-B3 theorem with `LeafHasse`, `LeafLocalTwo`
  replaced by the announced T14-T15.

The glue is (i) the dictionary `±1 ⊂ ℂˣ` ↔ `ZMod 2` (`sgn`, `unsgn`) between the two cochain
languages, compatible with cocycles, coboundaries and restriction along `G_{ℚ_p} → G_ℚ` (both
sides use the same Mathlib map `Field.absoluteGaloisGroup.map (algebraMap ℚ ℚ_[p])`), and
(ii) the real place: a class trivial at every finite prime is trivial at `∞` by reciprocity
(the parity of the number of ramified places).

In the draft, the definitions of `PkgI6` and glue-descent's files were verbatim copies; here
they are imported from `Conductor/I6Base.lean` and `Descent/*.lean`.
-/

/-! The `PkgI6` cochain definitions and leaves are imported from
`ZInQKernel.HDecomp.Conductor.I6Base`. -/

noncomputable section

namespace GlueWP3

open GlueDescent.B2 GlueDescent.B2Q PkgI6

/-! ## The dictionary `ZMod 2` ↔ `±1 ⊂ ℂˣ` -/

/-- `ZMod 2 → ±1 ⊂ ℂˣ`, `0 ↦ 1`, `1 ↦ -1`. -/
def sgn (a : ZMod 2) : ℂˣ := if a = 0 then 1 else -1

/-- `±1 → ZMod 2`, `1 ↦ 0`, anything else `↦ 1`. -/
def unsgn (s : ℂˣ) : ZMod 2 := if s = 1 then 0 else 1

theorem zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem sgn_zero : sgn 0 = 1 := by simp [sgn]

theorem sgn_one : sgn 1 = -1 := by simp [sgn]

theorem neg_one_ne_one : (-1 : ℂˣ) ≠ 1 := by
  intro h
  have := congrArg (fun u : ℂˣ => (u : ℂ)) h
  norm_num at this

theorem sgn_add (a b : ZMod 2) : sgn (a + b) = sgn a * sgn b := by
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · simp [sgn]
  · simp [sgn]
  · simp [sgn]
  · have : (1 + 1 : ZMod 2) = 0 := by decide
    rw [this, sgn_zero, sgn_one]; simp

theorem sgn_neg (a : ZMod 2) : sgn (-a) = sgn a := by
  rcases zmod2_cases a with rfl | rfl
  · simp
  · have : (-1 : ZMod 2) = 1 := by decide
    rw [this]

theorem sgn_sub (a b : ZMod 2) : sgn (a - b) = sgn a * sgn b := by
  rw [sub_eq_add_neg, sgn_add, sgn_neg]

theorem sgn_sq (a : ZMod 2) : sgn a ^ 2 = 1 := by
  rcases zmod2_cases a with rfl | rfl <;> simp [sgn]

theorem sgn_inv (a : ZMod 2) : (sgn a)⁻¹ = sgn a := by
  rw [inv_eq_iff_mul_eq_one, ← sq, sgn_sq]

theorem sgn_injective : Function.Injective sgn := by
  intro a b h
  rcases zmod2_cases a with rfl | rfl <;> rcases zmod2_cases b with rfl | rfl
  · rfl
  · rw [sgn_zero, sgn_one] at h; exact absurd h.symm neg_one_ne_one
  · rw [sgn_zero, sgn_one] at h; exact absurd h neg_one_ne_one
  · rfl

theorem sgn_eq_one_iff (a : ZMod 2) : sgn a = 1 ↔ a = 0 := by
  rw [← sgn_zero]; exact sgn_injective.eq_iff

/-- A unit of `ℂ` with square `1` is `±1`. -/
theorem sq_eq_one_cases {s : ℂˣ} (h : s ^ 2 = 1) : s = 1 ∨ s = -1 := by
  have h' : (s : ℂ) * s = 1 := by
    have := congrArg (fun u : ℂˣ => (u : ℂ)) h
    simpa [sq] using this
  rcases mul_self_eq_one_iff.mp h' with h1 | h1
  · left; exact Units.ext h1
  · right; exact Units.ext (by simpa using h1)

theorem sgn_unsgn {s : ℂˣ} (h : s ^ 2 = 1) : sgn (unsgn s) = s := by
  rcases sq_eq_one_cases h with rfl | rfl
  · simp [unsgn, sgn]
  · simp [unsgn, sgn]

/-! ## Cocycles and coboundaries correspond -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- Push a `ZMod 2` cochain to a sign cochain. -/
def sgnC (ε : G → G → ZMod 2) : G → G → ℂˣ := fun x y => sgn (ε x y)

/-- Pull a sign cochain back to a `ZMod 2` cochain. -/
def unsgnC (η : G → G → ℂˣ) : G → G → ZMod 2 := fun x y => unsgn (η x y)

theorem sgnC_unsgnC {η : G → G → ℂˣ} (h : ∀ x y, η x y ^ 2 = 1) : sgnC (unsgnC η) = η := by
  funext x y; exact sgn_unsgn (h x y)

theorem isCocycle2_iff (ε : G → G → ZMod 2) : IsCocycle2 ε ↔ IsSignCocycle (sgnC ε) := by
  constructor
  · rintro ⟨hc, hcoc⟩
    refine ⟨?_, fun x y => sgn_sq _, fun x y z => ?_⟩
    · have : IsLocallyConstant (fun x : G × G => ε x.1 x.2) :=
        (IsLocallyConstant.iff_continuous _).mpr hc
      exact this.comp sgn
    · -- `ε y z - ε (xy) z + ε x (yz) - ε x y = 0`
      have h := congrArg sgn (hcoc x y z)
      rw [sgn_sub, sgn_add, sgn_sub, sgn_zero] at h
      simp only [sgnC]
      have e1 := sgn_inv (ε (x * y) z)
      have e2 := sgn_inv (ε x y)
      calc sgn (ε (x * y) z) * sgn (ε x y)
          = sgn (ε (x * y) z) * sgn (ε x y) *
            (sgn (ε y z) * sgn (ε (x * y) z) * sgn (ε x (y * z)) * sgn (ε x y)) := by
            rw [h, mul_one]
        _ = sgn (ε y z) * sgn (ε x (y * z)) *
            ((sgn (ε (x * y) z) * sgn (ε (x * y) z)) * (sgn (ε x y) * sgn (ε x y))) := by ac_rfl
        _ = sgn (ε y z) * sgn (ε x (y * z)) := by
            rw [← sq, ← sq, sgn_sq, sgn_sq, one_mul, mul_one]
  · rintro ⟨hl, -, hcoc⟩
    refine ⟨?_, fun a b c => ?_⟩
    · have hl' : IsLocallyConstant (fun x : G × G => ε x.1 x.2) := by
        have := hl.comp unsgn
        have e : (unsgn ∘ Function.uncurry (sgnC ε)) = fun x : G × G => ε x.1 x.2 := by
          funext ⟨x, y⟩
          show unsgn (sgn (ε x y)) = ε x y
          rcases zmod2_cases (ε x y) with h | h <;> rw [h] <;> simp [sgn, unsgn]
        rwa [e] at this
      exact hl'.continuous
    · apply sgn_injective
      rw [sgn_sub, sgn_add, sgn_sub, sgn_zero]
      have h := hcoc a b c
      simp only [sgnC] at h
      calc sgn (ε b c) * sgn (ε (a * b) c) * sgn (ε a (b * c)) * sgn (ε a b)
          = (sgn (ε b c) * sgn (ε a (b * c))) * (sgn (ε (a * b) c) * sgn (ε a b)) := by ac_rfl
        _ = (sgn (ε (a * b) c) * sgn (ε a b)) * (sgn (ε (a * b) c) * sgn (ε a b)) := by rw [h]
        _ = 1 := by rw [← sq, mul_pow, sgn_sq, sgn_sq, mul_one]

theorem isCoboundary2_iff (ε : G → G → ZMod 2) : IsCoboundary2 ε ↔ SignCob (sgnC ε) := by
  constructor
  · rintro ⟨f, hf, he⟩
    refine ⟨fun x => sgn (f x), ((IsLocallyConstant.iff_continuous f).mpr hf).comp sgn,
      fun x => sgn_sq _, fun x y => ?_⟩
    simp only [sgnC, dB, he, sgn_add, sgn_sub, sgn_inv]
    ac_rfl
  · rintro ⟨γ, hγl, hγs, he⟩
    refine ⟨fun x => unsgn (γ x), (hγl.comp unsgn).continuous, fun a b => ?_⟩
    apply sgn_injective
    have h := he a b
    simp only [sgnC, dB] at h
    have hi : (γ (a * b))⁻¹ = γ (a * b) :=
      inv_eq_of_mul_eq_one_right (by rw [← sq, hγs])
    rw [h, sgn_add, sgn_sub, sgn_unsgn (hγs a), sgn_unsgn (hγs b), sgn_unsgn (hγs (a * b)), hi]
    ac_rfl

/-- Every sign cocycle is `sgnC` of a `ZMod 2` cocycle. -/
theorem exists_of_isSignCocycle {η : G → G → ℂˣ} (h : IsSignCocycle η) :
    ∃ ε : G → G → ZMod 2, IsCocycle2 ε ∧ η = sgnC ε :=
  ⟨unsgnC η, by rw [isCocycle2_iff, sgnC_unsgnC h.2.1]; exact h, (sgnC_unsgnC h.2.1).symm⟩

end Generic

/-- Restriction commutes with the dictionary: glue-descent's `pull (resp p)` is pkg-I6's
`resC ℚ_[p]` (the same Mathlib map). -/
theorem pull_resp_sgnC (p : Nat.Primes) (ε : GQ → GQ → ZMod 2) :
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    pull (resp p) (sgnC ε) = sgnC (resC ℚ_[(p : ℕ)] ε) := rfl

/-! ## The two leaves -/

/-- The real place from reciprocity: a `ZMod 2` cocycle of `G_ℚ` that is a coboundary at every
finite prime is a coboundary at `∞` (the number of places where it is locally nontrivial is
even, and there are none at finite primes). -/
theorem real_of_finite (hR : BrauerReciprocity2C) (ε : GQ → GQ → ZMod 2) (hε : IsCocycle2 ε)
    (hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε)) :
    IsCoboundary2 (resC ℝ ε) := by
  classical
  obtain ⟨-, hev⟩ := hR ε hε
  have hempty : {q : Nat.Primes | haveI : Fact (q : ℕ).Prime := ⟨q.2⟩;
      ¬ IsCoboundary2 (resC ℚ_[(q : ℕ)] ε)} = ∅ := by
    ext q
    have : Fact (q : ℕ).Prime := ⟨q.2⟩
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact hp q
  rw [hempty, Set.ncard_empty, zero_add] at hev
  by_contra hne
  rw [if_neg hne] at hev
  exact Nat.not_even_one hev

/-- **glue-descent's `LeafHasse` from T14** (`BrauerHasse2C` and `BrauerReciprocity2C`). -/
theorem leafHasse_of_T14 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C) : LeafHasse := by
  intro η hη hloc
  obtain ⟨ε, hε, rfl⟩ := exists_of_isSignCocycle hη
  have hp : ∀ (p : ℕ) [Fact p.Prime], IsCoboundary2 (resC ℚ_[p] ε) := by
    intro p hpp
    rw [isCoboundary2_iff]
    exact hloc ⟨p, hpp.out⟩
  rw [← isCoboundary2_iff]
  exact hH ε hε (real_of_finite hR ε hε hp) hp

/-- **glue-descent's `LeafLocalTwo` from T15** (`LocalH2CardC`, its finite-place half; the
existence of a nontrivial class and the real place are not used). -/
theorem leafLocalTwo_of_T15 (hC : LocalH2CardC) : LeafLocalTwo := by
  intro p η₁ η₂ h₁ h₂ hn₁ hn₂
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  obtain ⟨ε₁, hε₁, rfl⟩ := exists_of_isSignCocycle h₁
  obtain ⟨ε₂, hε₂, rfl⟩ := exists_of_isSignCocycle h₂
  rw [← isCoboundary2_iff] at hn₁ hn₂
  have h := (hC.1 p).2 ε₁ ε₂ hε₁ hε₂ hn₁ hn₂
  rw [isCoboundary2_iff] at h
  have e : (fun x y => sgnC ε₁ x y * (sgnC ε₂ x y)⁻¹) = sgnC (ε₁ - ε₂) := by
    funext x y
    simp only [sgnC, Pi.sub_apply, sgn_sub, sgn_inv]
  rw [e]
  exact h

/-! ## Converses: glue-descent's forms say no more than the announced leaves -/

/-- `LeafHasse` (finite places only) implies `BrauerHasse2C` outright. -/
theorem brauerHasse2C_of_leafHasse (h : LeafHasse) : BrauerHasse2C := by
  intro ε hε _ hp
  rw [isCoboundary2_iff]
  rw [isCocycle2_iff] at hε
  refine h _ hε fun p => ?_
  have : Fact (p : ℕ).Prime := ⟨p.2⟩
  rw [pull_resp_sgnC, ← isCoboundary2_iff]
  exact hp p

/-- Given reciprocity, `LeafHasse ↔ BrauerHasse2C`. -/
theorem leafHasse_iff (hR : BrauerReciprocity2C) : LeafHasse ↔ BrauerHasse2C :=
  ⟨brauerHasse2C_of_leafHasse, fun hH => leafHasse_of_T14 hH hR⟩

/-- `LeafLocalTwo` is exactly the second half of `H2TwoClasses (G_{ℚ_p})` for every `p`. -/
theorem leafLocalTwo_iff : LeafLocalTwo ↔ ∀ (p : ℕ) [Fact p.Prime],
    ∀ ε₁ ε₂, IsCocycle2 (G := Field.absoluteGaloisGroup ℚ_[p]) ε₁ → IsCocycle2 ε₂ →
      ¬ IsCoboundary2 ε₁ → ¬ IsCoboundary2 ε₂ → IsCoboundary2 (ε₁ - ε₂) := by
  have e : ∀ {G : Type} [Group G] [TopologicalSpace G] (ε₁ ε₂ : G → G → ZMod 2),
      (fun x y => sgnC ε₁ x y * (sgnC ε₂ x y)⁻¹) = sgnC (ε₁ - ε₂) := by
    intro G _ _ ε₁ ε₂
    funext x y
    simp only [sgnC, Pi.sub_apply, sgn_sub, sgn_inv]
  constructor
  · intro h p hp ε₁ ε₂ h₁ h₂ hn₁ hn₂
    rw [isCocycle2_iff] at h₁ h₂
    rw [isCoboundary2_iff] at hn₁ hn₂ ⊢
    rw [← e]
    exact h ⟨p, hp.out⟩ _ _ h₁ h₂ hn₁ hn₂
  · intro h p η₁ η₂ h₁ h₂ hn₁ hn₂
    have : Fact (p : ℕ).Prime := ⟨p.2⟩
    obtain ⟨ε₁, hε₁, rfl⟩ := exists_of_isSignCocycle h₁
    obtain ⟨ε₂, hε₂, rfl⟩ := exists_of_isSignCocycle h₂
    rw [← isCoboundary2_iff] at hn₁ hn₂
    rw [e, ← isCoboundary2_iff]
    exact h p ε₁ ε₂ hε₁ hε₂ hn₁ hn₂

/-! ## B2-B3 from the announced leaves -/

/-- **B2-B3 with the constants from the announced leaves**: glue-descent's
`GlueDescent.B3Q.b3_degree_le_QM` with `LeafHasse`, `LeafLocalTwo` replaced by T14-T15
(`BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`).  The remaining hypotheses
`LeafSqrtCrit` (L-B2c, T16) and `LeafUnramified` (L-B2d) are glue-descent's other leaves. -/
theorem b3_degree_le_QM_of_T14_T15 (hH : BrauerHasse2C) (hR : BrauerReciprocity2C)
    (hC : LocalH2CardC) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (R : ℝ)
    (hRD : (ZInQ.heightD : ℝ) ≤ R) (hRS : ∀ p ∈ S, (p : ℝ) ≤ R) (hR12 : (10 : ℝ) ^ 12 ≤ R)
    (u : ℚ)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (hLD : Module.finrank ℚ L ≤ ZInQ.heightD)
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ GlueDescent.ramSet S u → UnramifiedAt L p)
    (η : GQ →* ℂˣ) (hη : ∀ x, η x ^ 2 = 1) (hηl : IsLocallyConstant η) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
      (L' : IntermediateField ℚ (AlgebraicClosure ℚ)),
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      (∀ x y, β x * β y = ε x y * β (x * y)) ∧
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GlueDescent.B3Q.GQL L' ↔ σ ∈ GlueDescent.B3Q.GQL L ∧ β σ = 1) ∧
      (Module.finrank ℚ L' : ℝ) ≤ ZInQ.heightQ R * ZInQ.contactSupport S u :=
  GlueDescent.B3Q.b3_degree_le_QM (leafHasse_of_T14 hH hR) (leafLocalTwo_of_T15 hC) hSq hUnr
    S hS R hRD hRS hR12 u L hLD ε hε hinf h11 hram η hη hηl

end GlueWP3

end

end GlueWP3Sec

section G0ModFieldSec

/-!
# g0-mod-field: glue steps G2, G4, G7 of the H decomposition (first range of `ModularConstituent`)

Task g0-mod-field (2026-11-13). `ModularConstituent` (scratch/g0-split/Split.lean, piece 10)
covers G2, G4, G7-G16 of docs/research/h-decomposition.md §3. This file takes the range
G2 (fibre field `K`), G4 (Hom field `L`, `[L:ℚ] ≤ D`), G7 (scalar descent to `L'`,
`[L':ℚ] ≤ Q·M`), for `S = S_mul`, `R = D` (the instance `SixContactMin`).

Outputs (`def … : Prop`): `G2Out Y Φ u P` (with `RationalFibre`), `G4Out u P`, `G7Out u P`, and the clause list `G7Data`
with `G7OutUnr u P` (G7 with the twist: `L'` unramified outside `T`), for a `ℚ̄`-object `P` of
`Y₃` over `J(u)` (`FibreCtx`). The descent datum of B1 on the actual `A` is `DescentDatum`
(maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)`, `a_σ`, sign cocycle `ε`).

Proved (no `sorry`, standard axioms):
* `g2Out_of_cover`: G2's bookkeeping (a splitting field of a separable polynomial of degree
  `≤ 324` is Galois of degree `≤ 324!`).
* `descentDatum_of_conjugacy`: B1's normalization (N5 L645-663): conjugacy isogenies with
  rational discrepancy `c` give `a_σ = |ker m_σ|^{-1/4}` and the sign cocycle `ε = sgn c`.
* `g4Out_of_kernelField`: G4's bookkeeping (Hom field `L = E ⊔ K` Galois,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D` by Minkowski's bound, model by base change, B1).
* `g7Out_of_g4Out`, `g7OutUnr_of_g4Out`: G7 = B2-B3 on the actual descent datum
  (`b2_of_leaves`, `GlueB3Unram.unramified_outside_noLeaf`, `b3_of_cochain`, `degree_le_QM`) and the
  model over `L'` (`isModelOver_baseChange`, transitivity of base change).
* `fieldDescent`, `fieldDescentUnr`: the composite G2 → G4 → G7.
* `modularConstituent_of_ranges`: `ModularConstituentG` (part_split's `ModularConstituent` over
  `PkgI3.AbVar`) from this range and the next ranges bundled as `AfterG7`.

Remaining (named Props): `FibreCoverExists` (G2: Prop. TS + Lemma NV), `KernelFieldExists` (G4:
Weil restriction, Galois image in `GL_r(ℤ)`, inertia on the Tate module, the conjugacy isogenies
`ConjugacyData`), `UnramifiedSup` (compositum of unramified fields; STANDARD), the four B2 leaves
of glue-descent (`LeafHasse`, `LeafLocalTwo`, `LeafSqrtCrit`, `LeafUnramified`), and `AfterG7`
(G8-G16, the other two tasks).
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ LeafQM.AV GlueDescent GlueDescent.B2 GlueDescent.B2Q GlueDescent.B3Q

namespace G0ModField

/-- Intermediate fields of `ℚ̄/ℚ`. -/
abbrev IF : Type := IntermediateField ℚ Qbar

/-- `T = S_mul ∪ supp M_{S_mul}(u)`, the ramification set (N5 L528). -/
noncomputable def T (u : ℚ) : Finset ℕ := GlueDescent.ramSet Mult.S_mul u

/-- `A`, an abelian variety over the subfield `L ⊆ ℚ̄`, is a model of the surface of the
`ℚ̄`-object `P`: `A_{ℚ̄} ≅ P.A` as `ℚ̄`-schemes (base change along the inclusion `L ⊆ ℚ̄`). -/
def IsModelOver (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  Nonempty ((A.baseChange Qbar).X ≅ P.A.X)

/-- The algebra `L → L'` for `L ≤ L'`. -/
@[instance_reducible] noncomputable def incAlg {L L' : IF} (h : L ≤ L') : Algebra L L' :=
  (IntermediateField.inclusion h).toRingHom.toAlgebra

/-- **`A/L` is a QM model of `P`**: the base change to `L` of the abelian surface of an object
`PK` of `Y₃`'s moduli problem (QM by `𝒪` with level-3 structure) over a subfield `K ≤ L`, itself a
model of `P`'s surface. Such an `A` has good reduction away from `3` (G3,
`LeafQM.AV.QML3.goodReduction`), unlike an arbitrary model (a twist by a cocycle ramified at
`p ∉ T` has bad reduction at `p`), so the later steps (G11, G15) hold for every such `A`. -/
def IsQMModel (L : IF) (A : PkgI3.AbVar L) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (hKL : K ≤ L) (PK : QML3 K), IsModelOver K PK.A P ∧
    A = @PkgI3.AbVar.baseChange K _ PK.A L _ (incAlg hKL)

/-- **The fibre context** (the hypotheses of `ModularConstituent`): moduli data `(Y, Φ, π)` with
R1-R2's clauses, `u ∉ 𝒞`, and a `ℚ̄`-point `y` of `Y₃` carrying the object `P` and lying over
`J(u)`. -/
def FibreCtx (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) : Prop :=
  R1fpProps Y Φ ∧ R2fpProps Y Φ π ∧ u ∉ contactSet ∧
  ∃ y : fieldPt Qbar ⟶ Y, Φ Qbar y = M3.mk P ∧
    π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u))

/-- **A rational fibre over `K`** (Glazer N5 L528: "Choose a fiber `A/K`"): `PK` is an object of
`Y₃` over `K ⊆ ℚ̄` at a `K`-point `yK` whose base change to `ℚ̄` carries `P` (so `yK` lies over the
`ℚ̄`-point of `P`, `Φ` being a bijection), and `PK.A` is a model of `P`'s surface. Unlike an
arbitrary `K`-model (a twist of `PK.A` by a cocycle ramified outside `T` can have bad
reduction there), `PK.A` is the fibre of the universal family and has good reduction away
from `3` (G3). -/
def RationalFibre (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (P : QML3 Qbar) (K : IF)
    (PK : QML3 K) : Prop :=
  (∃ yK : fieldPt K ⟶ Y, Φ K yK = M3.mk PK ∧ Φ Qbar (fieldMap K.val ≫ yK) = M3.mk P) ∧
    IsModelOver K PK.A P

/-! ## The outputs of G2, G4, G7 -/

/-- **G2's output (Lemma PR(i), N5 L524-529).** A finite Galois `K ⊆ ℚ̄` with `[K:ℚ] ≤ F₀ = 324!`,
unramified outside `T`, with a rational fibre `PK/K` over `P` (Glazer: "Choose a fiber `A/K`";
`RationalFibre`). -/
def G2Out (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (K : IF) (_ : FiniteDimensional ℚ K) (_ : IsGalois ℚ K),
    Module.finrank ℚ K ≤ heightF0 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) ∧
    ∃ PK : QML3 K, RationalFibre Y Φ P K PK

/-- `A(ℚ̄)` as an additive group, for `A` over `L ⊆ ℚ̄`. -/
abbrev PtQ (L : IF) (A : PkgI3.AbVar L) : Type := Additive (A.Pt Qbar)

/-- **The descent datum of B1 on the actual `A` (N5 L632-663).** `ε` is a normalized
locally constant sign 2-cocycle of `G_ℚ` inflated from `Gal(L/ℚ)`, and it is the cocycle of `A`:
there are maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` (`μ_σ : ^σA → A` the `B`-linear conjugacy isogeny over
`L`, `σ` acting on coordinates) and reals `a_σ > 0` (`a_σ = (deg μ_σ)^{-1/4}`) with
* `a` inflated from `Gal(L/ℚ)` with `a = 1` on `G_L`,
* `m_σ` the Galois action of `σ` for `σ ∈ G_L` (`μ_σ = 1` there),
* `m_{σk} = m_σ m_k`, `m_{kσ} = m_k m_σ` for `k ∈ G_L` (`μ` inflated from `Gal(L/ℚ)`, defined
  over `L`),
* `m_σ` commutes with every `L`-endomorphism of `A` (`μ_σ` is `B`-linear and `L` is the Hom
  field),
* `m_σ` surjective with finite kernel (an isogeny composed with a bijection),
* `m_σ m_τ = c(σ,τ) m_{στ}` with `c = n/d ∈ ℚ^×` (the discrepancy commutes with `B`), and
  `a_σ a_τ c(σ,τ) = ε(σ,τ) a_{στ}` (N5 L651-660: `ν = aμ`, `ν_σ ^σν_τ = ε ν_{στ}`).
* `m_σ` is algebraic: it is induced by a finite surjective morphism of schemes
  `F_σ : A → A` (`μ_σ`, composed with the identification of the underlying schemes of `^σA` and
  `A`): `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` (G14's trace identities reduce `F_σ` modulo primes).
The maps `m_σ` are on points, hence independent of `ℓ`; on `V_ℓ(A)` they give G8's
`ρ_ℓ(σ) = β(σ)⁻¹ a_σ μ_σ σ` (N5 L725-727). -/
def DescentDatum (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) : Prop :=
  IsSignCocycle ε ∧ InflatedFrom L ε ∧ ε 1 1 = 1 ∧
  ∃ (m : GQ → (PtQ L A →+ PtQ L A)) (a : GQ → ℝ),
    (∀ σ, 0 < a σ) ∧
    (∀ σ k : GQ, k ∈ GQL L → a k = 1 ∧ a (σ * k) = a σ ∧ a (k * σ) = a σ) ∧
    (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
        m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
    (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
    (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
        (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
          (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
    (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
    (∀ σ τ, ∃ n d : ℤ, n ≠ 0 ∧ d ≠ 0 ∧ d • (m σ).comp (m τ) = n • m (σ * τ) ∧
        (((a σ * a τ * ((n : ℝ) / d) : ℝ) : ℂ)) = (ε σ τ : ℂ) * ((a (σ * τ) : ℝ) : ℂ)) ∧
    (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
        ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
          Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
            (Additive.toMul x).left ≫ F σ)

/-! ## B1's normalization (proved): from conjugacy isogenies to the sign cocycle -/

/-- The sign of a rational, as `±1 ∈ ℂ^×` (`1` for `q > 0`). -/
noncomputable def sgnU (q : ℚ) : ℂˣ := if 0 < q then 1 else -1

theorem sgnU_sq (q : ℚ) : sgnU q ^ 2 = 1 := by
  unfold sgnU; split_ifs <;> simp

theorem sgnU_mul {q r : ℚ} (hq : q ≠ 0) (hr : r ≠ 0) : sgnU (q * r) = sgnU q * sgnU r := by
  unfold sgnU
  rcases lt_or_gt_of_ne hq with hq' | hq' <;> rcases lt_or_gt_of_ne hr with hr' | hr'
  · rw [if_pos (mul_pos_of_neg_of_neg hq' hr'), if_neg (not_lt.2 hq'.le),
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_neg_of_pos hq' hr').le), if_neg (not_lt.2 hq'.le),
      if_pos hr']; simp
  · rw [if_neg (not_lt.2 (mul_neg_of_pos_of_neg hq' hr').le), if_pos hq',
      if_neg (not_lt.2 hr'.le)]; simp
  · rw [if_pos (mul_pos hq' hr'), if_pos hq', if_pos hr']; simp

/-- `sgn(q)·|q| = q`, in `ℂ`. -/
theorem sgnU_mul_abs (q : ℚ) : ((sgnU q : ℂˣ) : ℂ) * ((|(q : ℝ)| : ℝ) : ℂ) = ((q : ℝ) : ℂ) := by
  unfold sgnU
  split_ifs with h
  · have : (0 : ℝ) < q := by exact_mod_cast h
    rw [abs_of_pos this]; simp
  · have : (q : ℝ) ≤ 0 := by exact_mod_cast not_lt.1 h
    rw [abs_of_nonpos this]; push_cast; ring

/-- **The conjugacy isogenies before normalization (N5 L632-645; the content of G4 + B1's
geometric half).** Maps `m_σ = μ_σ ∘ σ` on `A(ℚ̄)` with the first four clauses of
`DescentDatum`; the discrepancy `c(σ,τ) = n/d ∈ ℚ^×` with `d·m_σ m_τ = n·m_{στ}`, a 2-cocycle
inflated from `Gal(L/ℚ)` with `c(1,1) = 1`; and degree multiplicativity in the form
`|ker m_σ|·|ker m_τ| = c(σ,τ)⁴·|ker m_{στ}|` (`deg μ = |ker μ(ℚ̄)|` in characteristic 0,
`deg[n] = n⁴` on a surface); and algebraicity: `m_σ(x) = F_σ ∘ x ∘ Spec(σ)` for a finite
surjective scheme morphism `F_σ : A → A`. -/
def ConjugacyData (L : IF) (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A))
    (c : GQ → GQ → ℚ) : Prop :=
  (∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ')) ∧
  (∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ)) ∧
  (∀ (σ : GQ) (f : PkgI3.AbVar.End A),
      (m σ).comp (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)) =
        (MonoidHom.toAdditive (PkgI3.AbVar.ptMap (L := Qbar) f)).comp (m σ)) ∧
  (∀ σ, Function.Surjective (m σ) ∧ ((m σ).ker : Set (PtQ L A)).Finite) ∧
  (∀ σ τ, c σ τ ≠ 0 ∧ ∃ n d : ℤ, d ≠ 0 ∧ c σ τ = n / d ∧
      d • (m σ).comp (m τ) = n • m (σ * τ)) ∧
  (∀ σ τ ρ, c (σ * τ) ρ * c σ τ = c τ ρ * c σ (τ * ρ)) ∧
  (∀ σ σ' τ τ' : GQ, (∀ x ∈ L, act σ x = act σ' x) → (∀ x ∈ L, act τ x = act τ' x) →
      c σ τ = c σ' τ') ∧
  c 1 1 = 1 ∧
  (∀ σ τ, (Nat.card (m σ).ker : ℚ) * Nat.card (m τ).ker = c σ τ ^ 4 * Nat.card (m (σ * τ)).ker) ∧
  (∃ F : GQ → (A.X.left ⟶ A.X.left), ∀ σ, IsFinite (F σ) ∧ Surjective (F σ) ∧
      ∀ x : PtQ L A, (Additive.toMul (m σ x)).left =
        Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
          (Additive.toMul x).left ≫ F σ)

/-- The Galois action of `σ' ∈ Aut(ℚ̄/L)` on `A(ℚ̄)` is bijective. -/
theorem galAct_bijective {L : IF} (A : PkgI3.AbVar L) (σ' : Qbar ≃ₐ[L] Qbar) :
    Function.Bijective (A.galAct σ') := by
  have key : ∀ (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar),
      A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
    intro g h P
    show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
    rw [PkgI3.AbVar.galHom_mul, Category.assoc]
  have one : ∀ P : A.Pt Qbar, A.galAct 1 P = P := by
    intro P
    show PkgI3.AbVar.galHom 1 ≫ P = P
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
  refine ⟨fun P Q h => ?_, fun Q => ⟨A.galAct σ'⁻¹ Q, ?_⟩⟩
  · have := congrArg (A.galAct σ'⁻¹) h
    rwa [key, key, inv_mul_cancel, one, one] at this
  · rw [key, mul_inv_cancel, one]

/-- `k ∈ G_L` as an `L`-automorphism of `ℚ̄`. -/
noncomputable def toLAut {L : IF} (k : GQ) (hk : k ∈ GQL L) : Qbar ≃ₐ[L] Qbar :=
  AlgEquiv.ofRingEquiv (f := (act k).toRingEquiv) (fun x => mem_GQL.mp hk x x.2)

theorem toLAut_apply {L : IF} (k : GQ) (hk : k ∈ GQL L) (x : Qbar) : toLAut k hk x = act k x :=
  rfl

/-- The kernel sizes of `m_k`, `m_{σk}`, `m_{kσ}` for `k ∈ G_L` (from the first two clauses of
`ConjugacyData`). -/
theorem card_ker_GL {L : IF} {A : PkgI3.AbVar L} {m : GQ → (PtQ L A →+ PtQ L A)}
    (hgal : ∀ (σ : GQ) (σ' : Qbar ≃ₐ[L] Qbar), (∀ x, σ' x = act σ x) →
      m σ = MonoidHom.toAdditive (A.galAct σ'))
    (hinfl : ∀ σ k : GQ, k ∈ GQL L → m (σ * k) = (m σ).comp (m k) ∧ m (k * σ) = (m k).comp (m σ))
    (σ k : GQ) (hk : k ∈ GQL L) :
    Nat.card (m k).ker = 1 ∧ Nat.card (m (σ * k)).ker = Nat.card (m σ).ker ∧
      Nat.card (m (k * σ)).ker = Nat.card (m σ).ker := by
  have hmk : m k = MonoidHom.toAdditive (A.galAct (toLAut k hk)) :=
    hgal k (toLAut k hk) (toLAut_apply k hk)
  have hbij : Function.Bijective (m k) := by
    rw [hmk]; exact galAct_bijective A (toLAut k hk)
  have hker : (m k).ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : m k x = m k 0 := by rw [map_zero]; exact hx
    exact hbij.1 this
  refine ⟨by rw [hker]; simp, ?_, ?_⟩
  · rw [(hinfl σ k hk).1]
    refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨m k x, x.2⟩) ⟨?_, ?_⟩)
    · intro x y h
      exact Subtype.ext (hbij.1 (congrArg Subtype.val h))
    · rintro ⟨y, hy⟩
      obtain ⟨x, rfl⟩ := hbij.2 y
      exact ⟨⟨x, hy⟩, rfl⟩
  · have hk2 : ((m k).comp (m σ)).ker = (m σ).ker := by
      ext x
      simp only [AddMonoidHom.mem_ker, AddMonoidHom.coe_comp, Function.comp_apply]
      constructor
      · intro h
        have : m k (m σ x) = m k 0 := by rw [map_zero]; exact h
        exact hbij.1 this
      · intro h; rw [h, map_zero]
    rw [(hinfl σ k hk).2, hk2]

/-- `a_σ = |ker m_σ|^{-1/4}` (`= (deg μ_σ)^{-1/4}`, N5 L645). -/
noncomputable def normA {L : IF} {A : PkgI3.AbVar L} (m : GQ → (PtQ L A →+ PtQ L A)) (σ : GQ) :
    ℝ := (Nat.card (m σ).ker : ℝ) ^ (-(1 / 4 : ℝ))

/-- **B1's normalization, proved** (N5 L645-663): from the conjugacy isogenies, `ε = sgn c` is a
normalized locally constant sign cocycle inflated from `Gal(L/ℚ)`, and `(m, a = |ker m|^{-1/4},
ε)` is a descent datum. -/
theorem descentDatum_of_conjugacy (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (A : PkgI3.AbVar L) (m : GQ → (PtQ L A →+ PtQ L A)) (c : GQ → GQ → ℚ)
    (h : ConjugacyData L A m c) : DescentDatum L A (fun σ τ => sgnU (c σ τ)) := by
  obtain ⟨hgal, hinfl, hend, hfin, hc, hcoc, hcinf, hc11, hdeg, halg⟩ := h
  have hkerL := card_ker_GL hgal hinfl
  have hcard : ∀ σ, 0 < Nat.card (m σ).ker := fun σ => by
    haveI : Finite (m σ).ker := (hfin σ).2.to_subtype
    exact Nat.card_pos
  -- the sign cocycle
  have hloc : IsLocallyConstant (Function.uncurry fun σ τ => sgnU (c σ τ)) := by
    refine isLocallyConstant_of_openSubgroup ((GQL L).prod (GQL L))
      (by rw [Subgroup.coe_prod]; exact L.fixingSubgroup_isOpen.prod L.fixingSubgroup_isOpen)
      _ ?_
    rintro ⟨σ, τ⟩ ⟨k₁, k₂⟩ hk
    rw [Subgroup.mem_prod] at hk
    simp only [Function.uncurry_apply_pair, Prod.mk_mul_mk]
    congr 1
    refine (hcinf σ (σ * k₁) τ (τ * k₂) ?_ ?_).symm
    · intro x hx
      show act σ x = act σ (act k₁ x)
      rw [mem_GQL.mp hk.1 x hx]
    · intro x hx
      show act τ x = act τ (act k₂ x)
      rw [mem_GQL.mp hk.2 x hx]
  refine ⟨⟨hloc, fun σ τ => sgnU_sq _, fun σ τ ρ => ?_⟩, ?_, ?_, m, normA m, ?_, ?_, hgal, hinfl,
    hend, hfin, ?_, halg⟩
  · rw [← sgnU_mul (hc _ _).1 (hc _ _).1, ← sgnU_mul (hc _ _).1 (hc _ _).1, hcoc]
  · exact fun σ σ' τ τ' h1 h2 => by simp only [hcinf σ σ' τ τ' h1 h2]
  · show sgnU (c 1 1) = 1
    rw [hc11]; unfold sgnU; simp
  · intro σ; unfold normA; exact Real.rpow_pos_of_pos (by exact_mod_cast hcard σ) _
  · intro σ k hk
    obtain ⟨h1, h2, h3⟩ := hkerL σ k hk
    unfold normA
    rw [h1, h2, h3]
    simp
  · intro σ τ
    obtain ⟨hc0, n, d, hd, hcnd, hnd⟩ := hc σ τ
    have hn : n ≠ 0 := by
      rintro rfl; apply hc0; rw [hcnd]; simp
    refine ⟨n, d, hn, hd, hnd, ?_⟩
    have hx : (0 : ℝ) < Nat.card (m σ).ker := by exact_mod_cast hcard σ
    have hy : (0 : ℝ) < Nat.card (m τ).ker := by exact_mod_cast hcard τ
    have hz : (0 : ℝ) < Nat.card (m (σ * τ)).ker := by exact_mod_cast hcard (σ * τ)
    have hdegR : (Nat.card (m σ).ker : ℝ) * Nat.card (m τ).ker =
        |(c σ τ : ℝ)| ^ 4 * Nat.card (m (σ * τ)).ker := by
      have := congrArg (fun q : ℚ => (q : ℝ)) (hdeg σ τ)
      push_cast at this
      rw [this, pow_abs, abs_of_nonneg (by positivity)]
    have hcR : ((n : ℝ) / d) = (c σ τ : ℝ) := by rw [hcnd]; push_cast; rfl
    have habs : (0 : ℝ) < |(c σ τ : ℝ)| := abs_pos.mpr (by exact_mod_cast hc0)
    have key : normA m σ * normA m τ * |(c σ τ : ℝ)| = normA m (σ * τ) := by
      unfold normA
      rw [← Real.mul_rpow hx.le hy.le, hdegR, Real.mul_rpow (by positivity) hz.le]
      rw [show |(c σ τ : ℝ)| ^ 4 = |(c σ τ : ℝ)| ^ ((4 : ℕ) : ℝ) by norm_cast,
        ← Real.rpow_mul habs.le]
      rw [show ((4 : ℕ) : ℝ) * (-(1 / 4 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
      field_simp
    rw [hcR]
    have e1 : ((normA m σ * normA m τ * (c σ τ : ℝ) : ℝ) : ℂ) =
        ((sgnU (c σ τ) : ℂˣ) : ℂ) * ((normA m σ * normA m τ * |(c σ τ : ℝ)| : ℝ) : ℂ) := by
      have h := sgnU_mul_abs (c σ τ)
      push_cast at h ⊢
      linear_combination (-((normA m σ : ℂ) * (normA m τ : ℂ))) * h
    rw [e1, key]

/-! ## Sanity check: `DescentDatum` is satisfiable (an abelian variety over `ℚ`, `ε = 1`) -/

theorem mem_GQL_bot (σ : GQ) : σ ∈ GQL (⊥ : IF) := by
  rw [mem_GQL]
  intro x hx
  obtain ⟨r, rfl⟩ := IntermediateField.mem_bot.mp hx
  exact (act σ).commutes r

theorem galAct_mul {L : IF} (A : PkgI3.AbVar L) (g h : Qbar ≃ₐ[L] Qbar) (P : A.Pt Qbar) :
    A.galAct g (A.galAct h P) = A.galAct (g * h) P := by
  show PkgI3.AbVar.galHom g ≫ PkgI3.AbVar.galHom h ≫ P = PkgI3.AbVar.galHom (g * h) ≫ P
  rw [PkgI3.AbVar.galHom_mul, Category.assoc]

/-- **Sanity check (proved).** For every abelian variety `A` over `ℚ` (here `L = ⊥ ⊆ ℚ̄`), the
Galois action itself is a descent datum with `ε = 1`, `a = 1`, `F_σ = id`. So `DescentDatum` is
not contradictory. -/
theorem descentDatum_bot (A : PkgI3.AbVar (⊥ : IF)) : DescentDatum ⊥ A (fun _ _ => 1) := by
  let m : GQ → (PtQ ⊥ A →+ PtQ ⊥ A) := fun σ =>
    MonoidHom.toAdditive (A.galAct (toLAut σ (mem_GQL_bot σ)))
  have hmul : ∀ σ τ : GQ, (m σ).comp (m τ) = m (σ * τ) := by
    intro σ τ
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (A.galAct _ (A.galAct _ (Additive.toMul x))) =
      Additive.ofMul (A.galAct _ (Additive.toMul x))
    rw [galAct_mul]
    rfl
  have hbij : ∀ σ, Function.Bijective (m σ) := fun σ => galAct_bijective A _
  refine ⟨⟨IsLocallyConstant.const 1, fun _ _ => by simp, fun _ _ _ => by simp⟩,
    fun _ _ _ _ _ _ => rfl, rfl, m, fun _ => 1, fun _ => one_pos, fun _ _ _ => ⟨rfl, rfl, rfl⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ σ' h
    have : σ' = toLAut σ (mem_GQL_bot σ) := AlgEquiv.ext h
    rw [this]
  · intro σ k _
    exact ⟨(hmul σ k).symm, (hmul k σ).symm⟩
  · intro σ f
    refine AddMonoidHom.ext fun x => ?_
    show Additive.ofMul (PkgI3.AbVar.galHom _ ≫ (Additive.toMul x ≫ f.hom)) =
      Additive.ofMul ((PkgI3.AbVar.galHom _ ≫ Additive.toMul x) ≫ f.hom)
    rw [Category.assoc]
  · intro σ
    refine ⟨(hbij σ).2, ?_⟩
    have : ((m σ).ker : Set (PtQ ⊥ A)) = {0} := by
      ext x
      simp only [SetLike.mem_coe, AddMonoidHom.mem_ker, Set.mem_singleton_iff]
      constructor
      · intro h; exact (hbij σ).1 (h.trans (map_zero _).symm)
      · rintro rfl; exact map_zero _
    rw [this]; exact Set.finite_singleton 0
  · intro σ τ
    refine ⟨1, 1, one_ne_zero, one_ne_zero, by rw [one_smul, one_smul, hmul], by simp⟩
  · refine ⟨fun _ => 𝟙 _, fun σ => ⟨inferInstance, inferInstance, fun x => ?_⟩⟩
    show (PkgI3.AbVar.galHom (toLAut σ (mem_GQL_bot σ)) ≫ Additive.toMul x).left =
      Spec.map (CommRingCat.ofHom ((act σ : Qbar ≃ₐ[ℚ] Qbar) : Qbar →+* Qbar)) ≫
        (Additive.toMul x).left ≫ 𝟙 _
    erw [Category.comp_id]
    rfl

/-- **G4's output (N5 L532-563 and the B1 normalization L632-663).** A finite Galois `L ⊆ ℚ̄`
(the Hom field) with `[L:ℚ] ≤ D`, unramified outside `T`, a QM model `A/L` of `P` (`IsQMModel`), and
the descent datum `ε` of `A` (`DescentDatum`). -/
def G4Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L),
    Module.finrank ℚ L ≤ heightD ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
    ∃ (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ), IsQMModel L A P ∧ DescentDatum L A ε

/-- **G7's output (B2-B3, N5 L664-716).** The data of G4 (`L`, `A/L`, `ε`), and: a Dirichlet
character `χ` mod `N`, a locally constant cochain `β : G_ℚ → ℂ^×` with `β² = χ` and `∂β = ε`, and
the kernel field `L' ⊇ L` of `β|_{G_L}`: finite Galois, `G_{L'} = G_L ∩ ker β`,
`[L':ℚ] ≤ Q_D · M_{S_mul}(u)`, and the base change `A_{L'}` is a model of `P`'s surface. -/
def G7Out (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ),
    IsQMModel L A P ∧ DescentDatum L A ε ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  ∃ (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
    (∀ x y, β x * β y = ε x y * β (x * y)) ∧
    (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
    (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-! ## Transitivity of base change -/

/-- `(A_{L'})_{ℚ̄} ≅ A_{ℚ̄}` for `L ≤ L' ⊆ ℚ̄` (pasting of pullbacks). -/
noncomputable def baseChangeTrans {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) :
    ((@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)).baseChange Qbar).X ≅
      (A.baseChange Qbar).X := by
  letI := incAlg h
  have hcomp : Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)) ≫
      Spec.map (CommRingCat.ofHom (algebraMap L L')) =
      Spec.map (CommRingCat.ofHom (algebraMap L Qbar)) := by
    rw [← Spec.map_comp]
    congr 1
  exact ((Over.pullbackComp (Spec.map (CommRingCat.ofHom (algebraMap L' Qbar)))
      (Spec.map (CommRingCat.ofHom (algebraMap L L')))).app A.X).symm ≪≫
    eqToIso (congrArg (fun f => (Over.pullback f).obj A.X) hcomp)

theorem isModelOver_baseChange {L L' : IF} (h : L ≤ L') (A : PkgI3.AbVar L) (P : QML3 Qbar)
    (hA : IsModelOver L A P) :
    IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg h)) P := by
  obtain ⟨e⟩ := hA
  exact ⟨baseChangeTrans h A ≪≫ e⟩

theorem IsQMModel.isModelOver {L : IF} {A : PkgI3.AbVar L} {P : QML3 Qbar}
    (h : IsQMModel L A P) : IsModelOver L A P := by
  obtain ⟨K, hKL, PK, hPK, rfl⟩ := h
  exact isModelOver_baseChange hKL PK.A P hPK

/-! ## G7 from G4 (proved) -/

/-- `max S_mul ≤ D` (copied from `ZInQKernel/Main.lean`, `ZInQ.Mult.le_heightD_of_mem_S_mul`). -/
theorem le_heightD_of_mem_S_mul {p : ℕ} (hp : p ∈ Mult.S_mul) : p ≤ heightD :=
  (Mult.le_R_of_mem_S_mul hp).trans_eq ((Size.R_eq_D catalogueBound8).trans Mult.D_eq_heightD)

theorem admissible_S_mul :
    (∀ p ∈ Mult.S_mul, p.Prime) ∧ (∀ p ∈ Mult.S_mul, (p : ℝ) ≤ (heightD : ℝ)) ∧
      (10 : ℝ) ^ 12 ≤ (heightD : ℝ) :=
  ⟨fun _ hp => Mult.prime_of_mem_S_mul hp,
   fun _ hp => by exact_mod_cast le_heightD_of_mem_S_mul hp,
   by exact_mod_cast Compiler.Precision.ten_pow_twelve_le_heightD⟩

/-- **G7 (B2-B3 on the actual descent datum), proved** from G4's output and glue-descent's four
B2 leaves, by `GlueDescent.B3Q.b3_degree_le_QM` at `S = S_mul`, `R = D`, `η = 1`. -/
theorem g7Out_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  obtain ⟨N, hN, χ, β, L', hβl, hβs, hβe, hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_degree_le_QM hHasse hTwo hSq hUnr Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u L hLD
      ε hε hinf h11 hram 1 (fun _ => by simp) (IsLocallyConstant.const 1)
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, isModelOver_baseChange hle A P hA.isModelOver⟩

/-! ## G7 with the twist: `L'` unramified outside `T` (proved) -/

/-- **B2 over `G_ℚ` with the level of `χ` exposed** (the proof of
`GlueDescent.B2Q.b2_of_leaves`, copied; the only change is the extra output
`N = chiLevel T₋ = ∏_{p ∈ T₋} lev p` with `T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`). -/
theorem b2_of_leaves_level (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified)
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε)
    (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime)
    (hram : ∀ p : Nat.Primes, (p : ℕ) ∉ T → UnramifiedAt L p) :
    ∃ (N : ℕ) (hN : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ),
      (∃ Tm ⊆ T, N = chiLevel Tm) ∧
      (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T) ∧
      orderOf χ ≤ 2 * ∏ p ∈ T.filter (· ≠ 2), (p - 1) ∧
      IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
      ∀ x y, β x * β y = ε x y * β (x * y) := by
  classical
  let Tm := T.filter (fun p => ∃ hp : p.Prime, ¬ SignCob (pull (resp ⟨p, hp⟩) ε))
  have hloc : ∀ p : Nat.Primes, ¬ SignCob (pull (resp p) ε) ↔ (p : ℕ) ∈ Tm := by
    intro p
    constructor
    · intro h
      refine Finset.mem_filter.2 ⟨?_, p.2, h⟩
      by_contra hpT
      exact h (hUnr L ε hε hinf p (hram p hpT))
    · intro h
      obtain ⟨_, hp, h'⟩ := Finset.mem_filter.1 h
      exact h'
  have hTmP : ∀ q ∈ Tm, q.Prime := fun q hq => hT q (Finset.filter_subset _ _ hq)
  haveI hN : NeZero (chiLevel Tm) := ⟨(chiLevel_pos Tm hTmP).ne'⟩
  obtain ⟨_, hsupp, hord⟩ := exists_chi T Tm hT (Finset.filter_subset _ _)
  let χ := chi Tm
  let β₀ : GQ → ℂˣ := fun x => sqrtU (galChar χ x)
  have hβ₀ : ∀ x, β₀ x ^ 2 = galChar χ x := fun x => sqrtU_sq _
  have hl : IsLocallyConstant β₀ := (galChar_isLocallyConstant χ).comp sqrtU
  have agree : ∀ p : Nat.Primes,
      SignCob (pull (resp p) ε) ↔ SignCob (pull (resp p) (dB β₀)) := by
    intro p
    rw [pull_dB, signCob_dB_iff ((galChar χ).comp (resp p)) (β₀ ∘ resp p) (fun x => hβ₀ _)
      (hl.comp_continuous (resp_continuous p))]
    obtain ⟨u, hu1, hu2⟩ := exists_crt_unit (chiLevel Tm) p p.2
    have hsq := hSq p (chiLevel Tm) χ u hu1 hu2
    have hsq' : (∃ φ : GQp p →* ℂˣ, IsLocallyConstant φ ∧
        ∀ x, φ x ^ 2 = ((galChar χ).comp (resp p)) x) ↔ χ.toUnitHom u = 1 := hsq
    rw [hsq', chi_toUnitHom_crt Tm hTmP p p.2 u hu1 hu2]
    by_cases h : (p : ℕ) ∈ Tm
    · rw [if_pos h]
      have hne : (-1 : ℂˣ) ≠ 1 := by
        intro h1
        have := congrArg (fun z : ℂˣ => (z : ℂ)) h1
        norm_num at this
      constructor
      · intro hc; exact absurd hc ((hloc p).mpr h)
      · intro h1; exact absurd h1 hne
    · rw [if_neg h]
      simp only [iff_true]
      by_contra hc
      exact h ((hloc p).mp hc)
  obtain ⟨β, hβl, hβs, hβe⟩ := exists_beta (G := GQ) GQp resp resp_continuous hHasse hTwo ε hε
    (galChar χ) β₀ hβ₀ hl agree
  exact ⟨chiLevel Tm, hN, χ, β, ⟨Tm, Finset.filter_subset _ _, rfl⟩, hsupp, hord, hβl, hβs, hβe⟩

/-- **B3 from a given B2 cochain** (the proof of `GlueDescent.B3Q.b3_of_leaves`, copied, with
`b2_of_leaves`' output taken as hypotheses so that the twist `η` may depend on it). -/
theorem b3_of_cochain
    (L : IntermediateField ℚ (AlgebraicClosure ℚ)) [FiniteDimensional ℚ L] [IsGalois ℚ L]
    (ε : GQ → GQ → ℂˣ) (hε : IsSignCocycle ε) (hinf : InflatedFrom L ε) (h11 : ε 1 1 = 1)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (β₁ : GQ → ℂˣ) (hβl₁ : IsLocallyConstant β₁)
    (hβs₁ : ∀ x, β₁ x ^ 2 = galChar χ x) (hβe₁ : ∀ x y, β₁ x * β₁ y = ε x y * β₁ (x * y))
    (tw : GQ →* ℂˣ) (htw : ∀ x, tw x ^ 2 = 1) (htwl : IsLocallyConstant tw) :
    ∃ L' : IntermediateField ℚ (AlgebraicClosure ℚ),
      L ≤ L' ∧ FiniteDimensional ℚ L' ∧ IsGalois ℚ L' ∧
      (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β₁ σ * tw σ = 1) ∧
      Module.finrank ℚ L' ≤ 2 * orderOf χ * Module.finrank ℚ L := by
  let β : GQ → ℂˣ := fun x => β₁ x * tw x
  have hβl : IsLocallyConstant β := hβl₁.mul htwl
  have hβs : ∀ x, β x ^ 2 = galChar χ x := twist_sq (galChar χ) hβs₁ tw htw
  have hβe : ∀ x y, β x * β y = ε x y * β (x * y) := twist hβe₁ tw
  have hεN := inflatedNormalized_of L ε hε hinf h11
  have hβ : IsCochainFor ε β := hβe
  let K' : Subgroup GQ := kernelSubgroup hβ hεN
  have hHopen : IsOpen ((GQL L : Subgroup GQ) : Set GQ) := L.fixingSubgroup_isOpen
  have hK'set : (K' : Set GQ) = (GQL L : Set GQ) ∩ β ⁻¹' {1} := by
    ext g
    simp only [SetLike.mem_coe, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]
    exact mem_kernelSubgroup hβ hεN
  have hK'open : IsOpen (K' : Set GQ) := by
    rw [hK'set]; exact hHopen.inter (hβl.isOpen_fiber 1)
  have hK'closed : IsClosed (K' : Set GQ) := Subgroup.isClosed_of_isOpen K' hK'open
  let K'c : ClosedSubgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :=
    { toSubgroup := K', isClosed' := hK'closed }
  let L' : IntermediateField ℚ (AlgebraicClosure ℚ) := IntermediateField.fixedField K'
  have hfix : L'.fixingSubgroup = K' := InfiniteGalois.fixingSubgroup_fixedField K'c
  have hGL' : ∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1 := by
    intro σ
    show σ ∈ L'.fixingSubgroup ↔ _
    rw [hfix]
    exact mem_kernelSubgroup hβ hεN
  have hm := orderOf_pos_dirichlet χ
  have hpow : ∀ s ∈ GQL L, β s ^ (2 * orderOf χ) = 1 := by
    intro s _
    rw [pow_mul, hβs]
    show (MulChar.mulEquivToUnitHom χ (cyc N s)) ^ orderOf χ = 1
    rw [← MonoidHom.pow_apply, ← map_pow, pow_orderOf_eq_one, map_one, MonoidHom.one_apply]
  haveI : (GQL L).Normal := (InfiniteGalois.normal_iff_isGalois L).mpr inferInstance
  have hidx := index_kernel_le hβ hεN (2 * orderOf χ) (by positivity) hpow
  have hfd : FiniteDimensional ℚ L' :=
    (InfiniteGalois.isOpen_iff_finite L').mp (by rw [hfix]; exact hK'open)
  have hL : Module.finrank ℚ L = (GQL L).index := IntermediateField.finrank_eq_fixingSubgroup_index
      (L := L)
  have hL' : Module.finrank ℚ L' = K'.index := by
    rw [IntermediateField.finrank_eq_fixingSubgroup_index (L := L'), hfix]
    rfl
  have hgal : IsGalois ℚ L' :=
    (InfiniteGalois.normal_iff_isGalois L').mp (by rw [hfix]; exact kernelSubgroup_normal hβ hεN)
  have hle : L ≤ L' := by
    intro x hx
    show x ∈ IntermediateField.fixedField K'
    exact fun k => mem_GQL.mp (kernelSubgroup_le hβ hεN k.2) x hx
  refine ⟨L', hle, hfd, hgal, hGL', ?_⟩
  rw [hL', hL]; exact hidx

theorem two_mem_T (u : ℚ) : 2 ∈ T u :=
  Finset.mem_union_left _ (Mult.mem_S_mul_of_le Nat.prime_two (by norm_num))

/-- **The data of G7, clause by clause** (the interface handed to G8-G16). For the fibre `P`
over `J(u)`: the Hom field `L` (finite Galois, unramified outside `T`), the model `A/L` with its
descent datum `ε` (B1), the Dirichlet character `χ` mod `N` (`N = ∏_{p ∈ T₋} lev p` for some
`T₋ ⊆ T`, `lev 2 = 4`, `lev p = p`: `χ` is a product of odd characters mod `p` and mod `4`, N5
L677-683, which bounds the conductor of `β` at every prime, as G15 needs), the
cochain `β` (locally constant, `β² = χ`, `∂β = ε`, twisted so that inertia outside `T` dies), and
the kernel field `L' ⊇ L` of `β|_{G_L}`: `G_{L'} = G_L ∩ ker β`, `[L':ℚ] ≤ Q_D·M_{S_mul}(u)`,
`L'` unramified outside `T` (Galois form), and `A_{L'}` a model of `P`'s surface. -/
def G7Data (u : ℚ) (P : QML3 Qbar) (L : IF) (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ)
    [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF) (hLL' : L ≤ L') : Prop :=
  IsQMModel L A P ∧ DescentDatum L A ε ∧
  (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt L p) ∧
  (∀ q : ℕ, q.Prime → q ∣ N → q ∈ T u) ∧
  (∃ Tm ⊆ T u, N = chiLevel Tm) ∧
  IsLocallyConstant β ∧ (∀ x, β x ^ 2 = galChar χ x) ∧
  (∀ x y, β x * β y = ε x y * β (x * y)) ∧
  (∀ σ : GQ, σ ∈ GQL L' ↔ σ ∈ GQL L ∧ β σ = 1) ∧
  (Module.finrank ℚ L' : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
  GlueB3Unram.GalUnramifiedOutside L' (T u) ∧
  IsModelOver L' (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) P

/-- **G7's output with the twist** (N5 L702-716): the data of `G7Data` exist. -/
def G7OutUnr (u : ℚ) (P : QML3 Qbar) : Prop :=
  ∃ (L : IF) (_ : FiniteDimensional ℚ L) (_ : IsGalois ℚ L) (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) (_ : NeZero N) (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ)
    (L' : IF) (_ : FiniteDimensional ℚ L') (_ : IsGalois ℚ L') (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL'

/-- **G7 with the twist, proved** from G4's output and the four B2 leaves: B2
(`b2_of_leaves`), the twist killing inertia outside `T` (`GlueB3Unram.unramified_outside_noLeaf`,
no leaf), B3 (`b3_of_cochain`) and the constants (`degree_le_QM`). -/
theorem g7OutUnr_of_g4Out (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit)
    (hUnr : LeafUnramified) (u : ℚ) (P : QML3 Qbar) (h : G4Out u P) : G7OutUnr u P := by
  obtain ⟨L, hfd, hgal, hLD, hram, A, ε, hA, hD⟩ := h
  have ⟨hε, hinf, h11, _⟩ := hD
  obtain ⟨hS, hRS, hR12⟩ := admissible_S_mul
  have hT : ∀ p ∈ T u, p.Prime := by
    intro p hp
    rcases Finset.mem_union.mp hp with h | h
    · exact hS p h
    · exact Nat.prime_of_mem_primeFactors h
  obtain ⟨N, hN, χ, β₁, hlev, hsupp, hord, hβl₁, hβs₁, hβe₁⟩ :=
    b2_of_leaves_level hHasse hTwo hSq hUnr L ε hε hinf (T u) hT hram
  have hεN : ∀ σ τ, σ ∈ L.fixingSubgroup ∨ τ ∈ L.fixingSubgroup → ε σ τ = 1 :=
    inflatedNormalized_of L ε hε hinf h11
  obtain ⟨Q, -, hη, hηl, hunr⟩ := GlueB3Unram.unramified_outside_noLeaf L (T u) (two_mem_T u)
    hram ε hεN χ hsupp β₁ hβl₁ hβs₁ hβe₁
  obtain ⟨L', hle, hfd', hgal', hGL', hdeg⟩ :=
    b3_of_cochain L ε hε hinf h11 χ β₁ hβl₁ hβs₁ hβe₁ _ hη hηl
  have hdegR := degree_le_QM Mult.S_mul hS (heightD : ℝ) le_rfl hRS hR12 u
    (Module.finrank ℚ L) (orderOf χ) hLD hord
  refine ⟨L, hfd, hgal, A, ε, N, hN, χ, fun x => β₁ x * (∏ q ∈ Q, GlueB3Unram.etaP q) x,
    L', hfd', hgal', hle, hA, hD, hram, hsupp, hlev, hβl₁.mul hηl, twist_sq (galChar χ) hβs₁ _ hη,
    twist hβe₁ _, hGL', ?_, hunr L' hGL', isModelOver_baseChange hle A P hA.isModelOver⟩
  calc (Module.finrank ℚ L' : ℝ) ≤ ((2 * orderOf χ * Module.finrank ℚ L : ℕ) : ℝ) := by
        exact_mod_cast hdeg
    _ = 2 * (orderOf χ : ℝ) * Module.finrank ℚ L := by push_cast; ring
    _ ≤ _ := hdegR

theorem g7Out_of_g7OutUnr (u : ℚ) (P : QML3 Qbar) (h : G7OutUnr u P) : G7Out u P := by
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hA, hD, hram, -, -, hβl, hβs,
    hβe, hGL', hdeg, -, hM⟩ := h
  exact ⟨L, hfd, hgal, A, ε, hA, hD, hram, N, hN, χ, β, L', hfd', hgal', hle, hβl, hβs, hβe, hGL',
    hdeg, hM⟩

/-! ## G2's bookkeeping (proved) -/

/-- **G2's input, the fibre cover (Prop. TS + Lemma NV, N5 L509-529; remaining).** There is a
separable `f ∈ ℚ[X]` of degree `≤ 324` (the fibre of the normalized cover of `P¹_u` over `u`)
whose splitting field `K = ℚ(roots of f) ⊆ ℚ̄` is unramified outside `T` and contains the residue
field of the point of `P` (a rational fibre `PK/K`, `RationalFibre`). -/
def FibreCoverOut (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ) (P : QML3 Qbar) :
    Prop :=
  ∃ f : Polynomial ℚ, f.Separable ∧ f.natDegree ≤ 324 ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u →
      UnramifiedAt (IntermediateField.adjoin ℚ (f.rootSet Qbar)) p) ∧
    ∃ PK : QML3 (IntermediateField.adjoin ℚ (f.rootSet Qbar)),
      RationalFibre Y Φ P (IntermediateField.adjoin ℚ (f.rootSet Qbar)) PK

/-- **G2, proved from the fibre cover**: the splitting field is Galois of degree `≤ 324!`
(`GlueRepo.Numerics.splitting_degree_le`). -/
theorem g2Out_of_cover (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (u : ℚ)
    (P : QML3 Qbar) (h : FibreCoverOut Y Φ u P) : G2Out Y Φ u P := by
  obtain ⟨f, hs, hd, hram, A, hA⟩ := h
  have hsp : f.IsSplittingField ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IntermediateField.adjoin_rootSet_isSplittingField (IsAlgClosed.splits _)
  have hfd : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    Polynomial.IsSplittingField.finiteDimensional _ f
  have hgal : IsGalois ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) :=
    IsGalois.of_separable_splitting_field hs
  have hdeg : Module.finrank ℚ (IntermediateField.adjoin ℚ (f.rootSet Qbar)) ≤ heightF0 := by
    rw [(Polynomial.IsSplittingField.algEquiv _ f).toLinearEquiv.finrank_eq]
    exact GlueRepo.Numerics.splitting_degree_le f hs hd
  exact ⟨_, hfd, hgal, hdeg, hram, A, hA⟩

/-! ## G4's bookkeeping (proved) -/

/-- **Compositum of unramified fields (STANDARD; remaining, not in Mathlib v4.35).** If `E`
and `K` are finite over `ℚ` and unramified at `p`, so is `E ⊔ K` (Neukirch, *Algebraic Number
Theory*, I (8.?)/III, UNVERIFIED locator; a prime is unramified in a compositum iff it is in both
factors, for Galois factors). -/
def UnramifiedSup : Prop :=
  ∀ (E K : IF) [FiniteDimensional ℚ E] [FiniteDimensional ℚ K] [IsGalois ℚ E] [IsGalois ℚ K]
    (p : ℕ), UnramifiedAt E p → UnramifiedAt K p → UnramifiedAt (E ⊔ K) p

/-- **G4's input, the kernel field (N5 L540-563 and B1, L632-663; remaining).** For a field `K`
and model `A/K` as in G2's output: `W₀ = Res_{K/ℚ} A` has endomorphism lattice of rank `r ≤ 16F₀²`;
the image of `G_ℚ` on it is a finite subgroup `G ≤ GL_r(ℤ)` with kernel field `E`
(`[E:ℚ] = |G|`), unramified outside `T` (inertia at `p ∉ T` acts trivially on the Tate module of
`W₀`, which has good reduction there); and the base change `A_L` of `A` to the Hom field
`L = E ⊔ K` carries conjugacy isogenies `μ_σ : ^σA → A` over `L`, `B`-linear after the
Skolem-Noether correction, with rational discrepancy (`ConjugacyData`; B1's normalization to a
sign cocycle is proved, `descentDatum_of_conjugacy`). -/
def KernelFieldOut (u : ℚ) (P : QML3 Qbar) (K : IF) (A : PkgI3.AbVar K) : Prop :=
  ∃ (r : ℕ), r ≤ 16 * heightF0 ^ 2 ∧
  ∃ (G : Subgroup (GL (Fin r) ℤ)) (_ : Finite G) (E : IF) (_ : FiniteDimensional ℚ E)
    (_ : IsGalois ℚ E), Module.finrank ℚ E = Nat.card G ∧
    (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt E p) ∧
    ∃ (m : GQ → (PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) →+
        PtQ (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right))))
      (c : GQ → GQ → ℚ),
      ConjugacyData (E ⊔ K) (@PkgI3.AbVar.baseChange K _ A ↥(E ⊔ K) _ (incAlg le_sup_right)) m c

/-- **G4, proved from the kernel field**: `L = E ⊔ K` is finite Galois, unramified outside `T`
(`UnramifiedSup`), `[L:ℚ] ≤ [K:ℚ]·[E:ℚ] ≤ F₀·3^{r²} ≤ D` (Minkowski,
`GlueRepo.TorsionFree.card_le_three_pow`; `GlueRepo.Numerics.a8_field`), `A_L = (PK.A)_L` is a QM
model of `P` (`IsQMModel`), and B1's normalization gives the descent datum
(`descentDatum_of_conjugacy`). -/
theorem g4Out_of_kernelField (hSup : UnramifiedSup) (u : ℚ) (P : QML3 Qbar) (K : IF)
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (hK : Module.finrank ℚ K ≤ heightF0)
    (hramK : ∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) (PK : QML3 K)
    (hPK : IsModelOver K PK.A P) (h : KernelFieldOut u P K PK.A) : G4Out u P := by
  obtain ⟨r, hr, G, hG, E, hfE, hgE, hEG, hramE, m, c, hCD⟩ := h
  have hE : Module.finrank ℚ E ≤ 3 ^ (r ^ 2) := hEG ▸ GlueRepo.TorsionFree.card_le_three_pow G
  have hdeg : Module.finrank ℚ ↥(E ⊔ K) ≤ heightD :=
    GlueRepo.Numerics.a8_field E K Compiler.Precision.heightD_eq hK hE hr
  have : IsGalois ℚ ↥(E ⊔ K) := IsGalois.mk
  exact ⟨E ⊔ K, inferInstance, inferInstance, hdeg,
    fun p hp => hSup E K p (hramE p hp) (hramK p hp), _, _,
    ⟨K, le_sup_right, PK, hPK, rfl⟩, descentDatum_of_conjugacy _ _ m c hCD⟩

/-! ## The remaining glue as Props, and the composite -/

/-- **Remaining (G2): Prop. TS + Lemma NV on the actual fibre** (h-decomposition G2: inputs
R1(d), R2, T1, T2; the valuation case analysis is proved, `GlueRepo.PR.inertia_orders_eq_one_iff`,
and Lemma NV step 2, `LeafQM.AV.residue_unramified_over_branch`). -/
def FibreCoverExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P → FibreCoverOut Y Φ u P

/-- **Remaining (G4 + B1): the kernel field of `Res_{K/ℚ} A` and the descent datum on the Hom
field**, for every field `K` and rational fibre `PK/K` as in G2's output (h-decomposition G4: inputs R2, R3, T6,
R7a, T28; A7 proved, `LeafQM.AV.fibre_conjugates_isomorphic`; B1's algebra proved,
glue-descent `B1Quat`, `Cochain`; uses NoCM (G6) for `End⁰(A_ℚ̄) = B`). -/
def KernelFieldExists : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
    ∀ (K : IF) [FiniteDimensional ℚ K] [IsGalois ℚ K], Module.finrank ℚ K ≤ heightF0 →
      (∀ p : Nat.Primes, (p : ℕ) ∉ T u → UnramifiedAt K p) →
      ∀ PK : QML3 K, RationalFibre Y Φ P K PK → KernelFieldOut u P K PK.A

/-- **G2 → G4 → G7 (proved)**: from the two remaining glue Props and the four B2 leaves, every
fibre context has G7's output. -/
theorem fieldDescent (hCover : FibreCoverExists) (hKer : KernelFieldExists) (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7Out u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7Out_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-- **G2 → G4 → G7 with the twist (proved)**: as `fieldDescent`, with `L'` unramified outside `T`
and the clause list `G7Data`. -/
theorem fieldDescentUnr (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar) (hctx : FibreCtx Y Φ π u P) : G7OutUnr u P := by
  obtain ⟨K, hfK, hgK, hK, hramK, PK, hPK⟩ := g2Out_of_cover Y Φ u P (hCover Y Φ π u P hctx)
  exact g7OutUnr_of_g4Out hHasse hTwo hSq hUnr u P
    (g4Out_of_kernelField hSup u P K hK hramK PK hPK.2 (hKer Y Φ π u P hctx K hK hramK PK hPK))

/-! ## How G7's output feeds `ModularConstituent` -/

/-- (copied from scratch/g0-split/part_split.lean, `G0Split.CommonConstituent`, verbatim) The
hypotheses of E1: for some prime `ℓ` and field `E ⊇ ℚ_ℓ`, `V_ℓ(A) ⊗ E` and `V_ℓ(J) ⊗ E` have a
common nonzero constituent, as `G_K`-representations. -/
def CommonConstituent {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) : Prop :=
  ∃ (ℓ : ℕ) (_ : Fact ℓ.Prime) (E : Type) (_ : Field E) (_ : Algebra ℚ_[ℓ] E)
    (U : Subrepresentation (GlueI3.repBaseChange E (A.galRep ℓ)))
    (U' : Subrepresentation (GlueI3.repBaseChange E (J.galRep ℓ)))
    (e : U.toSubmodule ≃ₗ[E] U'.toSubmodule), U ≠ ⊥ ∧
    ∀ g (u : U.toSubmodule),
      (e ⟨GlueI3.repBaseChange E (A.galRep ℓ) g u, U.apply_mem_toSubmodule g u.2⟩ :
        TensorProduct ℚ_[ℓ] E (J.V ℓ)) = GlueI3.repBaseChange E (J.galRep ℓ) g (e u)

/-- A finite-dimensional `L ⊆ ℚ̄` is a number field. -/
theorem numberField_of_fd (L : IF) [FiniteDimensional ℚ L] : NumberField L := ⟨⟩

/-- **`ModularConstituent`** (scratch/g0-split/part_split.lean, piece 10), copied with
def-faltings' copy `ZInQ.DefFaltings.AbVar` and the bridge `LeafAdopt.abVarEquiv` (the identity on
the underlying scheme) replaced by the kernel's `PkgI3.AbVar`, which `ZInQKernel/HDecomp/`
already uses for both. -/
def ModularConstituentG : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (y : fieldPt Qbar ⟶ Y) (P : QML3 Qbar), Φ Qbar y = M3.mk P →
      π.val (K := Qbar) y.left = OnePoint.some (algebraMap ℚ Qbar (ZInQ.JHeight.Jmap u)) →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* Qbar) (A : PkgI3.AbVar L.K) (N : ℕ)
      (J : PkgI3.AbVar ℚ),
      (letI : Algebra L.K Qbar := emb.toAlgebra; Nonempty ((A.baseChange Qbar).X ≅ P.A.X)) ∧
      0 < N ∧ LeafModCurves.IsJ1 N J ∧
      (N : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      (Module.finrank ℚ L.K : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ∧
      CommonConstituent A (J.baseChange L.K)

/-- **The remaining ranges G8-G16 (the next tasks' target), as one Prop.** For every fibre
context and every G7 data (`G7Data`): a level `1 ≤ M ≤ Q_D·M_{S_mul}(u)²`, a `J₁(M)` over `ℚ`, and a
common constituent of `V_ℓ(A_{L'})` and `V_ℓ(J₁(M)_{L'})` as `G_{L'}`-representations (G8: `ρ_ℓ`
from `β`, `a_σ`, `m_σ`; G9-G12: de Rham, odd, modular; G13-G16: newform, level, Eichler-Shimura). -/
def AfterG7 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left) (u : ℚ)
    (P : QML3 Qbar), FibreCtx Y Φ π u P →
  ∀ (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ)
    (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    ∃ (M : ℕ) (J : PkgI3.AbVar ℚ), 0 < M ∧ LeafModCurves.IsJ1 M J ∧
      (M : ℝ) ≤ heightQ heightD * (contactSupport Mult.S_mul u : ℝ) ^ 2 ∧
      @CommonConstituent L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) (J.baseChange L')

/-- **`ModularConstituent` from this range and the next (proved)**: G2, G4, G7 here
(`fieldDescentUnr`) and the ranges G8-G16 as `AfterG7`. -/
theorem modularConstituent_of_ranges (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup)
    (hHasse : LeafHasse) (hTwo : LeafLocalTwo) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG := by
  intro Y Φ π h1 h2 u hu y P hy hπ
  have hctx : FibreCtx Y Φ π u P := ⟨h1, h2, hu, y, hy, hπ⟩
  obtain ⟨L, hfd, hgal, A, ε, N, hN, χ, β, L', hfd', hgal', hle, hdata⟩ :=
    fieldDescentUnr hCover hKer hSup hHasse hTwo hSq hUnr Y Φ π u P hctx
  obtain ⟨M, J, hM, hJ, hMle, hCC⟩ := hRest Y Φ π u P hctx L A ε N χ β L' hle hdata
  haveI : NumberField L' := numberField_of_fd L'
  exact ⟨⟨L'⟩, algebraMap L' Qbar, @PkgI3.AbVar.baseChange L _ A L' _ (incAlg hle), M, J,
    hdata.2.2.2.2.2.2.2.2.2.2.2, hM, hJ, hMle, hdata.2.2.2.2.2.2.2.2.2.1, hCC⟩

/-- **The same, with glue-descent's `LeafHasse`, `LeafLocalTwo` replaced by the bundle's T14-T15**
(`PkgI6.BrauerHasse2C`, `BrauerReciprocity2C`, `LocalH2CardC`; `GlueWP3.leafHasse_of_T14`,
`leafLocalTwo_of_T15`). -/
theorem modularConstituent_of_ranges_T14 (hCover : FibreCoverExists) (hKer : KernelFieldExists)
    (hSup : UnramifiedSup) (hH : PkgI6.BrauerHasse2C) (hR : PkgI6.BrauerReciprocity2C)
    (hC : PkgI6.LocalH2CardC) (hSq : LeafSqrtCrit) (hUnr : LeafUnramified)
    (hRest : AfterG7) : ModularConstituentG :=
  modularConstituent_of_ranges hCover hKer hSup (GlueWP3.leafHasse_of_T14 hH hR)
    (GlueWP3.leafLocalTwo_of_T15 hC) hSq hUnr hRest

/-! ## Feeding g0-mod-galois' inputs (G8-G12): their `G2Out`, `G7Out` -/

namespace GaloisCopy
/-! Copied from scratch/g0-mod-galois/part_galois.lean (branch wip/g0-mod-galois at 20fa1287),
definitions `resQ`, `Vb`, `tate`, `G2Out`, `G7Out`, verbatim (namespace renamed). -/

/-- (copied) The restriction map `G_K → G_ℚ` (Mathlib's `Field.absoluteGaloisGroup.map`). -/
noncomputable def resQ (K : Type) [Field K] [NumberField K] :
    Field.absoluteGaloisGroup K →* PkgI4.GQ :=
  (Field.absoluteGaloisGroup.map (algebraMap ℚ K) :
    Field.absoluteGaloisGroup K →* Field.absoluteGaloisGroup ℚ)

/-- (copied) `ℚ̄_ℓ ⊗_{ℚ_ℓ} V_ℓ(A)`. -/
abbrev Vb {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] : Type :=
  TensorProduct ℚ_[ℓ] (PadicAlgCl ℓ) (A.V ℓ)

/-- (copied) The Tate action of `G_K` on `ℚ̄_ℓ ⊗ V_ℓ(A)`. -/
noncomputable def tate {K : Type} [Field K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Representation (PadicAlgCl ℓ) (Field.absoluteGaloisGroup K) (Vb A ℓ) :=
  GlueI3.repBaseChange (PadicAlgCl ℓ) (A.galRep ℓ)

/-- (copied) g0-mod-galois' input "output of G2": inertia at `p ∉ T` lies in `G_K`. -/
def G2Out (K : Type) [Field K] [NumberField K] (T : Finset ℕ) : Prop :=
  ∀ p : ℕ, p.Prime → p ∉ T → ∀ v : ValuationSubring PkgI4.Qbar, PkgI4.LiesOver v p →
    ∀ σ ∈ v.inertiaSubgroup ℚ, ((σ : v.decompositionSubgroup ℚ) : PkgI4.GQ) ∈ (resQ K).range

/-- (copied) g0-mod-galois' input "output of G7 at the coefficient prime `ℓ`". -/
def G7Out {K : Type} [Field K] [NumberField K] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ) (Vb A ℓ))
    (c ε : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β : PkgI4.GQ → PadicAlgCl ℓ)
    (u : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ) (Vb A ℓ)) : Prop :=
  A.dim = 2 ∧ Module.finrank ℤ (PkgI3.AbVar.End A) = 4 ∧
  (∀ g h, Tm g * Tm h = c g h • Tm (g * h)) ∧
  (∀ g h, a g * a h * c g h = ε g h * a (g * h)) ∧
  (∀ g h, β g * β h = ε g h * β (g * h)) ∧ (∀ g, β g ≠ 0) ∧
  (∀ σ, Tm (resQ K σ) = tate A ℓ σ ∧ a (resQ K σ) = 1 ∧ β (resQ K σ) = 1) ∧
  (∀ g i j, Commute (Tm g) (u.e i j)) ∧
  (∀ (f : Module.Dual (PadicAlgCl ℓ) (Vb A ℓ)) (v : Vb A ℓ),
    Continuous fun g => f (GlueDescent.rho Tm a β g v))

end GaloisCopy

/-- **Bridge 1 (Mathlib-level Galois theory; proved below, `resQRange`).** For a finite Galois `L' ⊆ ℚ̄`, the
image of `resQ L' : G_{L'} → G_ℚ` is `G_{L'} = Fix(L')` (true for every embedding of the
algebraic closures because `L'/ℚ` is normal). -/
def ResQRange : Prop :=
  ∀ (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'],
    (@GaloisCopy.resQ L' _ (numberField_of_fd L')).range = L'.fixingSubgroup

/-- An element of `G_ℚ` as an automorphism of `ℚ̄`. -/
def actQ (τ : Field.absoluteGaloisGroup ℚ) : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ := τ
/-- An element of `G_K` as an automorphism of `\bar K`. -/
def actK {K : Type} [Field K] (σ : Field.absoluteGaloisGroup K) :
    AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K := σ

/-- `resQ K σ` is `σ` transported along the embedding `g : ℚ̄ → \bar K` that
`Field.absoluteGaloisGroup.map` chooses. -/
theorem resQ_comm' (K : Type) [Field K] [NumberField K] :
    ∃ g : AlgebraicClosure ℚ →+* AlgebraicClosure K, ∀ σ x,
      g (actQ (GaloisCopy.resQ K σ) x) = actK σ (g x) := by
  letI : Algebra ℚ K := (algebraMap ℚ K).toAlgebra
  let g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure K := IsAlgClosed.lift
  letI : Algebra (AlgebraicClosure ℚ) (AlgebraicClosure K) := g.toAlgebra
  haveI : IsScalarTower ℚ (AlgebraicClosure ℚ) (AlgebraicClosure K) :=
    IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
  refine ⟨g.toRingHom, fun σ x => ?_⟩
  exact AlgEquiv.restrictNormal_commutes ((AlgEquiv.restrictScalarsHom ℚ) σ) (AlgebraicClosure ℚ) x

/-- **`ResQRange` proved**: for finite Galois `L ⊆ ℚ̄`, the image of `resQ L` is `Fix(L)`
(normality of `L` gives `g(L) = L` inside `\bar L`; `g` is bijective because `\bar L/ℚ` is
algebraic). -/
theorem resQ_range (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] :
    (@GaloisCopy.resQ L _ (numberField_of_fd L)).range = L.fixingSubgroup := by
  haveI := numberField_of_fd L
  obtain ⟨g0, hcomm⟩ := resQ_comm' L
  let g : Qbar →ₐ[ℚ] AlgebraicClosure L := g0.toRatAlgHom
  have hg : ∀ x, g x = g0 x := fun _ => rfl
  -- `g` is bijective (`AlgebraicClosure L` is algebraic over `ℚ`)
  have hKalg : Algebra.IsAlgebraic ℚ (AlgebraicClosure L) := by
    haveI : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
    haveI : Algebra.IsAlgebraic L (AlgebraicClosure L) := AlgebraicClosure.isAlgebraic L
    exact Algebra.IsAlgebraic.trans ℚ L (AlgebraicClosure L)
  have hgbij : Function.Bijective g := by
    letI : Algebra Qbar (AlgebraicClosure L) := g.toAlgebra
    haveI : IsScalarTower ℚ Qbar (AlgebraicClosure L) :=
      IsScalarTower.of_algebraMap_eq (fun x => (g.commutes x).symm)
    haveI : Algebra.IsIntegral ℚ (AlgebraicClosure L) := inferInstance
    haveI : Algebra.IsIntegral Qbar (AlgebraicClosure L) := Algebra.IsIntegral.tower_top ℚ
    exact IsAlgClosed.algebraMap_bijective_of_isIntegral
  let ψ : L →ₐ[ℚ] AlgebraicClosure L := IsScalarTower.toAlgHom ℚ L (AlgebraicClosure L)
  let e : L ≃ₐ[ℚ] ψ.fieldRange := AlgEquiv.ofInjectiveField ψ
  haveI : Normal ℚ ψ.fieldRange := Normal.of_algEquiv e
  let f : ψ.fieldRange →ₐ[ℚ] AlgebraicClosure L := (g.comp L.val).comp e.symm.toAlgHom
  have hf := AlgHom.fieldRange_of_normal f
  have hgL : ∀ x : L, ∃ y : L, g x = ψ y := by
    intro x
    have hx : g x ∈ f.fieldRange := ⟨e x, by simp [f]⟩
    rw [hf] at hx
    obtain ⟨y, hy⟩ := hx
    exact ⟨y, hy.symm⟩
  have hLg : ∀ y : L, ∃ x : L, g x = ψ y := by
    intro y
    have hy : ψ y ∈ f.fieldRange := by rw [hf]; exact ⟨y, rfl⟩
    obtain ⟨z, hz⟩ := hy
    exact ⟨e.symm z, by simpa [f] using hz⟩
  ext τ
  constructor
  · rintro ⟨σ, rfl⟩
    refine (IntermediateField.mem_fixingSubgroup_iff L (actQ (GaloisCopy.resQ L σ))).mpr ?_
    intro x hx
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g x
    rw [hg, hcomm σ x, ← hg]
    obtain ⟨y, hy⟩ := hgL ⟨x, hx⟩
    have hy' : g x = ψ y := hy
    rw [hy']
    exact (actK σ).commutes y
  · intro hτ'
    have hτ := (IntermediateField.mem_fixingSubgroup_iff L (actQ τ)).mp hτ'
    let eg : Qbar ≃+* AlgebraicClosure L := RingEquiv.ofBijective g.toRingHom hgbij
    let τ' : Qbar ≃ₐ[ℚ] Qbar := τ
    let σ₀ : AlgebraicClosure L ≃+* AlgebraicClosure L := (eg.symm.trans τ'.toRingEquiv).trans eg
    have hσ₀ : ∀ x, σ₀ (g x) = g (τ' x) := by
      intro x
      show eg (τ' (eg.symm (eg x))) = g (τ' x)
      rw [RingEquiv.symm_apply_apply]; rfl
    have hfix : ∀ y : L, σ₀ (algebraMap L (AlgebraicClosure L) y) =
        algebraMap L (AlgebraicClosure L) y := by
      intro y
      obtain ⟨x, hx⟩ := hLg y
      have hx' : g x = algebraMap L (AlgebraicClosure L) y := hx
      rw [← hx', hσ₀, show τ' (x : Qbar) = x from hτ x x.2]
    let σ : Field.absoluteGaloisGroup L := AlgEquiv.ofRingEquiv (f := σ₀) hfix
    refine ⟨σ, ?_⟩
    apply AlgEquiv.ext
    intro x
    apply g.toRingHom.injective
    show g (actQ (GaloisCopy.resQ L σ) x) = g (τ' x)
    rw [hg, hcomm σ x, ← hg]
    exact hσ₀ x


theorem resQRange : ResQRange := fun L' _ _ => resQ_range L'

/-- **g0-mod-galois' `G2Out` for `K = L'`, proved** from `G7Data` (B3(v): inertia outside `T`
fixes `L'`) and `ResQRange`. -/
theorem galoisG2Out_of_g7Data (hRes : ResQRange) (u : ℚ) (P : QML3 Qbar) (L : IF)
    (A : PkgI3.AbVar L) (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N)
    (β : GQ → ℂˣ) (L' : IF) [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L')
    (h : G7Data u P L A ε N χ β L' hLL') :
    @GaloisCopy.G2Out L' _ (numberField_of_fd L') (T u) := by
  intro p hp hpT v hv σ hσ
  rw [hRes L']
  have hv' : GlueB3Unram.LiesOver v p := hv
  exact h.2.2.2.2.2.2.2.2.2.2.1 p hp hpT v hv' (Subgroup.mem_map_of_mem _ hσ)

/-- **Bridge 2 (remaining; the Tate functor on the descent datum, §3 of the report).** From G7's
data, the rank-4 endomorphism ring and `dim A_{L'} = 2` (G5-G6, A9; `model_dim`), for every `ℓ`:
operators `Tm σ` (`ℚ̄_ℓ ⊗ T_ℓ(m_σ)` transported to `V_ℓ(A_{L'})`), `c = n/d`, `a`, `ε`, `β` mapped
into `ℚ̄_ℓ` by one embedding of the number field they generate, and matrix units of
`End_{L'}(A) ⊗ ℚ̄_ℓ ≅ M₂(ℚ̄_ℓ)`, satisfying g0-mod-galois' `G7Out`. -/
def TateBridge : Prop :=
  ∀ (u : ℚ) (P : QML3 Qbar) (L : IF) [FiniteDimensional ℚ L] [IsGalois ℚ L] (A : PkgI3.AbVar L)
    (ε : GQ → GQ → ℂˣ) (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (β : GQ → ℂˣ) (L' : IF)
    [FiniteDimensional ℚ L'] [IsGalois ℚ L'] (hLL' : L ≤ L'),
    G7Data u P L A ε N χ β L' hLL' →
    (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')).dim = 2 →
    Module.finrank ℤ (PkgI3.AbVar.End (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL'))) = 4 →
    ∀ (ℓ : ℕ) [Fact ℓ.Prime], ∃ (Tm : PkgI4.GQ → Module.End (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ))
      (c ε' : PkgI4.GQ → PkgI4.GQ → PadicAlgCl ℓ) (a β' : PkgI4.GQ → PadicAlgCl ℓ)
      (uu : GlueDescent.MatrixUnits2 (PadicAlgCl ℓ)
        (GaloisCopy.Vb (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ)),
      @GaloisCopy.G7Out L' _ (numberField_of_fd L')
        (@PkgI3.AbVar.baseChange L _ A L' _ (incAlg hLL')) ℓ _ Tm c ε' a β' uu

end G0ModField
end G0ModFieldSec


/-! ## §3″. g0-thetapoint: `ThetaPointOfFibre` (missing piece 9) from smaller named Props

Task g0-thetapoint, 2026-11-13. `G0Split.ThetaPointOfFibre` (above, unchanged) is proved here
along two routes.

* Route E (`ThetaPt.thetaPointOfFibre_of_qm_ratios`): `ThetaPt.FibreQMPeriod` (GLUE: R1(b) and
  the Hauptmodul comparison on the actual fibre: some uniformization lattice of the fibre is a QM
  lattice `ι(𝒪)(τ, 1)ᵀ` with `j_θ(Ω(τ)) = J(u)`) and `ThetaPt.ThetaRatiosAlgebraic` (LEAF
  candidate: theta-constant ratios at a period matrix of an abelian surface over a number field
  are algebraic numbers). `ThetaRatiosAlgebraic` implies `ThetaPt.ThetaNullAlgebraic` (proved).
* Route A (`ThetaPt.thetaPointOfFibre_of_parts`): `DimBaseChange` (g0-split piece 2, unchanged;
  the model is a surface), `ThetaPt.UniformizationExistsNF` (TEXTBOOK leaf candidate: analytic
  uniformization at some complex place), `ThetaPt.FibreQMPeriodAll` (GLUE: the universal form of
  `FibreQMPeriod`) and `ThetaPt.ThetaNullAlgebraic` (LEAF-COMPOSITE).

Proved glue: the F1 value passes from `ℂ` to the number field (`f1_of_theta`, homogeneity of
degree 0 of `j_θ`), the height comparison (`height_even`, Mathlib's `logHeight_comp_le`; the odd
theta constants are not needed), `Ω(τ) ∈ 𝔥₂` and `Ω(τ)` is a period matrix of every lattice
linearly isomorphic to `ι(𝒪)(τ, 1)ᵀ` (bp-analytic's `ZInQKernel/HDecomp/Analytic/QMLattice.lean`),
the identification of the two copies of `θ_m` and of `Ω(τ)`, and, as a check of the docstring of
`ThetaPointOfFibre`, the vanishing of the six odd theta constants (`thetaConst_odd`). -/

noncomputable section

namespace HSyn

open scoped MatrixGroups ModularForm

namespace G0Split

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ ZInQ.JHeight LeafQM.AV ZInQ.DefFaltings

namespace ThetaPt

-- g0-assemble: in Leaves.lean these R22 objects are leaf-push2's originals (leaf-adopt3 removed
-- g0-split's textual copies `HSyn.G0Split.Char2` etc.), so they are opened here.
open ZInQ.LeafPush2 (CPts cptObj IsUniformization IsSiegel IsPeriodMatrix Char2 thetaConst absLogHeight)

open Complex

/-! ### Definitions and connective lemmas -/

/-- F1's theta expression `j_θ(Ω) = 3779136 (∏_{m even} θ_m(0, Ω))⁴ / (Σ_{m even} θ_m(0, Ω)⁸)⁵`,
with leaf-push2's theta constants (`thetaConst`, as in R22). -/
def jTheta (Ω : Matrix (Fin 2) (Fin 2) ℂ) : ℂ :=
  3779136 * (∏ m ∈ PkgI1.evenChars, thetaConst Ω m) ^ 4 /
    (∑ m ∈ PkgI1.evenChars, thetaConst Ω m ^ 8) ^ 5

/-- An enumeration `Fin 10 ≃ {even characteristics}`. -/
def evenEnum : Fin 10 ≃ PkgI1.evenChars :=
  (PkgI1.evenChars.equivFin.trans (finCongr PkgI1.card_evenChars)).symm

theorem prod_evenEnum {R : Type*} [CommMonoid R] (g : Char2 → R) :
    ∏ i : Fin 10, g (evenEnum i) = ∏ m ∈ PkgI1.evenChars, g m := by
  rw [← Finset.prod_coe_sort]
  exact Equiv.prod_comp evenEnum (fun m : PkgI1.evenChars => g m)

theorem sum_evenEnum {R : Type*} [AddCommMonoid R] (g : Char2 → R) :
    ∑ i : Fin 10, g (evenEnum i) = ∑ m ∈ PkgI1.evenChars, g m := by
  rw [← Finset.sum_coe_sort]
  exact Equiv.sum_comp evenEnum (fun m : PkgI1.evenChars => g m)

/-- leaf-push2's theta constant is pkg-I1's (`2πi·vᵀ(b/2) = πi·vᵀb`); the proof of
`ZInQ.LeafPush2.thetaConst_eq` (ZInQKernel/HDecomp/LeafPush2/Bridge.lean), repeated. -/
theorem thetaConst_eq_pkgI1 (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) :
    thetaConst Ω m = PkgI1.thetaConst m Ω := by
  unfold thetaConst PkgI1.thetaConst
  congr 1
  funext n
  congr 2
  have : (fun i => ((m.2 i : ℕ) : ℂ) / 2) = (1 / 2 : ℂ) • fun i => ((m.2 i : ℕ) : ℂ) := by
    funext i; simp [div_eq_inv_mul]
  rw [this, dotProduct_smul, smul_eq_mul]
  ring

/-- `j_θ = jNum / jDen` in pkg-I1's notation (the function of `PkgI1.QMHauptmodul`). -/
theorem jTheta_eq (Ω : Matrix (Fin 2) (Fin 2) ℂ) :
    jTheta Ω = PkgI1.jNum Ω / PkgI1.jDen Ω := by
  unfold jTheta PkgI1.jNum PkgI1.jDen PkgI1.thetaProd2 PkgI1.thetaSum8
  simp only [thetaConst_eq_pkgI1]
  rw [Finset.prod_pow, ← pow_mul]

/-- pkg-I1's `Ω(τ)` (copied in `Leaves.lean`) is bp-analytic's (the same text). -/
theorem omega_eq (τ : ℂ) : PkgI1.Omega τ = BPAnalytic.QM.Omega τ := rfl

/-- **F1 passes to the number field (glue, proved).** If `emb(z_m) = c·θ_m(Ω)` with `c ≠ 0` and
`j_θ(Ω) = q ∈ ℚ`, then the ten even coordinates of `z` satisfy `Φ(z') = q` in `L` (`j_θ` is
homogeneous of degree `0`: `c⁴⁰` cancels; `emb` is injective). -/
theorem f1_of_theta {L : Type*} [Field L] [CharZero L] (emb : L →+* ℂ)
    (Ω : Matrix (Fin 2) (Fin 2) ℂ) (z : Char2 → L) (c : ℂ) (hc : c ≠ 0)
    (hz : ∀ m, emb (z m) = c * thetaConst Ω m) (q : ℚ) (hJ : jTheta Ω = (q : ℂ)) :
    3779136 * (∏ i, (fun i => z (evenEnum i)) i) ^ 4 /
      (∑ i, (fun i => z (evenEnum i)) i ^ 8) ^ 5 = algebraMap ℚ L q := by
  apply emb.injective
  rw [eq_ratCast (algebraMap ℚ L), map_ratCast, ← hJ]
  simp only [map_div₀, map_mul, map_pow, map_prod, map_sum, map_ofNat, hz]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [mul_pow]
  rw [← Finset.mul_sum, prod_evenEnum (fun m => thetaConst Ω m),
    sum_evenEnum (fun m => thetaConst Ω m ^ 8)]
  unfold jTheta
  set P := ∏ m ∈ PkgI1.evenChars, thetaConst Ω m
  set S := ∑ m ∈ PkgI1.evenChars, thetaConst Ω m ^ 8
  have h40 : c ^ 40 ≠ 0 := pow_ne_zero 40 hc
  calc 3779136 * ((c ^ 10) ^ 4 * P ^ 4) / (c ^ 8 * S) ^ 5
      = c ^ 40 * (3779136 * P ^ 4) / (c ^ 40 * S ^ 5) := by ring
    _ = 3779136 * P ^ 4 / S ^ 5 := mul_div_mul_left _ _ h40

/-- **The height comparison (glue, proved).** Dropping coordinates does not increase the height:
`h(z') ≤ h(z)` for the ten even coordinates `z'` of `z` (Mathlib's `logHeight_comp_le`). -/
theorem height_even {L : Type*} [Field L] [NumberField L] (z : Char2 → L) :
    Height.logHeight (fun i => z (evenEnum i)) / Module.finrank ℚ L ≤ absLogHeight z := by
  unfold absLogHeight
  exact div_le_div_of_nonneg_right (Height.logHeight_comp_le (fun i => (evenEnum i : Char2)) z)
    (Nat.cast_nonneg _)

/-- Transport of `IsPeriodMatrix` along a `ℂ`-linear isomorphism (the proof of
`ZInQ.LeafPush2.isPeriodMatrix_of_map`, repeated). -/
theorem isPeriodMatrix_of_map {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)} {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : IsPeriodMatrix Λ Ω) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hF : Λ.map (F.toLinearMap.restrictScalars ℤ) = Λ') : IsPeriodMatrix Λ' Ω := by
  obtain ⟨T, hT⟩ := h
  refine ⟨F.symm.trans T, fun z => ?_⟩
  have hz : z ∈ Λ' ↔ F.symm z ∈ Λ := by
    rw [← hF, Submodule.mem_map]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hy
      exact ⟨F.symm z, hy, by simp⟩
  rw [hz, hT]
  rfl

/-- The converse transport: if `F` maps `Λ` onto `Λ'`, a period matrix of `Λ'` is one of `Λ`. -/
theorem isPeriodMatrix_of_comap {Λ Λ' : Submodule ℤ (Fin 2 → ℂ)} {Ω : Matrix (Fin 2) (Fin 2) ℂ}
    (h : IsPeriodMatrix Λ' Ω) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ))
    (hF : Λ.map (F.toLinearMap.restrictScalars ℤ) = Λ') : IsPeriodMatrix Λ Ω := by
  refine isPeriodMatrix_of_map h F.symm ?_
  rw [← hF, ← Submodule.map_comp]
  convert Submodule.map_id Λ
  ext v
  simp

/-- `Ω(τ)` is a period matrix of the QM lattice `Λ_τ = ι(𝒪)(τ, 1)ᵀ` (bp-analytic; the proof of
`ZInQ.LeafPush2.isPeriodMatrix_qmLattice`, repeated). -/
theorem isPeriodMatrix_qmLattice {τ : ℂ} (hτ : τ.im ≠ 0) :
    IsPeriodMatrix (BPAnalytic.QM.qmLattice hτ) (BPAnalytic.QM.Omega τ) :=
  isPeriodMatrix_of_map
    (⟨LinearEquiv.refl ℂ _, fun z => by
      simpa using BPAnalytic.mem_periodLattice_iff _ (BPAnalytic.QM.det_im_Omega_ne_zero hτ) z⟩)
    (BPAnalytic.QM.FpEquiv hτ).toLinearEquiv (BPAnalytic.QM.map_periodLattice_Omega hτ)

/-- `Ω(τ) ∈ 𝔥₂` for `Im τ > 0` (bp-analytic's `Omega_mem_siegelSpace`). -/
theorem isSiegel_Omega {τ : ℂ} (hτ : 0 < τ.im) : IsSiegel (BPAnalytic.QM.Omega τ) :=
  BPAnalytic.QM.Omega_mem_siegelSpace hτ

/-- The odd characteristics: `aᵀb` odd. -/
def IsOddChar (m : Char2) : Prop :=
  ((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) % 2 = 1

/-- **The six odd theta constants vanish (proved).** `n ↦ -n - a` maps the term at `n` to minus
itself when `aᵀb` is odd. This checks the docstring of `ThetaPointOfFibre` ("the six odd theta
nulls vanish"); the proof of the piece does not need it (`height_even`). -/
theorem thetaConst_odd (Ω : Matrix (Fin 2) (Fin 2) ℂ) (m : Char2) (hm : IsOddChar m) :
    thetaConst Ω m = 0 := by
  set a : Fin 2 → ℤ := fun i => ((m.1 i : ℕ) : ℤ)
  set f : (Fin 2 → ℤ) → ℂ := fun n => Complex.exp (Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ
          Ω.mulVec (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2)) +
      2 * Real.pi * I *
        ((fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ (fun i => ((m.2 i : ℕ) : ℂ) / 2))) with hf
  let e : (Fin 2 → ℤ) ≃ (Fin 2 → ℤ) :=
    { toFun := fun n => -n - a, invFun := fun n => -n - a,
      left_inv := fun n => by simp, right_inv := fun n => by simp }
  have hv : ∀ n : Fin 2 → ℤ, (fun i => ((e n i : ℤ) : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) =
      -(fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) := by
    intro n; funext i
    simp only [e, Equiv.coe_fn_mk, Pi.sub_apply, Pi.neg_apply, a, Int.cast_sub, Int.cast_neg,
      Int.cast_natCast]
    ring
  -- the parity: `aᵀb = 2k + 1`
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ) = 2 * k + 1 :=
    ⟨((m.1 0 : ℕ) * (m.2 0 : ℕ) + (m.1 1 : ℕ) * (m.2 1 : ℕ)) / 2, by unfold IsOddChar at hm; omega⟩
  have hfe : ∀ n, f (e n) = - f n := by
    intro n
    simp only [hf]
    rw [hv n, Matrix.mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg, neg_dotProduct]
    set Q := (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ
          Ω.mulVec (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2)
    set D := (fun i => (n i : ℂ) + ((m.1 i : ℕ) : ℂ) / 2) ⬝ᵥ (fun i => ((m.2 i : ℕ) : ℂ) / 2)
    -- `2·2πi·D = 2πi (nᵀb) + πi (aᵀb)`
    have hD : 2 * D = ((n 0 * (m.2 0 : ℕ) + n 1 * (m.2 1 : ℕ) + k : ℤ) : ℂ) + 1 / 2 := by
      have hk' : ((m.1 0 : ℕ) : ℂ) * ((m.2 0 : ℕ) : ℂ) + ((m.1 1 : ℕ) : ℂ) * ((m.2 1 : ℕ) : ℂ)
          = 2 * (k : ℂ) + 1 := by exact_mod_cast hk
      simp only [D, dotProduct, Fin.sum_univ_two]
      push_cast
      linear_combination (1 / 2 : ℂ) * hk'
    have hexp : Complex.exp (2 * Real.pi * I * D) =
        - Complex.exp (2 * Real.pi * I * (-D)) := by
      have h2 : 2 * Real.pi * I * D = 2 * Real.pi * I * (-D) +
          (((n 0 * (m.2 0 : ℕ) + n 1 * (m.2 1 : ℕ) + k : ℤ) : ℂ) * (2 * Real.pi * I) +
            Real.pi * I) := by
        linear_combination (2 * Real.pi * I) * hD
      rw [h2, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I,
        Complex.exp_pi_mul_I]
      ring
    rw [Complex.exp_add, Complex.exp_add, hexp]
    ring
  have h : thetaConst Ω m = - thetaConst Ω m := by
    change ∑' n, f n = - ∑' n, f n
    rw [← tsum_neg, ← Equiv.tsum_eq e f]
    exact tsum_congr hfe
  have h2 : (2 : ℂ) * thetaConst Ω m = 0 := by linear_combination h
  simpa using h2

/-! ### The smaller named Props -/

/-- **TEXTBOOK leaf candidate (analytic uniformization at a complex place).** An abelian surface
`A` over a number field `K` has, at some embedding `σ : K → ℂ`, an analytic uniformization
`Φ : ℂ² → A(ℂ)_σ` with kernel `Λ` (`IsUniformization`: surjective homomorphism, kernel `Λ`, open
preimages of affine charts, holomorphic regular functions). Mumford, *Abelian Varieties*, §1
(`X(ℂ)` is a complex torus `ℂ^g/Λ`) with Serre's GAGA for the holomorphy of regular functions
(locators UNVERIFIED). In the build: `ZInQKernel/HDecomp/LeafPush2/UnifBridge.lean`,
`exists_isUniformization_of_leaf`, gives it over `ℂ` from bp-analytic's `UniformizationLeafAll`;
here `σ` exists because `K` is a number field. -/
def UniformizationExistsNF : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K), A.dim = (2 : WithBot ℕ∞) →
    ∃ (σ : K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ),
      IsUniformization σ Λ Φu

/-- **GLUE (G19, F1 analytic on the actual fibre: R1(b) with the Hauptmodul comparison).** For
`u ∉ 𝒞`, every number-field model `A` of the fibre surface over `J(u)` (`FibreOver`), every
complex place `σ` and every analytic uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ`: there are
`τ ∈ ℍ` and a `ℂ`-linear automorphism `F` of `ℂ²` carrying `Λ` onto the QM lattice
`Λ_τ = ι(𝒪)(τ, 1)ᵀ` (bp-analytic's `qmLattice`, N5's basis of `𝒪`), with F1's value
`jNum(Ω(τ)) / jDen(Ω(τ)) = J(u)` (pkg-I1's `Ω(τ)`, the period matrix of the principal
polarization `Trd(μ⁻¹xȳ)` of `ℂ²/Λ_τ`).

Why true (model argument, no human review). `σ` factors as `ℚ̄ → ℂ` after a Galois conjugate of
the embedding of `FibreOver`; `π` is defined over `ℚ` and `J(u) ∈ ℚ`, so the conjugate object of
`Y₃` again lies over `J(u)`. R1(b) (`R01b_ComplexUniformization`, a placeholder: Shimura 1967,
Main Thm I) gives `τ ∈ ℍ` with `A(ℂ)_σ ≅ ℂ²/Λ_τ`, and two uniformizations of one complex torus
differ by a linear automorphism of `ℂ²` (bp-analytic, `IsUniformization.continuous_comparison`
and its sequel). The value: `τ ↦ π(P_τ)` (R1(b)(c)) and the function `f` of
`PkgI1.QMHauptmodul` (a consequence of R2-R4) are Hauptmoduln of `Γ*\ℍ = X₆/W` with the same
values `0, ∞, -16/27` at the CM points of discriminants `-4, -3, -24` (`R2fpProps`), so they are
equal (a Möbius map fixing three points is the identity); `jDen(Ω(τ)) ≠ 0` because `J(u) ≠ ∞`
and `χ₁₀(Ω(τ)) ≠ 0` for the simple surface `A` (`FibreSimple`). The polarization of the QM
object plays no role (`f` and `π` are compared as functions of `τ`); like every leaf-qm-fp object
this inherits the SPECULATIVE premise bp-qmmoduli §2.2 through `R1fpProps`, `R2fpProps`. Size: large (it
needs the analytification of `Y₃` and of the universal family, rv-blueprints Q3). -/
def FibreQMPeriodAll : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∀ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) σ), IsUniformization σ Λ Φu →
    ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
      Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = ((Jmap u : ℚ) : ℂ)

/-- **GLUE (G19, F1 analytic on the actual fibre; the existential form of `FibreQMPeriodAll`).**
For `u ∉ 𝒞` and every number-field model `A` of the fibre surface over `J(u)`: at some complex
place `σ`, some analytic uniformization `Φ : ℂ² → A(ℂ)_σ` has a kernel `Λ` carried onto a QM
lattice `Λ_τ = ι(𝒪)(τ, 1)ᵀ` (`τ ∈ ℍ`) by a `ℂ`-linear automorphism, with
`jNum(Ω(τ)) / jDen(Ω(τ)) = J(u)`. It follows from `DimBaseChange`, `UniformizationExistsNF` and
`FibreQMPeriodAll` (`fibreQMPeriod_of_all`), and with `ThetaNullAlgebraic` alone it gives
`ThetaPointOfFibre` (`thetaPointOfFibre_of_qm`). Why true: as for `FibreQMPeriodAll`, at the
place `σ` through which the embedding of `FibreOver` factors (no Galois conjugation needed). -/
def FibreQMPeriod : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) σ), IsUniformization σ Λ Φu ∧
    ∃ (τ : ℂ) (hτ : 0 < τ.im) (F : (Fin 2 → ℂ) ≃ₗ[ℂ] (Fin 2 → ℂ)),
      Λ.map (F.toLinearMap.restrictScalars ℤ) = BPAnalytic.QM.qmLattice hτ.ne' ∧
      PkgI1.jNum (PkgI1.Omega τ) / PkgI1.jDen (PkgI1.Omega τ) = ((Jmap u : ℚ) : ℂ)

/-- **LEAF-COMPOSITE (algebraicity of theta constants).** For an abelian variety `A` over a
number field `K`, an analytic uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ` and any
`Ω ∈ 𝔥₂` that is a period matrix of `Λ` (that is, any principal polarization of `ℂ²/Λ` with any
symplectic basis), the sixteen theta constants `θ_m(0, Ω)` are, up to one nonzero factor `c`, the
image of a point `z ∈ L¹⁶` of a number field `L` under an embedding `L → ℂ`.

Sources: the principal polarization of `A(ℂ)_σ` is algebraic (Lefschetz, Appell–Humbert with
GAGA) and defined over `ℚ̄` (`NS(A_ℚ̄) = NS(A_ℂ)`); theta-constant ratios of a principally
polarized abelian variety over `ℚ̄` are algebraic: for genus 2, Thomae's formula expresses
`θ_m⁴/θ_{m'}⁴` through the Rosenhain roots of the curve (Mumford, *Tata Lectures on Theta II*,
IIIa §8; for a product of elliptic curves, Jacobi's formulas), and in general Shimura's theorem
on special values of Siegel modular functions with algebraic Fourier coefficients (Shimura,
*Theta functions with complex multiplication*, Duke 43 (1976), and Faltings–Chai, Ch. V) (all
locators UNVERIFIED). Not one printed theorem: a composite of published results, so a leaf
candidate to be reviewed, not a leaf. -/
def ThetaNullAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ), IsUniformization σ Λ Φu →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : Char2 → L.K) (c : ℂ), c ≠ 0 ∧
      ∀ m, emb (z m) = c * thetaConst Ω m

/-- **LEAF candidate (theta-constant ratios are algebraic numbers).** For an abelian variety `A`
over a number field `K`, a uniformization `Φ : ℂ² → A(ℂ)_σ` with kernel `Λ` and any period matrix
`Ω ∈ 𝔥₂` of `Λ`: some theta constant `θ_{m₀}(0, Ω)` is nonzero and every ratio
`θ_m(0, Ω)/θ_{m₀}(0, Ω)` is an algebraic number. This is the form in which the literature states
it (values of Siegel modular functions with algebraic Fourier coefficients at a point whose
principally polarized abelian variety is defined over `ℚ̄` are algebraic: Shimura, Duke 43 (1976);
for genus 2 also Thomae's formula, Mumford, *Tata Lectures on Theta II*, IIIa §8; with
`NS(A_ℚ̄) = NS(A_ℂ)` for the polarization defined by `Ω`; all locators UNVERIFIED). Nonvanishing:
at most one of the ten even `θ_m(0, Ω)` vanishes in genus 2 (it vanishes exactly on products of
elliptic curves; UNVERIFIED locator: Igusa 1962/1967). `ThetaNullAlgebraic` follows
(`thetaNullAlgebraic_of_ratios`, proved). -/
def ThetaRatiosAlgebraic : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (σ : K →+* ℂ)
    (Λ : Submodule ℤ (Fin 2 → ℂ)) (Φu : (Fin 2 → ℂ) → CPts A σ), IsUniformization σ Λ Φu →
    ∀ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω → IsPeriodMatrix Λ Ω →
    ∃ m₀ : Char2, thetaConst Ω m₀ ≠ 0 ∧ ∀ m, IsAlgebraic ℚ (thetaConst Ω m / thetaConst Ω m₀)

/-- Finitely many algebraic complex numbers lie in the image of a number field (`ℚ(α_i) ⊆ ℂ`). -/
theorem exists_nf_of_isAlgebraic {Idx : Type} [Fintype Idx] (α : Idx → ℂ)
    (h : ∀ i, IsAlgebraic ℚ (α i)) :
    ∃ (L : GlueAssembly.NF) (emb : L.K →+* ℂ) (z : Idx → L.K), ∀ i, emb (z i) = α i := by
  set E : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ (Set.range α)
  have hfd : FiniteDimensional ℚ E := by
    apply IntermediateField.finiteDimensional_adjoin
    rintro x ⟨i, rfl⟩
    exact (h i).isIntegral
  have : NumberField E := ⟨⟩
  exact ⟨⟨E⟩, E.val.toRingHom, fun i => ⟨α i, IntermediateField.subset_adjoin ℚ _ ⟨i, rfl⟩⟩,
    fun i => rfl⟩

/-- **`ThetaNullAlgebraic` from `ThetaRatiosAlgebraic` (proved):** `L = ℚ(θ_m/θ_{m₀})`,
`c = θ_{m₀}⁻¹`. -/
theorem thetaNullAlgebraic_of_ratios (h : ThetaRatiosAlgebraic) : ThetaNullAlgebraic := by
  intro K _ _ A σ Λ Φu hU Ω hS hP
  obtain ⟨m₀, h0, halg⟩ := h K A σ Λ Φu hU Ω hS hP
  obtain ⟨L, emb, z, hz⟩ := exists_nf_of_isAlgebraic _ halg
  exact ⟨L, emb, z, (thetaConst Ω m₀)⁻¹, inv_ne_zero h0, fun m => by
    rw [hz m, div_eq_inv_mul]⟩

/-- **GLUE (G19, F1 analytic; proved below from `DimBaseChange`, `UniformizationExistsNF` and
`FibreQMPeriodAll`).** For `u ∉ 𝒞` and every model `A` of the fibre surface over `J(u)`: some
analytic uniformization of `A(ℂ)_σ` with a period matrix `Ω ∈ 𝔥₂` such that `j_θ(Ω) = J(u)`. -/
def FibreThetaF1 : Prop :=
  ∀ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y) (π : ToP1 Y.left),
    R1fpProps Y Φ → R2fpProps Y Φ π → ∀ u : ℚ, u ∉ contactSet →
    ∀ (K : GlueAssembly.NF) (A : ZInQ.DefFaltings.AbVar K.K), FibreOver Y Φ π u K A →
    ∃ (σ : K.K →+* ℂ) (Λ : Submodule ℤ (Fin 2 → ℂ))
      (Φu : (Fin 2 → ℂ) → CPts (LeafAdopt.abVarEquiv K.K A) σ), IsUniformization σ Λ Φu ∧
    ∃ Ω : Matrix (Fin 2) (Fin 2) ℂ, IsSiegel Ω ∧ IsPeriodMatrix Λ Ω ∧
      jTheta Ω = ((Jmap u : ℚ) : ℂ)

/-! ### The proofs -/

/-- **`ThetaPointOfFibre` from F1-analytic and algebraicity (proved).** Take `K' = L` and `z'`
the ten even coordinates of the algebraic theta point `z`. -/
theorem thetaPointOfFibre_of (hF1 : FibreThetaF1) (hAlg : ThetaNullAlgebraic) :
    ThetaPointOfFibre := by
  intro Y Φ π h1 h2 u hu K A hFib
  obtain ⟨σ, Λ, Φu, hU, Ω, hS, hP, hJ⟩ := hF1 Y Φ π h1 h2 u hu K A hFib
  obtain ⟨L, emb, z, c, hc, hz⟩ := hAlg K.K (LeafAdopt.abVarEquiv K.K A) σ Λ Φu hU Ω hS hP
  exact ⟨σ, Λ, Φu, hU, Ω, hS, hP, L, emb, z, c, hc, hz, L, fun i => z (evenEnum i),
    f1_of_theta emb Ω z c hc hz (Jmap u) hJ, height_even z⟩

/-- **The existential form (proved)** from `DimBaseChange` (the model is a surface,
`model_dim`), `UniformizationExistsNF` and `FibreQMPeriodAll`. -/
theorem fibreQMPeriod_of_all (hDim : DimBaseChange) (hU : UniformizationExistsNF)
    (hQM : FibreQMPeriodAll) : FibreQMPeriod := by
  intro Y Φ π h1 h2 u hu K A hFib
  obtain ⟨emb, y, P, hP, hy, hiso⟩ := hFib
  have hA2 : A.dim = 2 := model_dim hDim emb A P.A hiso P.surface
  obtain ⟨σ, Λ, Φu, hΦu⟩ := hU K.K (LeafAdopt.abVarEquiv K.K A) hA2
  exact ⟨σ, Λ, Φu, hΦu, hQM Y Φ π h1 h2 u hu K A ⟨emb, y, P, hP, hy, hiso⟩ σ Λ Φu hΦu⟩

/-- **F1-analytic on the fibre (proved)** from `FibreQMPeriod`, with `Ω = Ω(τ)`
(bp-analytic: `Ω(τ) ∈ 𝔥₂`, and `Ω(τ)` is a period matrix of `Λ_τ`, hence of `Λ`). -/
theorem fibreThetaF1_of_qm (hQM : FibreQMPeriod) : FibreThetaF1 := by
  intro Y Φ π h1 h2 u hu K A hFib
  obtain ⟨σ, Λ, Φu, hΦu, τ, hτ, F, hF, hJ⟩ := hQM Y Φ π h1 h2 u hu K A hFib
  refine ⟨σ, Λ, Φu, hΦu, BPAnalytic.QM.Omega τ, isSiegel_Omega hτ,
    isPeriodMatrix_of_comap (isPeriodMatrix_qmLattice hτ.ne') F hF, ?_⟩
  rw [jTheta_eq, ← omega_eq]
  exact hJ

/-- F1-analytic on the fibre from `DimBaseChange`, `UniformizationExistsNF`, `FibreQMPeriodAll`. -/
theorem fibreThetaF1_of (hDim : DimBaseChange) (hU : UniformizationExistsNF)
    (hQM : FibreQMPeriodAll) : FibreThetaF1 :=
  fibreThetaF1_of_qm (fibreQMPeriod_of_all hDim hU hQM)

/-- **Missing piece 9, `ThetaPointOfFibre`, from two named Props (proved):** the existential
F1-analytic glue `FibreQMPeriod` and the algebraicity of theta constants. -/
theorem thetaPointOfFibre_of_qm (hQM : FibreQMPeriod) (hAlg : ThetaNullAlgebraic) :
    ThetaPointOfFibre :=
  thetaPointOfFibre_of (fibreThetaF1_of_qm hQM) hAlg

/-- **Missing piece 9 from the existential F1 glue and the ratio form of algebraicity (proved).** -/
theorem thetaPointOfFibre_of_qm_ratios (hQM : FibreQMPeriod) (hAlg : ThetaRatiosAlgebraic) :
    ThetaPointOfFibre :=
  thetaPointOfFibre_of_qm hQM (thetaNullAlgebraic_of_ratios hAlg)

/-- **Missing piece 9, `ThetaPointOfFibre`, from strictly smaller named Props (proved).** -/
theorem thetaPointOfFibre_of_parts (hDim : DimBaseChange) (hU : UniformizationExistsNF)
    (hQM : FibreQMPeriodAll) (hAlg : ThetaNullAlgebraic) : ThetaPointOfFibre :=
  thetaPointOfFibre_of (fibreThetaF1_of hDim hU hQM) hAlg

end ThetaPt

end G0Split

end HSyn

end


/-! ## g0-assemble: `ModularConstituent` from g0-mod-field's range and `AfterG7`

g0-mod-field proved `G0ModField.ModularConstituentG` (its copy of `ModularConstituent` over the
kernel's `PkgI3.AbVar`, without `LeafAdopt.abVarEquiv`) from `FibreCoverExists`,
`KernelFieldExists`, `UnramifiedSup`, the bundle's T14a, T14b, T15, T30, T31, and `AfterG7`.
Here its file is compiled over `Leaves.lean`'s copies (it needed only the kernel module
`Descent/WP3.lean`, copied above), and the layer caveat of g0-mod-newform is checked:
`LeafAdopt.abVarEquiv` commutes with `baseChange` definitionally (`abVarEquiv_baseChange`,
`abVarEquiv_symm_baseChange`, both `rfl`), so `ModularConstituentG → ModularConstituent` is a
repackaging (`modularConstituent_of_G`). -/

section G0AssembleModSec

namespace HSyn

/-- Layer check: def-faltings' `baseChange` and I3's `baseChange` agree through `abVarEquiv`. -/
theorem abVarEquiv_baseChange (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]
    (A : ZInQ.DefFaltings.AbVar K) :
    LeafAdopt.abVarEquiv L (A.baseChange L) = (LeafAdopt.abVarEquiv K A).baseChange L := rfl

/-- Layer check, the form `ModularConstituent` uses for `J₁(N)_L`. -/
theorem abVarEquiv_symm_baseChange (K : Type) [Field K] (L : Type) [Field L] [Algebra K L]
    (J : PkgI3.AbVar K) :
    LeafAdopt.abVarEquiv L (((LeafAdopt.abVarEquiv K).symm J).baseChange L) = J.baseChange L :=
  rfl

/-- The two textual copies of `CommonConstituent` (g0-mod-field's, g0-split's) agree. -/
theorem commonConstituent_copy {K : Type} [Field K] [NumberField K] (A J : PkgI3.AbVar K) :
    G0ModField.CommonConstituent A J ↔ G0Split.CommonConstituent A J := Iff.rfl

/-- **g0-mod-field's `ModularConstituentG` gives g0-split's `ModularConstituent`** (the model
`A : PkgI3.AbVar L` is sent to `(abVarEquiv L).symm A`; every clause is definitionally the same). -/
theorem modularConstituent_of_G (h : G0ModField.ModularConstituentG) :
    G0Split.ModularConstituent := by
  intro Y Φ π h1 h2 u hu y P hy hπ
  obtain ⟨L, emb, A, N, J, hiso, hN, hJ, hNle, hdeg, hCC⟩ := h Y Φ π h1 h2 u hu y P hy hπ
  refine ⟨L, emb, (LeafAdopt.abVarEquiv L.K).symm A, N, J, ?_, hN, hJ, hNle, hdeg, ?_⟩
  · exact hiso
  · rw [abVarEquiv_symm_baseChange, Equiv.apply_symm_apply]
    exact (commonConstituent_copy _ _).1 hCC

/-- **`ModularConstituent` from g0-mod-field's three glue Props, the bundle's T14a, T14b, T15,
T30 (`TextbookLeaves.leafSqrtCrit`, from T16a) and T31, and `AfterG7` (G8-G16).** -/
theorem modularConstituent_of_field (t : TextbookLeaves) (hCover : G0ModField.FibreCoverExists)
    (hKer : G0ModField.KernelFieldExists) (hSup : G0ModField.UnramifiedSup)
    (hRest : G0ModField.AfterG7) : G0Split.ModularConstituent :=
  modularConstituent_of_G (G0ModField.modularConstituent_of_ranges_T14 hCover hKer hSup t.t14a
    t.t14b t.t15 t.leafSqrtCrit t.t31 hRest)

end HSyn

end G0AssembleModSec

#print axioms HSyn.modularConstituent_of_field


/-! ## g0-assemble: wave 26 assembled — `GluePieces` from `GluePieces2`

Task g0-assemble, 2026-11-13. The ten fields of `HSyn.GluePieces` (above, unchanged) are derived
from the smaller named Props that wave 26 reduced them to, bundled as `HSyn.GluePieces2`:

| `GluePieces` field | wave-26 task | how it is obtained here |
|---|---|---|
| `dimFinite` | g0-dim | `G0Split.dimFinite` (proved, Mathlib only) |
| `dimBaseChange` | g0-dim | `G0Split.dimBaseChange` (proved, Mathlib only) |
| `fibreSimple` | g0-fibresimple | `G0FibreSimple.fibreSimple_of_leaves` from `t.t6`, `t.t27`, the textbook leaves `MulIsogeny`, `RigidityHom`, the glue `FiniteDescends` and the glue `FibreComTrivial` (blocked on qm-pin) |
| `productModelHeight` | g0-heightadd | `ZInQ.G0HeightAdd.productModelHeight_of` with `productMetrization_of_geo`, from four glue Props |
| `stableHeightBaseChange` | g0-stablebc | `G0StableBC.stableHeightBaseChange_of_hodgeLine` from the glue `HodgeLineBaseChange` |
| `productExists` | g0-product | `G0Product.productExists` (proved, Mathlib only) |
| `reverseIsogeny` | g0-reverseisog | `G0RevIsog.reverseIsogeny_of_leaves r dimFinite` (route B: R19 and H5 of the bundle) |
| `thetaPoint` | g0-thetapoint | `ThetaPt.thetaPointOfFibre_of_qm_ratios` from the glue `FibreQMPeriod` (blocked on qm-pin) and the leaf candidate `ThetaRatiosAlgebraic` |
| `modularConstituent` | g0-mod-field (G2-G7) | `modularConstituent_of_field` (above): g0-mod-field's three glue Props (`KernelFieldExists` blocked on qm-pin), the bundle's T14a, T14b, T15, T30, T31, and `AfterG7` (G8-G16, kept whole: g0-mod-galois and g0-mod-newform are not yet composed with it, see `docs/research/g0-assemble.md` §3) |
| `heightCopies` | (no wave-26 task) | kept as one field (glue, pure transport) |
-/

section G0AssembleSec

noncomputable section

namespace HSyn

open G0Split

/-- **The glue Props left after wave 26** (g0-assemble). Each field is a named `def … : Prop` of a
wave-26 task, copied verbatim into this file in that task's section above; kinds as in
`docs/research/g0-assemble.md` §2 (LEAF = textbook theorem new to the bundles; GLUE = to be proved
by the project; QM-PIN = glue that cannot be proved as stated until task qm-pin repairs the QM
clauses `R1fpProps`, `R2fpProps`). -/
structure GluePieces2 : Prop where
  /-- g0-fibresimple, LEAF (textbook; Mumford §4 Application 2, Milne Thm 8.2, UNVERIFIED
  locators): `[n]` is finite and surjective for `n ≠ 0` (characteristic 0). -/
  mulIsogeny : G0FibreSimple.MulIsogeny
  /-- g0-fibresimple, LEAF (textbook; Mumford §4 Cor. 1, Milne Cor. 2.2, UNVERIFIED locators):
  rigidity, a pointed morphism of abelian varieties is a homomorphism. -/
  rigidityHom : G0FibreSimple.RigidityHom
  /-- g0-fibresimple FS1b′, GLUE (EGA IV₂ 2.7.1, UNVERIFIED): `IsFinite` descends along
  `Spec L → Spec K`. -/
  finiteDescends : G0FibreSimple.FiniteDescends
  /-- g0-fibresimple FS5, GLUE, **QM-PIN**: NoCM on the fibre, `End_𝒪(P.A) = ℤ`. -/
  fibreComTrivial : G0FibreSimple.FibreComTrivial
  /-- g0-heightadd (stated in def-faltings), GLUE: uniqueness of analytic uniformizations. -/
  analyticUniformizationUnique : ZInQ.DefFaltings.AnalyticUniformizationUnique
  /-- g0-heightadd, GLUE: two metrizations of one group model have the same dimension. -/
  metrizationDimUnique : ZInQ.G0HeightAdd.MetrizationDimUnique
  /-- g0-heightadd, GLUE: every group model has a metrization. -/
  metrizationExists : ZInQ.G0HeightAdd.MetrizationExists
  /-- g0-heightadd P2a-geo, GLUE: the product metrization with multiplicative index,
  coefficients and covolumes. -/
  productMetrizationGeo : ZInQ.G0HeightAdd.ProductMetrizationGeo
  /-- g0-stablebc, GLUE (geometric half of h5-neron's H4a): the natural map on `⋀^g ω` under base
  change of group models. -/
  hodgeLineBaseChange : G0StableBC.HodgeLineBaseChange
  /-- g0-thetapoint, GLUE, **QM-PIN**: a uniformization lattice of the fibre is a QM lattice
  `ι(𝒪)(τ,1)ᵀ` with `j_θ(Ω(τ)) = J(u)`. -/
  fibreQMPeriod : G0Split.ThetaPt.FibreQMPeriod
  /-- g0-thetapoint, LEAF candidate (composite of published results: Shimura 1976 / Mumford Tata
  II; UNVERIFIED locators): theta-constant ratios at a period matrix of an abelian surface over a
  number field are algebraic. -/
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  /-- g0-mod-field G2, GLUE (Prop. TS + Lemma NV on the actual fibre): a separable `f`,
  `deg f ≤ 324`, whose splitting field is unramified outside `T` and carries a rational fibre. -/
  fibreCoverExists : G0ModField.FibreCoverExists
  /-- g0-mod-field G4 + B1, GLUE, **QM-PIN**: the kernel field and the conjugacy data. -/
  kernelFieldExists : G0ModField.KernelFieldExists
  /-- g0-mod-field, GLUE (STANDARD, Neukirch I §8, UNVERIFIED): a compositum of finite Galois
  extensions of `ℚ` unramified at `p` is unramified at `p`. -/
  unramifiedSup : G0ModField.UnramifiedSup
  /-- G8-G16, GLUE, kept whole: for every fibre context and G7 data, a `J₁(M)` with `M ≤ Q_D·M²`
  and a common constituent over `L'` (g0-mod-galois and g0-mod-newform reduce its two halves). -/
  afterG7 : G0ModField.AfterG7
  /-- leaf-adopt2's transport target, GLUE (no wave-26 task). -/
  heightCopies : HeightCopiesAgree

/-- **`GluePieces` from `GluePieces2` and the leaf bundles** (g0-assemble): every field of
`GluePieces` is a wave-26 theorem applied to fields of `GluePieces2`, `r` or `t`. -/
theorem gluePieces_of_gluePieces2 (r : ResearchLeaves) (t : TextbookLeaves) (gp2 : GluePieces2) :
    GluePieces where
  dimFinite := G0Split.dimFinite
  dimBaseChange := G0Split.dimBaseChange
  fibreSimple := G0FibreSimple.fibreSimple_of_leaves t gp2.mulIsogeny gp2.rigidityHom
    ⟨gp2.finiteDescends, gp2.fibreComTrivial⟩
  productModelHeight := ZInQ.G0HeightAdd.productModelHeight_of gp2.analyticUniformizationUnique
    gp2.metrizationDimUnique gp2.metrizationExists
    (ZInQ.G0HeightAdd.productMetrization_of_geo gp2.productMetrizationGeo)
  stableHeightBaseChange := G0StableBC.stableHeightBaseChange_of_hodgeLine gp2.hodgeLineBaseChange
  productExists := G0Product.productExists
  reverseIsogeny := G0RevIsog.reverseIsogeny_of_leaves r G0Split.dimFinite
  thetaPoint := G0Split.ThetaPt.thetaPointOfFibre_of_qm_ratios gp2.fibreQMPeriod
    gp2.thetaRatiosAlgebraic
  modularConstituent := modularConstituent_of_field t gp2.fibreCoverExists gp2.kernelFieldExists
    gp2.unramifiedSup gp2.afterG7
  heightCopies := gp2.heightCopies

/-- **G0 after wave 26** (g0-assemble): the leaf bundles and `GluePieces2` imply
`ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves2 (r : ResearchLeaves) (t : TextbookLeaves) (gp2 : GluePieces2) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves r t (gluePieces_of_gluePieces2 r t gp2)

end HSyn

end

end G0AssembleSec

#print axioms HSyn.gluePieces_of_gluePieces2
#print axioms HSyn.sixContactMin_of_leaves2

