import Mathlib

/-! Part A: abstract chart machinery. A continuous open map `ξ : ℂ → E` whose fibres are the cosets
of an additive subgroup `Λ`, together with chart data `(c, e)` (`c : E → ℂ` with `c ∘ ξ = e` on the
source of a local biholomorphism `e` of `ℂ`), gives a complex-analytic atlas on `E` for which `ξ` is
a local biholomorphism. -/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

noncomputable section
open Topology Filter Set
open scoped Manifold ContDiff

namespace HCMW

variable {E : Type*} [TopologicalSpace E] {Λ : AddSubgroup ℂ} {ξ : ℂ → E}

/-- A chart datum for `ξ`: a coordinate `c : E → ℂ` and a partial homeomorphism `e` of `ℂ` with
nonvanishing complex derivative on its source, such that `c ∘ ξ = e` on the source of `e`. -/
structure ChartDatum (ξ : ℂ → E) where
  c : E → ℂ
  e : OpenPartialHomeomorph ℂ ℂ
  eq : ∀ z ∈ e.source, c (ξ z) = e z
  deriv : ∀ z ∈ e.source, ∃ d : ℂ, d ≠ 0 ∧ HasDerivAt e d z

/-- The chart `ξ(S) → e(S)`, `P ↦ c P`, of a chart datum. -/
def ChartDatum.chart (hc : Continuous ξ) (ho : IsOpenMap ξ) (D : ChartDatum ξ) :
    OpenPartialHomeomorph E ℂ where
  toFun := D.c
  invFun := ξ ∘ D.e.symm
  source := ξ '' D.e.source
  target := D.e.target
  map_source' := by rintro _ ⟨z, hz, rfl⟩; rw [D.eq z hz]; exact D.e.map_source hz
  map_target' := fun t ht => ⟨D.e.symm t, D.e.map_target ht, rfl⟩
  left_inv' := by
    rintro _ ⟨z, hz, rfl⟩
    simp only [Function.comp]; rw [D.eq z hz, D.e.left_inv hz]
  right_inv' := fun t ht => by
    simp only [Function.comp]; rw [D.eq _ (D.e.map_target ht), D.e.right_inv ht]
  open_source := ho _ D.e.open_source
  open_target := D.e.open_target
  continuousOn_toFun := by
    rw [continuousOn_open_iff (ho _ D.e.open_source)]
    intro O hO
    have : ξ '' D.e.source ∩ D.c ⁻¹' O = ξ '' (D.e.source ∩ D.e ⁻¹' O) := by
      ext P; constructor
      · rintro ⟨⟨z, hz, rfl⟩, hP⟩
        exact ⟨z, ⟨hz, by simpa [Set.mem_preimage, D.eq z hz] using hP⟩, rfl⟩
      · rintro ⟨z, ⟨hz, hO'⟩, rfl⟩
        exact ⟨⟨z, hz, rfl⟩, by simpa [Set.mem_preimage, D.eq z hz] using hO'⟩
    rw [this]; exact ho _ (D.e.isOpen_inter_preimage hO)
  continuousOn_invFun := hc.comp_continuousOn D.e.continuousOn_symm

@[simp] theorem ChartDatum.chart_coe (hc : Continuous ξ) (ho : IsOpenMap ξ) (D : ChartDatum ξ) :
    ⇑(D.chart hc ho) = D.c := rfl

@[simp] theorem ChartDatum.chart_symm_coe (hc : Continuous ξ) (ho : IsOpenMap ξ) (D : ChartDatum ξ) :
    ⇑(D.chart hc ho).symm = ξ ∘ D.e.symm := rfl

@[simp] theorem ChartDatum.chart_source (hc : Continuous ξ) (ho : IsOpenMap ξ) (D : ChartDatum ξ) :
    (D.chart hc ho).source = ξ '' D.e.source := rfl

@[simp] theorem ChartDatum.chart_target (hc : Continuous ξ) (ho : IsOpenMap ξ) (D : ChartDatum ξ) :
    (D.chart hc ho).target = D.e.target := rfl

/-- Local form: near any `w` with `ξ w` in the chart source, `c ∘ ξ = e ∘ (· - l)` on an open set. -/
theorem ChartDatum.local_form (hfib : ∀ z w, ξ z = ξ w ↔ z - w ∈ Λ) (D : ChartDatum ξ) {w : ℂ}
    (hw : ξ w ∈ ξ '' D.e.source) :
    ∃ l : ℂ, IsOpen ((· - l) ⁻¹' D.e.source) ∧ w ∈ (· - l) ⁻¹' D.e.source ∧
      ∀ w' ∈ (· - l) ⁻¹' D.e.source, D.c (ξ w') = D.e (w' - l) := by
  obtain ⟨v, hv, hvw⟩ := hw
  refine ⟨w - v, D.e.open_source.preimage (continuous_id.sub continuous_const), ?_, fun w' hw' => ?_⟩
  · simpa using hv
  · have hl : w - v ∈ Λ := (hfib w v).1 hvw.symm
    have : ξ w' = ξ (w' - (w - v)) := (hfib _ _).2 (by simpa using hl)
    rw [this, D.eq _ hw']

theorem ChartDatum.differentiableAt_e (D : ChartDatum ξ) {z : ℂ} (hz : z ∈ D.e.source) :
    DifferentiableAt ℂ D.e z := by
  obtain ⟨d, -, hd⟩ := D.deriv z hz; exact hd.differentiableAt

theorem ChartDatum.differentiableOn_e (D : ChartDatum ξ) : DifferentiableOn ℂ D.e D.e.source :=
  fun z hz => (D.differentiableAt_e hz).differentiableWithinAt

theorem ChartDatum.differentiableAt_symm (D : ChartDatum ξ) {t : ℂ} (ht : t ∈ D.e.target) :
    DifferentiableAt ℂ D.e.symm t := by
  obtain ⟨d, hd0, hd⟩ := D.deriv _ (D.e.map_target ht)
  exact (D.e.hasDerivAt_symm ht hd0 hd).differentiableAt

theorem ChartDatum.contDiffAt_symm (D : ChartDatum ξ) {n : ℕ∞ω} {t : ℂ} (ht : t ∈ D.e.target) :
    ContDiffAt ℂ n D.e.symm t :=
  (DifferentiableOn.contDiffOn (fun t ht => (D.differentiableAt_symm ht).differentiableWithinAt)
    D.e.open_target).contDiffAt (D.e.open_target.mem_nhds ht)

/-- `c ∘ ξ` is analytic near every point mapped into the chart source. -/
theorem ChartDatum.contDiffAt_comp (hfib : ∀ z w, ξ z = ξ w ↔ z - w ∈ Λ) (D : ChartDatum ξ)
    {n : ℕ∞ω} {w : ℂ} (hw : ξ w ∈ ξ '' D.e.source) : ContDiffAt ℂ n (D.c ∘ ξ) w := by
  obtain ⟨l, hU, hwU, hEq⟩ := D.local_form hfib hw
  have hd : DifferentiableOn ℂ (fun w' => D.e (w' - l)) ((· - l) ⁻¹' D.e.source) := fun w' hw' =>
    ((D.differentiableAt_e hw').comp w' (differentiableAt_id.sub_const l)).differentiableWithinAt
  have := (hd.contDiffOn (n := n) hU).contDiffAt (hU.mem_nhds hwU)
  exact this.congr_of_eventuallyEq (eventually_of_mem (hU.mem_nhds hwU) fun w' hw' => hEq w' hw')

/-- The atlas of a family `A` of chart data, with a choice of chart at each point. -/
def chartedSpaceOf (hc : Continuous ξ) (ho : IsOpenMap ξ) (A : Set (ChartDatum ξ))
    (choice : E → ChartDatum ξ) (hA : ∀ P, choice P ∈ A)
    (hmem : ∀ P, P ∈ ξ '' (choice P).e.source) : ChartedSpace ℂ E where
  atlas := (fun D => D.chart hc ho) '' A
  chartAt P := (choice P).chart hc ho
  mem_chart_source P := hmem P
  chart_mem_atlas P := ⟨_, hA P, rfl⟩

section Manifold

variable (hc : Continuous ξ) (ho : IsOpenMap ξ) (hfib : ∀ z w, ξ z = ξ w ↔ z - w ∈ Λ)
  (A : Set (ChartDatum ξ)) (choice : E → ChartDatum ξ) (hA : ∀ P, choice P ∈ A)
  (hmem : ∀ P, P ∈ ξ '' (choice P).e.source)

include hfib in
theorem transition_contDiffOn (D₁ D₂ : ChartDatum ξ) {n : ℕ∞ω} :
    ContDiffOn ℂ n ((D₁.chart hc ho).symm ≫ₕ (D₂.chart hc ho))
      ((D₁.chart hc ho).symm ≫ₕ (D₂.chart hc ho)).source := by
  refine DifferentiableOn.contDiffOn (fun t ht => ?_) (OpenPartialHomeomorph.open_source _)
  simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    ChartDatum.chart_target, ChartDatum.chart_symm_coe, ChartDatum.chart_source, mem_inter_iff,
    mem_preimage, Function.comp_apply] at ht
  obtain ⟨ht1, ht2⟩ := ht
  have h1 := (D₂.contDiffAt_comp hfib (n := 1) ht2).differentiableAt one_ne_zero
  have h2 := D₁.differentiableAt_symm ht1
  simp only [OpenPartialHomeomorph.coe_trans, ChartDatum.chart_coe, ChartDatum.chart_symm_coe]
  exact (h1.comp t h2).differentiableWithinAt

include hfib in
theorem isManifoldOf :
    @IsManifold ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ω E _ (chartedSpaceOf hc ho A choice hA hmem) := by
  letI := chartedSpaceOf hc ho A choice hA hmem
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨D₁, -, rfl⟩ ⟨D₂, -, rfl⟩
  simpa using transition_contDiffOn hc ho hfib D₁ D₂

include hfib in
theorem contMDiff_of :
    @ContMDiff ℂ _ ℂ _ _ ℂ _ 𝓘(ℂ) ℂ _ _ ℂ _ _ ℂ _ 𝓘(ℂ) E _ (chartedSpaceOf hc ho A choice hA hmem)
      ω ξ := by
  letI := chartedSpaceOf hc ho A choice hA hmem
  intro z
  rw [contMDiffAt_iff]
  refine ⟨hc.continuousAt, ?_⟩
  simp only [extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq, modelWithCornersSelf_coe,
    OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, range_id,
    OpenPartialHomeomorph.toFun_eq_coe, PartialEquiv.coe_trans, Function.id_comp,
    PartialEquiv.coe_trans_symm, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
    modelWithCornersSelf_coe_symm, Function.comp_id, contDiffWithinAt_univ, id_eq]
  exact (choice (ξ z)).contDiffAt_comp hfib (hmem (ξ z))


include hfib in
/-- `ξ` is a local biholomorphism (Mathlib's `IsLocalDiffeomorph` for the model `𝓘(ℂ)` and `C^ω`). -/
theorem isLocalDiffeomorph_of :
    letI := chartedSpaceOf hc ho A choice hA hmem
    IsLocalDiffeomorph 𝓘(ℂ) 𝓘(ℂ) ω ξ := by
  letI := chartedSpaceOf hc ho A choice hA hmem
  intro z
  set D := choice (ξ z)
  obtain ⟨v, hv, hvz⟩ := hmem (ξ z)
  set l := z - v with hl
  have hlΛ : l ∈ Λ := (hfib z v).1 hvz.symm
  have hshift : ∀ w, ξ (w - l) = ξ w := fun w => (hfib _ _).2 (by simpa using neg_mem hlΛ)
  have hshift' : ∀ s, ξ (s + l) = ξ s := fun s => (hfib _ _).2 (by simpa using hlΛ)
  refine ⟨{ toFun := ξ
            invFun := fun Q => D.e.symm (D.c Q) + l
            source := (· - l) ⁻¹' D.e.source
            target := ξ '' D.e.source
            map_source' := fun w hw => ⟨w - l, hw, hshift w⟩
            map_target' := by
              rintro _ ⟨s, hs, rfl⟩
              simp only [mem_preimage, D.eq s hs, D.e.left_inv hs, add_sub_cancel_right]; exact hs
            left_inv' := fun w hw => by
              simp only [mem_preimage] at hw
              simp only [← hshift w, D.eq _ hw, D.e.left_inv hw, sub_add_cancel]
            right_inv' := by
              rintro _ ⟨s, hs, rfl⟩
              simp only [D.eq s hs, D.e.left_inv hs, hshift']
            open_source := D.e.open_source.preimage (continuous_id.sub continuous_const)
            open_target := ho _ D.e.open_source
            contMDiffOn_toFun := (contMDiff_of hc ho hfib A choice hA hmem).contMDiffOn
            contMDiffOn_invFun := ?_ }, ?_, fun w _ => rfl⟩
  · intro Q hQ
    have hQo : (ξ '' D.e.source) ∈ 𝓝 Q := (ho _ D.e.open_source).mem_nhds hQ
    refine ContMDiffAt.contMDiffWithinAt ?_
    rw [contMDiffAt_iff]
    have hcQ : D.c Q ∈ D.e.target := (D.chart hc ho).map_source hQ
    refine ⟨?_, ?_⟩
    · have h1 : ContinuousAt D.c Q := ((D.chart hc ho).continuousOn.continuousAt hQo)
      exact ((D.e.continuousAt_symm hcQ).comp h1).add continuousAt_const
    · simp only [extChartAt, OpenPartialHomeomorph.extend, chartAt_self_eq, modelWithCornersSelf_coe,
        OpenPartialHomeomorph.refl_partialEquiv, PartialEquiv.refl_trans, range_id,
        OpenPartialHomeomorph.toFun_eq_coe, PartialEquiv.coe_trans, Function.id_comp,
        PartialEquiv.coe_trans_symm, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
        modelWithCornersSelf_coe_symm, Function.comp_id, contDiffWithinAt_univ, id_eq]
      set D' := choice Q
      have hQ' := hmem Q
      have ht0 : D'.c Q ∈ D'.e.target := (D'.chart hc ho).map_source hQ'
      have hw0 : ξ (D'.e.symm (D'.c Q)) = Q := (D'.chart hc ho).left_inv hQ'
      have h3 : ContDiffAt ℂ ω D'.e.symm (D'.c Q) := D'.contDiffAt_symm ht0
      have h2 : ContDiffAt ℂ ω (D.c ∘ ξ) (D'.e.symm (D'.c Q)) :=
        D.contDiffAt_comp hfib (by rw [hw0]; exact hQ)
      have h1 : ContDiffAt ℂ ω D.e.symm ((D.c ∘ ξ) (D'.e.symm (D'.c Q))) := by
        simp only [Function.comp_apply, hw0]; exact D.contDiffAt_symm hcQ
      have := (h1.comp (D'.c Q) (h2.comp (D'.c Q) h3)).add (contDiffAt_const (c := l))
      convert this using 1 <;> first | rfl | (funext x; rfl)
  · show z - l ∈ D.e.source
    simpa [hl] using hv

end Manifold

end HCMW
