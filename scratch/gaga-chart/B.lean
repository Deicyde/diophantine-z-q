import ZInQKernel.Contrib.OneProof.GAGAChart

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj

set_option linter.unusedSectionVars false

noncomputable section

namespace GAGAAn

open UnifPrinted UnifTopology BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-! ## An analytic structure on `X(ℂ)` from charts by regular functions -/

section RChart

variable {X : Over (Spec (CommRingCat.of ℂ))}

/-- Regular functions are continuous on `U(ℂ)` for the classical topology. -/
theorem continuousOn_xevalAt (U : X.left.Opens) (f : Γ(X.left, U)) :
    @ContinuousOn _ _ (classicalTopology X) _ (XevalAt X U f) {P | XPtIn X P U} := by
  let _ := classicalTopology X
  intro P hP
  apply ContinuousAt.continuousWithinAt
  rw [Metric.continuousAt_iff']
  intro ε hε
  have h := (isOpen_basic f (XevalAt X U f P) ε).mem_nhds (x := P) ⟨hP, by simpa using hε⟩
  filter_upwards [h] with Q hQ
  rw [dist_eq_norm]; exact hQ.2

/-- A chart of `X(ℂ)` given by regular functions `f` on `U`, in which every regular function has an
analytic representation. -/
structure RChart (X : Over (Spec (CommRingCat.of ℂ))) [TopologicalSpace (CPt X)] (n : ℕ) where
  U : X.left.Opens
  f : Fin n → Γ(X.left, U)
  e : OpenPartialHomeomorph (CPt X) (Fin n → ℂ)
  hsrc : e.source ⊆ {Q | XPtIn X Q U}
  heq : ∀ Q ∈ e.source, e Q = fun i => XevalAt X U (f i) Q
  hrep : ∀ (W : X.left.Opens) (h : Γ(X.left, W)) (w : Fin n → ℂ), w ∈ e.target →
    XPtIn X (e.symm w) W → ContDiffAt ℂ ω (fun w' => XevalAt X W h (e.symm w')) w

variable [TopologicalSpace (CPt X)] {n : ℕ}

/-- The charted space structure given by a choice of charts. -/
def rChartedSpace (ch : CPt X → RChart X n) (hch : ∀ P, P ∈ (ch P).e.source) :
    ChartedSpace (Fin n → ℂ) (CPt X) where
  atlas := Set.range fun P => (ch P).e
  chartAt P := (ch P).e
  mem_chart_source := hch
  chart_mem_atlas P := ⟨P, rfl⟩

theorem hrep_pi (c : RChart X n) {W : X.left.Opens} {m : ℕ} (h : Fin m → Γ(X.left, W))
    {w : Fin n → ℂ} (hw : w ∈ c.e.target) (hW : XPtIn X (c.e.symm w) W) :
    ContDiffAt ℂ ω (fun w' i => XevalAt X W (h i) (c.e.symm w')) w :=
  contDiffAt_pi.mpr fun i => c.hrep W (h i) w hw hW

theorem isManifold_rChart (ch : CPt X → RChart X n) (hch : ∀ P, P ∈ (ch P).e.source) :
    @IsManifold _ _ _ _ _ _ _ 𝓘(ℂ, Fin n → ℂ) ω (CPt X) _ (rChartedSpace ch hch) := by
  letI := rChartedSpace ch hch
  apply isManifold_of_contDiffOn
  rintro _ _ ⟨P, rfl⟩ ⟨P', rfl⟩
  simp only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, range_id, preimage_id,
    inter_univ, Function.id_comp, Function.comp_id]
  intro w hw
  apply ContDiffAt.contDiffWithinAt
  have hw' : w ∈ (ch P).e.target ∧ (ch P).e.symm w ∈ (ch P').e.source := by
    simpa [OpenPartialHomeomorph.trans_source] using hw
  have hH := hrep_pi (ch P) (ch P').f hw'.1 ((ch P').hsrc hw'.2)
  refine hH.congr_of_eventuallyEq ?_
  filter_upwards [((ch P).e.symm ≫ₕ (ch P').e).open_source.mem_nhds hw] with w' h2
  have h2' : (ch P).e.symm w' ∈ (ch P').e.source := by
    simp only [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source, mem_inter_iff,
      mem_preimage] at h2
    exact h2.2
  simp only [OpenPartialHomeomorph.coe_trans, Function.comp_apply]
  rw [(ch P').heq _ h2']

theorem contMDiffOn_xevalAt_rChart (ch : CPt X → RChart X n) (hch : ∀ P, P ∈ (ch P).e.source)
    (hcont : ∀ (W : X.left.Opens) (g : Γ(X.left, W)), ContinuousOn (XevalAt X W g) {P | XPtIn X P W})
    (hopen : ∀ W : X.left.Opens, IsOpen {P : CPt X | XPtIn X P W})
    (W : X.left.Opens) (g : Γ(X.left, W)) :
    letI := rChartedSpace ch hch
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X W g) {P | XPtIn X P W} := by
  letI := rChartedSpace ch hch
  intro P hP
  apply ContMDiffAt.contMDiffWithinAt
  rw [contMDiffAt_iff]
  have hPs := hch P
  have hw : (ch P).e P ∈ (ch P).e.target := (ch P).e.map_source hPs
  have hh := (ch P).hrep W g _ hw (by rw [(ch P).e.left_inv hPs]; exact hP)
  constructor
  · exact (hcont W g P hP).continuousAt ((hopen W).mem_nhds hP)
  · have hc : (chartAt (Fin n → ℂ) P) = (ch P).e := rfl
    simp only [extChartAt, OpenPartialHomeomorph.extend, hc, modelWithCornersSelf_coe,
      modelWithCornersSelf_coe_symm, range_id, PartialEquiv.coe_trans, PartialEquiv.coe_trans_symm,
      OpenPartialHomeomorph.toFun_eq_coe, OpenPartialHomeomorph.coe_toPartialEquiv_symm,
      ModelWithCorners.toPartialEquiv_coe, ModelWithCorners.toPartialEquiv_coe_symm,
      Function.id_comp, Function.comp_id, chartAt_self_eq, Function.comp_apply]
    exact hh.contDiffWithinAt

/-- **`IsAnStr` from a covering family of regular charts (proved).** -/
theorem isAnStr_rChart (ch : CPt X → RChart X n) (hch : ∀ P, P ∈ (ch P).e.source)
    (hcont : ∀ (W : X.left.Opens) (g : Γ(X.left, W)), ContinuousOn (XevalAt X W g) {P | XPtIn X P W})
    (hopen : ∀ W : X.left.Opens, IsOpen {P : CPt X | XPtIn X P W}) :
    @IsAnStr X n _ (rChartedSpace ch hch) := by
  letI := rChartedSpace ch hch
  haveI := isManifold_rChart ch hch
  refine ⟨isManifold_rChart ch hch, fun W g => contMDiffOn_xevalAt_rChart ch hch hcont hopen W g,
    fun P => ⟨(ch P).U, (ch P).f, (ch P).hsrc (hch P), ?_⟩⟩
  let D : PartialDiffeomorph 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) (CPt X) (Fin n → ℂ) ω :=
    { toPartialEquiv := (ch P).e.toPartialEquiv
      open_source := (ch P).e.open_source
      open_target := (ch P).e.open_target
      contMDiffOn_toFun := contMDiffOn_chart (x := P)
      contMDiffOn_invFun := contMDiffOn_chart_symm (x := P) }
  refine ⟨D, hch P, fun Q hQ => ?_⟩
  exact ((ch P).heq Q hQ).symm

end RChart

end GAGAAn
