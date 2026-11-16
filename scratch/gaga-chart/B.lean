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

/-! ## Regular charts from a uniformization -/

section Unif

variable {A : AbVar ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)} [DiscreteTopology Λ]
  {φ : Torus Λ ≃+ Additive (A.Pt ℂ)}

/-- `v ↦ φ (proj v)`, as a map `ℂ^g → A(ℂ)`. -/
def uPt (φ : Torus Λ ≃+ Additive (A.Pt ℂ)) (v : Fin g → ℂ) : CPt A.X :=
  Additive.toMul (φ (proj Λ v))

theorem continuous_uPt (hφ : IsUniformization A Λ φ) :
    @Continuous _ _ _ (classicalTopology A.X) (uPt φ) := by
  let _ := classicalTopology A.X
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨W, f, z, ε, rfl⟩
  have h := hφ.holo W f
  have hO : IsOpen ({v | PtIn A (uPt φ v) W} ∩
      (fun v => evalAt A W f (uPt φ v)) ⁻¹' Metric.ball z ε) :=
    h.2.continuousOn.isOpen_inter_preimage h.1 Metric.isOpen_ball
  convert hO using 1
  ext v
  simp only [mem_preimage, mem_inter_iff, Metric.mem_ball, dist_eq_norm]
  rfl

theorem continuous_symm (hφ : IsUniformization A Λ φ) :
    @Continuous _ _ (classicalTopology A.X) _ (fun P : CPt A.X => φ.symm (Additive.ofMul P)) := by
  let _ := classicalTopology A.X
  exact continuous_iff_continuousAt.mpr fun P => continuousAt_symm hφ P

theorem uPt_image_eq (S : Set (Fin g → ℂ)) :
    uPt φ '' S = (fun P : CPt A.X => φ.symm (Additive.ofMul P)) ⁻¹' (proj Λ '' S) := by
  ext P
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, by simp [uPt]⟩
  · rintro ⟨v, hv, hvP⟩
    refine ⟨v, hv, ?_⟩
    show Additive.toMul (φ (proj Λ v)) = P
    rw [hvP, AddEquiv.apply_symm_apply]; rfl

/-- **A regular chart at every point, from a uniformization (proved).** Clause (ii) gives regular
functions `f` on `U ∋ P₀` with `G = f ∘ φ ∘ proj` of invertible derivative at `v₀`; the inverse function
theorem makes `G` a homeomorphism from a neighbourhood `S` of `v₀` (on which `dG` stays invertible)
onto an open set, and `Q ↦ f(Q)` is a homeomorphism from `φ(proj S)` onto `G(S)`, with inverse
`φ ∘ proj ∘ G⁻¹`; regular functions are analytic in it (clause (i) and the analytic inverse function
theorem at each point of `G(S)`). -/
theorem exists_rChart (hφ : IsUniformization A Λ φ) (P₀ : CPt A.X) :
    letI := classicalTopology A.X
    ∃ c : RChart A.X g, P₀ ∈ c.e.source := by
  letI := classicalTopology A.X
  set v₀ := (φ.symm (Additive.ofMul P₀)).out
  have hv₀ : proj Λ v₀ = φ.symm (Additive.ofMul P₀) := QuotientAddGroup.out_eq' _
  have hP₀ : uPt φ v₀ = P₀ := by
    show Additive.toMul (φ (proj Λ v₀)) = P₀
    rw [hv₀, AddEquiv.apply_symm_apply]; rfl
  obtain ⟨U, fA, e, hU0, hder⟩ := hφ.coords v₀
  set O : Set (Fin g → ℂ) := {v | PtIn A (uPt φ v) U} with hOdef
  have hO : IsOpen O := (hφ.holo U 0).1
  set Gf : (Fin g → ℂ) → (Fin g → ℂ) := fun v i => evalAt A U (fA i) (uPt φ v) with hGf
  have hGa : AnalyticOnNhd ℂ Gf O := fun v hv => AnalyticAt.pi fun i => (hφ.holo U (fA i)).2 v hv
  have hGc : ContDiffOn ℂ ω Gf O := hGa.contDiffOn hO.uniqueDiffOn
  have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
  have hs : HasStrictFDerivAt Gf (e : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) v₀ :=
    (hGa v₀ hU0).contDiffAt.hasStrictFDerivAt' hder hn
  set h := hs.toOpenPartialHomeomorph Gf with hhdef
  have hcoe : (h : (Fin g → ℂ) → (Fin g → ℂ)) = Gf := hs.toOpenPartialHomeomorph_coe
  set S : Set (Fin g → ℂ) := h.source ∩ (O ∩ {v | (fderiv ℂ Gf v).IsInvertible}) with hSdef
  have hSo : IsOpen S := by
    refine h.open_source.inter ?_
    exact (hGc.continuousOn_fderiv_of_isOpen hO (by simp)).isOpen_inter_preimage hO
      ContinuousLinearMap.isOpen_setOfPred_isInvertible
  have hv₀S : v₀ ∈ S := ⟨hs.mem_toOpenPartialHomeomorph_source, hU0, ⟨e, hder.fderiv.symm⟩⟩
  have hSh : S ⊆ h.source := inter_subset_left
  have hΘ : ∀ v, (fun i => XevalAt A.X U (fA i) (uPt φ v)) = h v := by
    intro v; rw [hcoe]; rfl
  let E : OpenPartialHomeomorph (CPt A.X) (Fin g → ℂ) :=
    { toFun := fun P i => XevalAt A.X U (fA i) P
      invFun := fun w => uPt φ (h.symm w)
      source := uPt φ '' S
      target := h '' S
      map_source' := by
        rintro _ ⟨v, hv, rfl⟩
        exact ⟨v, hv, (hΘ v).symm⟩
      map_target' := by
        rintro _ ⟨v, hv, rfl⟩
        refine ⟨v, hv, ?_⟩
        show uPt φ v = uPt φ (h.symm (h v))
        rw [h.left_inv (hSh hv)]
      left_inv' := by
        rintro _ ⟨v, hv, rfl⟩
        show uPt φ (h.symm (fun i => XevalAt A.X U (fA i) (uPt φ v))) = uPt φ v
        rw [hΘ v, h.left_inv (hSh hv)]
      right_inv' := by
        rintro _ ⟨v, hv, rfl⟩
        show (fun i => XevalAt A.X U (fA i) (uPt φ (h.symm (h v)))) = h v
        rw [h.left_inv (hSh hv), hΘ v]
      open_source := by
        rw [uPt_image_eq]
        exact (QuotientAddGroup.isOpenMap_coe _ hSo).preimage (continuous_symm hφ)
      open_target := h.isOpen_image_of_subset_source hSo hSh
      continuousOn_toFun := by
        refine continuousOn_pi.mpr fun i => (continuousOn_xevalAt U (fA i)).mono ?_
        rintro _ ⟨v, hv, rfl⟩
        exact hv.2.1
      continuousOn_invFun := by
        refine (continuous_uPt hφ).comp_continuousOn (h.continuousOn_symm.mono ?_)
        rintro _ ⟨v, hv, rfl⟩
        exact h.map_source (hSh hv) }
  refine ⟨⟨U, fA, E, ?_, fun Q _ => rfl, ?_⟩, ⟨v₀, hv₀S, hP₀⟩⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact hv.2.1
  · rintro W g₀ w ⟨v, hv, rfl⟩ hW
    have hvL : h.symm (h v) = v := h.left_inv (hSh hv)
    -- `h⁻¹` is analytic at `h v`
    obtain ⟨e', he'⟩ := hv.2.2
    have hL : ContDiffAt ℂ ω h.symm (h v) := by
      refine h.contDiffAt_symm (f₀' := e') (h.map_source (hSh hv)) ?_ ?_
      · rw [hvL, he', hcoe]
        exact ((hGa v hv.2.1).differentiableAt).hasFDerivAt
      · rw [hvL, hcoe]; exact (hGa v hv.2.1).contDiffAt
    have hW' : PtIn A (uPt φ (h.symm (h v))) W := hW
    have hg : ContDiffAt ℂ ω (fun v' => evalAt A W g₀ (uPt φ v')) (h.symm (h v)) :=
      ((hφ.holo W g₀).2 _ hW').contDiffAt
    exact hg.comp (h v) hL

end Unif

end GAGAAn
