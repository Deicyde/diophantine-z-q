import ZInQKernel.OneProof.H.TailQ
import ZInQKernel.Contrib.OneProof.SmoothComplexManifoldEtale

/-!
# gaga-chart: `ZInQ.HomLattice.GAGAMorphism` from GAGA in chart form

The textbook field `gagaMorphism : ZInQ.HomLattice.GAGAMorphism` (`ZInQKernel/OneProof/H/TailQ.lean`) states GAGA
for maps of complex abelian varieties with its hypothesis in uniformization form: an analytic homomorphism
`ψ : ℂ^g → B(ℂ)` (`IsAnalyticHom`) killing `Λ`, where `φ : ℂ^g ⧸ Λ ≃ A(ℂ)` is a strong uniformization
(`IsStrongUnif`). The print's hypothesis is a holomorphic map `A^an → B^an`. This file states GAGA with that
hypothesis, over the analytic topology of unif-topology and charts of `A^an`, `B^an` characterized by `IsAnStr`
(the clauses of `UnifTopology.SmoothComplexManifoldAn`, satisfied by sga1-etale's atlas of étale charts), and proves
the field from it:

* `GAGAAn.GAGAChart` (new leaf): a map `A(ℂ) → B(ℂ)` that is holomorphic (`ContMDiff ω`) in such charts is
  `P ↦ P ≫ f` for a morphism `f : A → B`;
* `GAGAAn.gagaMorphism_of_gagaChart : UniformizationLeafAll → GAGAChart → GAGAMorphism` (main theorem); the
  variants `gagaMorphism_of_chart` (charts from `SmoothComplexManifoldAn`) and `gagaMorphism_of_chart_etale`
  (charts from sga1-etale's `SGA1_XII_3_1_Etale`).

The holomorphic inverse function step that the dictionary pass found between the two hypotheses is proved here
(Mathlib's analytic inverse function theorem, `ContDiffAt.to_localInverse` and
`OpenPartialHomeomorph.contDiffAt_symm` at `ω`, applied to `G = Θ ∘ φ ∘ proj` with `Θ` the regular coordinates of
clause (ii) of the uniformization). It is used twice: for `F`, which near `P₀ = φ (proj v₀)` is `ψ ∘ G⁻¹ ∘ Θ`; and
for the charts `Q ↦ Θ Q` on `φ(proj S)` (`exists_rChart`), which give `IsAnStr` charts on `A(ℂ)` from a
uniformization (`exists_isAnStr_of_unif`). `contMDiff_id_of_isAnStr` shows that `IsAnStr` fixes the complex
structure (any two such atlases have the same holomorphic maps), so the leaf is about the complex manifold `A^an`.
Report: `docs/research/gaga-chart.md`.
-/

open scoped Manifold ContDiff Topology
open Set Filter CategoryTheory AlgebraicGeometry Limits MonObj

set_option linter.unusedSectionVars false

noncomputable section

namespace GAGAAn

open UnifPrinted UnifTopology BPAnalytic BPAnalytic.Uniformization
open PkgI3 (AbVar)

/-- The complex-analytic manifold structure of `X^an`: a charted space on `X(ℂ)` (over the given
topology) that is an analytic manifold, in which regular functions are holomorphic on `U(ℂ)`, and
in which some regular functions are local holomorphic coordinates at every point. These are the
three clauses of `UnifTopology.SmoothComplexManifoldAn`. -/
def IsAnStr (X : Over (Spec (CommRingCat.of ℂ))) (n : ℕ) [TopologicalSpace (CPt X)]
    [ChartedSpace (Fin n → ℂ) (CPt X)] : Prop :=
  IsManifold 𝓘(ℂ, Fin n → ℂ) ω (CPt X) ∧
  (∀ (U : X.left.Opens) (f : Γ(X.left, U)),
    ContMDiffOn 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (XevalAt X U f) {P | XPtIn X P U}) ∧
  (∀ P : CPt X, ∃ (U : X.left.Opens) (f : Fin n → Γ(X.left, U)), XPtIn X P U ∧
    IsLocalDiffeomorphAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω (fun Q i => XevalAt X U (f i) Q) P)

/-- **LEAF (printed form, special case): GAGA for maps of complex abelian varieties, chart form.** Let `A`, `B`
be abelian varieties over `ℂ`. Give `A(ℂ)` and `B(ℂ)` the analytic topology (`analyticTopology`, the topology of
`A^an`, `B^an`) and complex analytic manifold structures satisfying `IsAnStr` (the complex structure of `A^an`, `B^an`:
SGA 1 XII 1.1, 3.1; Shafarevich, *BAG 2*, VII §1.1; it exists by `SmoothComplexManifoldAn`, e.g. sga1-etale's étale
charts, and is unique by `contMDiff_id_of_isAnStr`). Then every holomorphic map `F : A(ℂ) → B(ℂ)` (`ContMDiff ω`
in these charts: a morphism of complex manifolds, i.e. of analytic spaces, `A^an → B^an`) comes from a morphism of
schemes `f : A → B`, `F P = P ≫ f`. Serre, GAGA (Ann. Inst. Fourier 6, 1956), for projective varieties (abelian
varieties are projective); SGA 1, Exp. XII, Thm. 4.4 and its corollary on morphisms, for `X` proper over `ℂ`
(`Hom(X, Y) → Hom(X^an, Y^an)` bijective); locators UNVERIFIED. Special case `X = A`, `Y = B` abelian varieties;
uniqueness of `f` dropped. -/
def GAGAChart : Prop :=
  ∀ (A B : AbVar ℂ) (n m : ℕ),
    letI := analyticTopology A.X
    letI := analyticTopology B.X
    ∀ (_ : ChartedSpace (Fin n → ℂ) (CPt A.X)) (_ : ChartedSpace (Fin m → ℂ) (CPt B.X)),
      IsAnStr A.X n → IsAnStr B.X m →
      ∀ F : CPt A.X → CPt B.X, ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F →
        ∃ f : A.X ⟶ B.X, ∀ P, F P = P ≫ f


/-! ## Glue -/

section Glue

variable {X : Over (Spec (CommRingCat.of ℂ))}

/-- **Holomorphy into `X(ℂ)` from regular functions.** A map `G` into `X(ℂ)`, continuous at `x`,
such that every regular function composed with `G` is holomorphic at `x`, is holomorphic at `x`
(through the regular local coordinates of `IsAnStr`). -/
theorem contMDiffAt_of_regular {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {M : Type*} [TopologicalSpace M] [ChartedSpace E M] {m : ℕ}
    [TopologicalSpace (CPt X)] [ChartedSpace (Fin m → ℂ) (CPt X)]
    (hX : IsAnStr X m) (G : M → CPt X) (x : M) (hc : ContinuousAt G x)
    (hreg : ∀ (U : X.left.Opens) (f : Γ(X.left, U)), XPtIn X (G x) U →
      ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (fun y => XevalAt X U f (G y)) x) :
    ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin m → ℂ) ω G x := by
  obtain ⟨hMan, -, hcoords⟩ := hX
  have := hMan
  obtain ⟨U, f, hU, hloc⟩ := hcoords (G x)
  set c : CPt X → (Fin m → ℂ) := fun Q i => XevalAt X U (f i) Q
  have hcG : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, Fin m → ℂ) ω (fun y => c (G y)) x :=
    contMDiffAt_pi_module_iff.mpr fun i => hreg U (f i) hU
  have hinv := hloc.contMDiffAt_localInverse
  have heq : G =ᶠ[𝓝 x] (fun y => hloc.localInverse (c (G y))) := by
    have h2 := hloc.localInverse_eventuallyEq_left.comp_tendsto hc
    filter_upwards [h2] with y hy
    exact hy.symm
  exact (hinv.comp x hcG).congr_of_eventuallyEq heq

/-- An analytic homomorphism `ℂ^n → B(ℂ)` is continuous for the classical topology. -/
theorem continuous_analyticHom {B : AbVar ℂ} {n : ℕ} {ψ : (Fin n → ℂ) → CPt B.X}
    (hψ : ZInQ.HomLattice.IsAnalyticHom (RingHom.id ℂ) ψ) :
    Continuous[_, classicalTopology B.X] ψ := by
  let _ := classicalTopology B.X
  refine continuous_generateFrom_iff.mpr ?_
  rintro _ ⟨V, g, w, ε, rfl⟩
  have hev : ∀ z, XevalAt B.X V g (ψ z) = ZInQ.LeafPush2.cEvalAt (ψ z) V g := fun z =>
    (ZInQ.LeafPush2.cEvalAt_eq_evalAt B (ψ z) V g).symm
  have hO : IsOpen (ZInQ.LeafPush2.cDom ψ V ∩
      (fun z => ZInQ.LeafPush2.cEvalAt (ψ z) V g) ⁻¹' Metric.ball w ε) :=
    (hψ.2.2 V g).continuousOn.isOpen_inter_preimage (hψ.2.1 V) Metric.isOpen_ball
  convert hO using 1
  ext z
  simp only [mem_preimage, mem_inter_iff, Metric.mem_ball, dist_eq_norm, ← hev]
  rfl

/-- `φ⁻¹` is continuous for the classical topology (clause (iii) of a uniformization). -/
theorem continuousAt_symm {A : AbVar ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} (hφ : IsUniformization A Λ φ) (P₀ : CPt A.X) :
    @ContinuousAt _ _ (classicalTopology A.X) _ (fun P : CPt A.X => φ.symm (Additive.ofMul P)) P₀ := by
  let _ := classicalTopology A.X
  set v₀ := (φ.symm (Additive.ofMul P₀)).out
  have hv₀ : proj Λ v₀ = φ.symm (Additive.ofMul P₀) := QuotientAddGroup.out_eq' _
  have hP₀ : Additive.toMul (φ (proj Λ v₀)) = P₀ := by
    rw [hv₀, AddEquiv.apply_symm_apply]; rfl
  intro N hN
  replace hN : N ∈ 𝓝 (proj Λ v₀) := by rw [hv₀]; exact hN
  obtain ⟨U, k, f, ε, hε, hU, hsep⟩ := hφ.open_map v₀ N hN
  rw [hP₀] at hU hsep
  set S := {P : CPt A.X | XPtIn A.X P U} ∩
    ⋂ i, {P | XPtIn A.X P U ∧ ‖XevalAt A.X U (f i) P - XevalAt A.X U (f i) P₀‖ < ε}
  have hS : IsOpen S :=
    (isOpen_ptIn U).inter (isOpen_iInter_of_finite fun i => isOpen_basic _ _ _)
  have hP₀S : P₀ ∈ S := ⟨hU, mem_iInter.mpr fun i => ⟨hU, by simpa using hε⟩⟩
  rw [Filter.mem_map]
  refine Filter.mem_of_superset (hS.mem_nhds hP₀S) ?_
  rintro P ⟨hPU, hPi⟩
  obtain ⟨q, hq, hqP⟩ := hsep P hPU fun i => (mem_iInter.mp hPi i).2
  show φ.symm (Additive.ofMul P) ∈ N
  rw [← hqP]
  simpa using hq

end Glue

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

/-! ## Main theorem -/

/-- **GLUE (proved twice below, `exists_isAnStr_of_unif` and `SmoothComplexManifoldAn`):** every complex abelian
variety has charts on `A(ℂ)` (analytic topology) satisfying `IsAnStr`. -/
def IsAnStrExists : Prop :=
  ∀ A : AbVar ℂ, letI := analyticTopology A.X
    ∃ (n : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt A.X)), IsAnStr A.X n

/-- **`GAGAMorphism` from the chart form of GAGA (proved).** The hypothesis of `GAGAMorphism`
(an analytic homomorphism `ψ : ℂ^g → B(ℂ)` killing `Λ`, given through a strong uniformization `φ`
of `A`) gives a map `F : A(ℂ) → B(ℂ)`, `F (φ (proj v)) = ψ v`, holomorphic in any charts of `A^an`
and `B^an` (`IsAnStr`): near `P₀ = φ (proj v₀)`, `F = ψ ∘ L ∘ Θ` with `Θ` regular coordinates of `A`
(clause (ii) of the uniformization) and `L` the analytic local inverse of `Θ ∘ φ ∘ proj` (analytic
inverse function theorem). The charts exist by `SmoothComplexManifoldAn`; the analyticity of `ψ`
comes from a uniformization of `B` (`ψ = φ_B ∘ proj ∘ D`, `D` linear). -/
theorem gagaMorphism_of_chart_core (hU : UniformizationLeafAll) (hEx : IsAnStrExists)
    (hG : GAGAChart) : ZInQ.HomLattice.GAGAMorphism := by
  intro A B g Λ _ φ hφs ψ hψ hker
  have hφ : IsUniformization A Λ φ := ZInQ.HomLattice.bp_of_isStrongUnif hφs
  obtain ⟨g', ΛB, hdB, -, φB, hφB⟩ := hU B
  obtain ⟨D, hD⟩ := ZInQ.HomLattice.exists_complexLinear_of_analytic_strong
    (ZInQ.HomLattice.isStrongUnif_of_bp hφB) hψ
  let tA : TopologicalSpace (CPt A.X) := analyticTopology A.X
  let tB : TopologicalSpace (CPt B.X) := analyticTopology B.X
  obtain ⟨n, cA, hA⟩ := hEx A
  obtain ⟨m, cB, hB⟩ := hEx B
  have hA' : IsAnStr A.X n := hA
  have hB' : IsAnStr B.X m := hB
  -- `ψ` is constant on `Λ`-cosets
  let ψ' : (Fin g → ℂ) → CPt B.X := ψ
  have hψ' : ZInQ.HomLattice.IsAnalyticHom (RingHom.id ℂ) ψ' := hψ
  have hψΛ : ∀ v w : Fin g → ℂ, v - w ∈ Λ → ψ' v = ψ' w := by
    intro v w h
    have := hψ.1 w (v - w)
    rw [add_sub_cancel, hker _ h, _root_.mul_one] at this
    exact this
  let Φ : (Fin g → ℂ) → CPt A.X := fun v => Additive.toMul (φ (proj Λ v))
  let F : CPt A.X → CPt B.X := fun P => ψ' (φ.symm (Additive.ofMul P)).out
  have hFψ : ∀ v, F (Φ v) = ψ' v := by
    intro v
    show ψ' (φ.symm (Additive.ofMul (Additive.toMul (φ (proj Λ v))))).out = ψ' v
    rw [ofMul_toMul, AddEquiv.symm_apply_apply]
    apply hψΛ
    have h := QuotientAddGroup.out_eq' (proj Λ v)
    rw [QuotientAddGroup.eq_iff_sub_mem] at h
    simpa using h
  have hDv : ∀ z, ψ' z = Additive.toMul (φB (proj ΛB (D z))) := fun z => (hD z).symm
  have hF : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F := by
    intro P₀
    set q₀ := φ.symm (Additive.ofMul P₀) with hq₀
    set v₀ := q₀.out with hv₀def
    have hv₀ : proj Λ v₀ = q₀ := QuotientAddGroup.out_eq' _
    have hP₀ : Φ v₀ = P₀ := by
      show Additive.toMul (φ (proj Λ v₀)) = P₀
      rw [hv₀, hq₀, AddEquiv.apply_symm_apply]; rfl
    obtain ⟨U, fA, e, hU0, hder⟩ := hφ.coords v₀
    have hU : XPtIn A.X P₀ U := by rw [← hP₀]; exact hU0
    set Gf : (Fin g → ℂ) → (Fin g → ℂ) :=
      fun v i => evalAt A U (fA i) (Additive.toMul (φ (proj Λ v))) with hGf
    have hGa : AnalyticAt ℂ Gf v₀ := AnalyticAt.pi fun i => (hφ.holo U (fA i)).2 v₀ hU0
    have hGc : ContDiffAt ℂ ω Gf v₀ := hGa.contDiffAt
    have hn : (ω : WithTop ℕ∞) ≠ 0 := by simp
    set L := hGc.localInverse hder hn with hLdef
    have hL : ContDiffAt ℂ ω L (Gf v₀) := hGc.to_localInverse hder hn
    have hs' := hGc.hasStrictFDerivAt' hder hn
    have hLG : ∀ᶠ v in 𝓝 v₀, L (Gf v) = v := hs'.eventually_left_inverse
    have hLv₀ : L (Gf v₀) = v₀ := hGc.localInverse_apply_image hder hn
    set Θ : CPt A.X → (Fin g → ℂ) := fun P i => XevalAt A.X U (fA i) P with hΘdef
    have hΘG : ∀ v, Θ (Φ v) = Gf v := fun v => rfl
    have hΘP₀ : Θ P₀ = Gf v₀ := by rw [← hΘG v₀, hP₀]
    -- `F = ψ ∘ L ∘ Θ` near `P₀`
    have hloc : F =ᶠ[𝓝 P₀] fun P => ψ' (L (Θ P)) := by
      have h1 : proj Λ '' {v | L (Gf v) = v} ∈ 𝓝 q₀ := by
        rw [← hv₀]; exact QuotientAddGroup.isOpenMap_coe.image_mem_nhds hLG
      have hc : ContinuousAt (fun P : CPt A.X => φ.symm (Additive.ofMul P)) P₀ := by
        have := continuousAt_symm hφ P₀
        rwa [classicalTopology_eq_analyticTopology] at this
      filter_upwards [hc h1] with P hP
      obtain ⟨v, hv, hvP⟩ := hP
      have hPv : P = Φ v := by
        show P = Additive.toMul (φ (proj Λ v))
        rw [hvP, AddEquiv.apply_symm_apply]; rfl
      rw [hPv, hFψ, hΘG, hv]
    have hΘ : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin g → ℂ) ω Θ P₀ := by
      refine contMDiffAt_pi_module_iff.mpr fun i => ?_
      exact (hA'.2.1 U (fA i) P₀ hU).contMDiffAt ((SGA1Etale.isOpen_ptIn_an U).mem_nhds hU)
    have hLΘ : ContinuousAt (fun P => L (Θ P)) P₀ := by
      have hLc : ContinuousAt L (Θ P₀) := by rw [hΘP₀]; exact hL.continuousAt
      exact hLc.comp hΘ.continuousAt
    have hLΘP₀ : L (Θ P₀) = v₀ := by rw [hΘP₀, hLv₀]
    refine contMDiffAt_of_regular hB' F P₀ ?_ ?_
    · have hψc : Continuous ψ' := by
        have := continuous_analyticHom (B := B) (ψ := ψ') hψ'
        rwa [classicalTopology_eq_analyticTopology] at this
      have h2 : ContinuousAt (fun P => ψ' (L (Θ P))) P₀ := hψc.continuousAt.comp hLΘ
      exact h2.congr hloc.symm
    · intro V g₀ hV
      have hFP₀ : F P₀ = ψ' v₀ := by rw [← hP₀, hFψ]
      have hh : AnalyticAt ℂ (fun z => XevalAt B.X V g₀ (ψ' z)) v₀ := by
        have hV' : PtIn B (Additive.toMul (φB (proj ΛB (D v₀)))) V := by
          rw [← hDv, ← hFP₀]; exact hV
        have h1 := (hφB.holo V g₀).2 (D v₀) hV'
        have h2 : AnalyticAt ℂ
            (fun z => evalAt B V g₀ (Additive.toMul (φB (proj ΛB (D z))))) v₀ :=
          h1.comp (D.analyticAt v₀)
        refine h2.congr (Eventually.of_forall fun z => ?_)
        show evalAt B V g₀ (Additive.toMul (φB (proj ΛB (D z)))) = XevalAt B.X V g₀ (ψ' z)
        rw [hDv z]; rfl
      have hcomp : ContDiffAt ℂ ω (fun w => XevalAt B.X V g₀ (ψ' (L w))) (Θ P₀) := by
        have hh' : ContDiffAt ℂ ω (fun z => XevalAt B.X V g₀ (ψ' z)) (L (Θ P₀)) := by
          rw [hLΘP₀]; exact hh.contDiffAt
        have hL' : ContDiffAt ℂ ω L (Θ P₀) := by rw [hΘP₀]; exact hL
        exact hh'.comp (Θ P₀) hL'
      have h3 := (contMDiffAt_iff_contDiffAt.mpr hcomp).comp P₀ hΘ
      refine h3.congr_of_eventuallyEq ?_
      filter_upwards [hloc] with P hP
      simp only [Function.comp_apply, hP]
  obtain ⟨f, hf⟩ := hG A B n m cA cB hA' hB' F hF
  refine ⟨f, fun z => ?_⟩
  exact (hFψ z).symm.trans (hf (Φ z))

/-- **`IsAnStr` charts exist on `A(ℂ)`, from a uniformization of `A` (proved).** -/
theorem exists_isAnStr_of_unif {A : AbVar ℂ} {g : ℕ} {Λ : Submodule ℤ (Fin g → ℂ)}
    [DiscreteTopology Λ] {φ : Torus Λ ≃+ Additive (A.Pt ℂ)} (hφ : IsUniformization A Λ φ) :
    letI := analyticTopology A.X
    ∃ (n : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt A.X)), IsAnStr A.X n := by
  have key : letI := classicalTopology A.X
      ∃ (n : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt A.X)), IsAnStr A.X n := by
    letI := classicalTopology A.X
    choose ch hch using exists_rChart hφ
    exact ⟨g, rChartedSpace ch hch,
      isAnStr_rChart ch hch (fun W f => continuousOn_xevalAt W f) isOpen_ptIn⟩
  rw [classicalTopology_eq_analyticTopology] at key
  exact key

/-- **Main theorem: `GAGAMorphism` from the chart form of GAGA (proved).** The only other input is
the textbook field `uniformizationLeafAll`, which the consumers of `gagaMorphism` already take: it gives
the analyticity of `ψ`, and charts on `A(ℂ)`, `B(ℂ)` satisfying `IsAnStr` (`exists_isAnStr_of_unif`). -/
theorem gagaMorphism_of_gagaChart (hU : UniformizationLeafAll) (hG : GAGAChart) :
    ZInQ.HomLattice.GAGAMorphism := by
  refine gagaMorphism_of_chart_core hU (fun A => ?_) hG
  obtain ⟨g, Λ, _, -, φ, hφ⟩ := hU A
  exact exists_isAnStr_of_unif hφ

/-- **`GAGAMorphism` from the chart form of GAGA, charts from `SmoothComplexManifoldAn` (proved).** -/
theorem gagaMorphism_of_chart (hU : UniformizationLeafAll) (hMan : SmoothComplexManifoldAn)
    (hG : GAGAChart) : ZInQ.HomLattice.GAGAMorphism :=
  gagaMorphism_of_chart_core hU (fun A => hMan A.X inferInstance inferInstance inferInstance) hG

/-! ## The structure `IsAnStr` is unique, and sga1-etale's charts have it -/

/-- **Uniqueness of the analytic structure (proved).** Two charted-space structures on `X(ℂ)`, over
the same topology in which every `U(ℂ)` is open, both satisfying `IsAnStr`, have the same
holomorphic maps: the identity is holomorphic from either to the other. So `IsAnStr` pins down the
complex structure of `X^an`, and a map holomorphic for one choice is holomorphic for every choice. -/
theorem contMDiff_id_of_isAnStr {X : Over (Spec (CommRingCat.of ℂ))} {n m : ℕ}
    [t : TopologicalSpace (CPt X)] (hopen : ∀ U : X.left.Opens, IsOpen {P : CPt X | XPtIn X P U})
    (c₁ : ChartedSpace (Fin n → ℂ) (CPt X)) (c₂ : ChartedSpace (Fin m → ℂ) (CPt X))
    (h₁ : @IsAnStr X n t c₁) (h₂ : @IsAnStr X m t c₂) :
    @ContMDiff _ _ _ _ _ _ _ 𝓘(ℂ, Fin n → ℂ) (CPt X) t c₁ _ _ _ _ _ 𝓘(ℂ, Fin m → ℂ) (CPt X) t c₂
      ω (id : CPt X → CPt X) := by
  intro P
  refine @contMDiffAt_of_regular X (Fin n → ℂ) _ _ (CPt X) t c₁ m t c₂ h₂ id P
    continuousAt_id fun U f hP => ?_
  exact (h₁.2.1 U f P hP).contMDiffAt ((hopen U).mem_nhds hP)

/-- GAGA in chart form for *some* `IsAnStr` charts on `A(ℂ)` and `B(ℂ)` (for instance those of `A^an`,
`B^an`). -/
def GAGAChartSome : Prop :=
  ∀ (A B : AbVar ℂ),
    letI := analyticTopology A.X
    letI := analyticTopology B.X
    ∃ (n m : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt A.X)) (_ : ChartedSpace (Fin m → ℂ) (CPt B.X)),
      IsAnStr A.X n ∧ IsAnStr B.X m ∧
      ∀ F : CPt A.X → CPt B.X, ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin m → ℂ) ω F →
        ∃ f : A.X ⟶ B.X, ∀ P, F P = P ≫ f

/-- **The quantifier over charts in `GAGAChart` adds nothing (proved).** GAGA for one choice of
`IsAnStr` charts gives it for every choice (`contMDiff_id_of_isAnStr`). -/
theorem gagaChart_of_some (h : GAGAChartSome) : GAGAChart := by
  intro A B n m cA cB hA hB F hF
  let tA := analyticTopology A.X
  let tB := analyticTopology B.X
  obtain ⟨n₀, m₀, cA₀, cB₀, hA₀, hB₀, hG⟩ := h A B
  have iA := @contMDiff_id_of_isAnStr A.X n₀ n tA (SGA1Etale.isOpen_ptIn_an) cA₀ cA hA₀ hA
  have iB := @contMDiff_id_of_isAnStr B.X m m₀ tB (SGA1Etale.isOpen_ptIn_an) cB cB₀ hB hB₀
  have inner := @ContMDiff.comp ℂ _ (Fin n₀ → ℂ) _ _ (Fin n₀ → ℂ) _ 𝓘(ℂ, Fin n₀ → ℂ) (CPt A.X) tA
    (Fin n → ℂ) _ _ (Fin n → ℂ) _ 𝓘(ℂ, Fin n → ℂ) (CPt A.X) tA
    (Fin m → ℂ) _ _ (Fin m → ℂ) _ 𝓘(ℂ, Fin m → ℂ) (CPt B.X) tB cA₀ cA cB id ω F hF iA
  have hF₀ := @ContMDiff.comp ℂ _ (Fin n₀ → ℂ) _ _ (Fin n₀ → ℂ) _ 𝓘(ℂ, Fin n₀ → ℂ) (CPt A.X) tA
    (Fin m → ℂ) _ _ (Fin m → ℂ) _ 𝓘(ℂ, Fin m → ℂ) (CPt B.X) tB
    (Fin m₀ → ℂ) _ _ (Fin m₀ → ℂ) _ 𝓘(ℂ, Fin m₀ → ℂ) (CPt B.X) tB cA₀ cB cB₀ (F ∘ id) ω id iB inner
  exact hG F hF₀

/-- sga1-etale's analytic structure (the atlas of étale charts, `SGA1Etale.chartedSpaceOf`) satisfies
`IsAnStr` (proved there, from the étale clause of SGA 1 XII 3.1). -/
theorem isAnStr_of_etale (hL : SGA1Etale.SGA1_XII_3_1_Etale) (X : Over (Spec (CommRingCat.of ℂ)))
    [Smooth X.hom] [IsProper X.hom] [IrreducibleSpace X.left] :
    letI := analyticTopology X
    ∃ (n : ℕ) (_ : ChartedSpace (Fin n → ℂ) (CPt X)), IsAnStr X n :=
  SGA1Etale.smoothComplexManifoldAn_of_etale hL X inferInstance inferInstance inferInstance

/-- **`GAGAMorphism` from the chart form of GAGA, with sga1-etale's charts (proved).** -/
theorem gagaMorphism_of_chart_etale (hU : UniformizationLeafAll)
    (hL : SGA1Etale.SGA1_XII_3_1_Etale) (hG : GAGAChart) : ZInQ.HomLattice.GAGAMorphism :=
  gagaMorphism_of_chart hU (SGA1Etale.smoothComplexManifoldAn_of_etale hL) hG


end GAGAAn

