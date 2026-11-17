import ZInQKernel.Contrib.OneProof.ShimuraMainCM

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


/-! ## Generic chart datum from an analytic local coordinate -/

theorem exists_chartDatum (c : E → ℂ) {U : Set ℂ} (hU : IsOpen U) {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    {H : ℂ → ℂ} (hH : AnalyticOnNhd ℂ H U) (hd : deriv H z₀ ≠ 0)
    (heq : ∀ z ∈ U, c (ξ z) = H z) : ∃ D : ChartDatum ξ, D.c = c ∧ z₀ ∈ D.e.source := by
  have hB : IsOpen (U ∩ deriv H ⁻¹' {0}ᶜ) :=
    hH.deriv.continuousOn.isOpen_inter_preimage hU isOpen_compl_singleton
  let e0 := ((hH z₀ hz₀).hasStrictDerivAt.hasStrictFDerivAt_equiv hd).toOpenPartialHomeomorph H
  refine ⟨⟨c, e0.restrOpen _ hB, fun z hz => ?_, fun z hz => ?_⟩, rfl, ?_⟩
  · rw [OpenPartialHomeomorph.restrOpen_source] at hz
    exact heq z hz.2.1
  · rw [OpenPartialHomeomorph.restrOpen_source] at hz
    exact ⟨deriv H z, hz.2.2, (hH z hz.2.1).differentiableAt.hasDerivAt⟩
  · rw [OpenPartialHomeomorph.restrOpen_source]
    exact ⟨HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _, hz₀, hd⟩

end HCMW

/-! ## The points of a Weierstrass curve over `ℂ` as a topological space -/

namespace HCMW

open WeierstrassCurve.Affine (Point)
open scoped PeriodPair

section Topology

variable (W : WeierstrassCurve ℂ)

/-- The affine points `(x, y)` of `W` over `ℂ`, with the subspace topology of `ℂ × ℂ`. -/
abbrev AffPt := {p : ℂ × ℂ // W.toAffine.Nonsingular p.1 p.2}

/-- `E(ℂ) → OnePoint (affine points)`, `O ↦ ∞`. -/
def toOnePoint : W.toAffine.Point → OnePoint (AffPt W)
  | .zero => OnePoint.infty
  | .some x y h => ((⟨(x, y), h⟩ : AffPt W) : OnePoint (AffPt W))

/-- The inverse of `toOnePoint`. -/
def ofOnePoint (p : OnePoint (AffPt W)) : W.toAffine.Point :=
  OnePoint.elim p .zero (fun q => .some q.1.1 q.1.2 q.2)

/-- `E(ℂ) ≃ OnePoint (affine points)`. -/
def pointEquiv : W.toAffine.Point ≃ OnePoint (AffPt W) where
  toFun := toOnePoint W
  invFun := ofOnePoint W
  left_inv P := by cases P <;> rfl
  right_inv p := by induction p using OnePoint.rec <;> rfl

/-- **The topology of `E(ℂ)`**: the one-point compactification of the affine points (with the
subspace topology of `ℂ²`), the point at infinity being `O`. For a smooth plane cubic this is the
subspace topology of `ℙ²(ℂ)` (the affine part is open and dense, its complement is the one point `O`,
and `E(ℂ) ⊂ ℙ²(ℂ)` is compact Hausdorff). -/
instance pointTopology : TopologicalSpace W.toAffine.Point :=
  TopologicalSpace.induced (pointEquiv W) inferInstance

/-- `E(ℂ) ≃ₜ OnePoint (affine points)`. -/
def pointHomeo : W.toAffine.Point ≃ₜ OnePoint (AffPt W) :=
  (pointEquiv W).toHomeomorphOfIsInducing ⟨rfl⟩

@[simp] lemma pointHomeo_apply (P : W.toAffine.Point) : pointHomeo W P = toOnePoint W P := rfl

end Topology

/-! ## Coordinates on `E(ℂ)` -/

section Coords

variable {W : WeierstrassCurve ℂ}

/-- The affine coordinate `x` (junk value `0` at `O`). -/
def xC : W.toAffine.Point → ℂ
  | .zero => 0
  | .some x _ _ => x

/-- The affine coordinate `y` (junk value `0` at `O`). -/
def yC : W.toAffine.Point → ℂ
  | .zero => 0
  | .some _ y _ => y

/-- The local parameter `t = -x/y` at `O` (with `t(O) = 0`). -/
def tC : W.toAffine.Point → ℂ
  | .zero => 0
  | .some x y _ => -x / y

/-- The coordinate used at a point: `t = -x/y` at `O`, `y` at the points with `y = 0` (the nonzero
`2`-torsion for a short Weierstrass model), `x` elsewhere. -/
def coordFor : W.toAffine.Point → (W.toAffine.Point → ℂ)
  | .zero => tC
  | .some _ y _ => if y = 0 then yC else xC

end Coords

/-! ## The Weierstrass map `ξ_L = L.toPoint` -/

section Weierstrass

variable (L : PeriodPair)

local notation "ξL" => L.toPoint L.discriminant_ne_zero

theorem toPoint_add (z w : ℂ) : (ξL) (z + w) = (ξL) z + (ξL) w :=
  (L.isUniformization_toPoint L.discriminant_ne_zero).1 z w

theorem toPoint_eq_zero_iff (z : ℂ) : (ξL) z = 0 ↔ z ∈ L.lattice :=
  ⟨(L.isUniformization_toPoint L.discriminant_ne_zero).2.2 z, fun h => L.toPoint_of_mem _ h⟩

theorem toPoint_surjective : Function.Surjective (ξL) :=
  (L.isUniformization_toPoint L.discriminant_ne_zero).2.1

/-- `ξ_L` as an additive homomorphism. -/
def toPointHom : ℂ →+ L.weierstrassCurve.toAffine.Point := AddMonoidHom.mk' (ξL) (toPoint_add L)

theorem toPoint_eq_iff (z w : ℂ) : (ξL) z = (ξL) w ↔ z - w ∈ L.lattice := by
  rw [← toPoint_eq_zero_iff]
  change toPointHom L z = toPointHom L w ↔ toPointHom L (z - w) = 0
  rw [map_sub, sub_eq_zero]

theorem xC_toPoint {z : ℂ} (hz : z ∉ L.lattice) : xC ((ξL) z) = ℘[L] z := by
  rw [L.toPoint_of_notMem _ hz]; rfl

theorem yC_toPoint {z : ℂ} (hz : z ∉ L.lattice) : yC ((ξL) z) = ℘'[L] z / 2 := by
  rw [L.toPoint_of_notMem _ hz]; rfl

theorem tC_toPoint {z : ℂ} (hz : z ∉ L.lattice) : tC ((ξL) z) = -℘[L] z / (℘'[L] z / 2) := by
  rw [L.toPoint_of_notMem _ hz]; rfl

/-- `‖℘_L‖ → ∞` at the lattice points. -/
theorem eventually_large_weierstrassP {z : ℂ} (hz : z ∈ L.lattice) (R : ℝ) :
    ∀ᶠ w in 𝓝 z, w ∉ L.lattice → R < ‖℘[L] w‖ := by
  set f := ℘[L - z]
  have hf : ContinuousAt f z := (L.analyticAt_weierstrassPExcept z).continuousAt
  set B := ‖f z‖ + 1 + ‖1 / z ^ 2‖
  have h1 : ∀ᶠ w in 𝓝 z, ‖f w - f z‖ < 1 := by
    have := hf.tendsto
    rw [Metric.tendsto_nhds] at this
    filter_upwards [this 1 one_pos] with w hw; rwa [dist_eq_norm] at hw
  have h2 : ∀ᶠ w in 𝓝 z, ‖w - z‖ ^ 2 * (R + B + 1) < 1 := by
    have hc : ContinuousAt (fun w : ℂ => ‖w - z‖ ^ 2 * (R + B + 1)) z := by fun_prop
    have := hc.eventually (gt_mem_nhds (a := 1) (by simp))
    exact this
  filter_upwards [h1, h2] with w hw1 hw2 hwΛ
  have hwz : w ≠ z := fun h => hwΛ (h ▸ hz)
  have hpos : 0 < ‖w - z‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwz)
  have hP : ℘[L] w = f w + (1 / (w - z) ^ 2 - 1 / z ^ 2) :=
    (L.weierstrassPExcept_add ⟨z, hz⟩ w).symm
  have hbig : R + B + 1 < ‖1 / (w - z) ^ 2‖ := by
    rw [norm_div, norm_one, norm_pow, lt_div_iff₀ (by positivity)]; linarith
  have hfw : ‖f w‖ ≤ ‖f z‖ + 1 := by
    have := norm_sub_norm_le (f w) (f z); linarith
  have : ‖1 / (w - z) ^ 2‖ ≤ ‖℘[L] w‖ + ‖f w‖ + ‖1 / z ^ 2‖ := by
    have e : 1 / (w - z) ^ 2 = ℘[L] w - f w + 1 / z ^ 2 := by rw [hP]; ring
    rw [e]
    calc ‖℘[L] w - f w + 1 / z ^ 2‖ ≤ ‖℘[L] w - f w‖ + ‖1 / z ^ 2‖ := norm_add_le _ _
      _ ≤ ‖℘[L] w‖ + ‖f w‖ + ‖1 / z ^ 2‖ := by gcongr; exact norm_sub_le _ _
  linarith

theorem isClosed_nonsingular :
    IsClosed {p : ℂ × ℂ | L.weierstrassCurve.toAffine.Nonsingular p.1 p.2} := by
  have : {p : ℂ × ℂ | L.weierstrassCurve.toAffine.Nonsingular p.1 p.2} =
      {p : ℂ × ℂ | p.2 ^ 2 = p.1 ^ 3 + (-L.g₂ / 4) * p.1 + (-L.g₃ / 4)} := by
    ext p
    simp only [mem_setOf_eq]
    rw [← WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
      L.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero, WeierstrassCurve.Affine.equation_iff]
    simp
  rw [this]
  exact isClosed_eq (by fun_prop) (by fun_prop)

instance : LocallyCompactSpace (AffPt L.weierstrassCurve) :=
  (isClosed_nonsingular L).locallyCompactSpace

instance : T2Space L.weierstrassCurve.toAffine.Point :=
  (pointHomeo L.weierstrassCurve).symm.t2Space

theorem continuous_toPoint : Continuous (ξL) := by
  rw [(pointHomeo L.weierstrassCurve).isInducing.continuous_iff, continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ L.lattice
  · have h0 : (pointHomeo L.weierstrassCurve ∘ ξL) z = OnePoint.infty := by
      simp only [Function.comp_apply, pointHomeo_apply, L.toPoint_of_mem _ hz]; rfl
    show Tendsto _ _ _
    rw [h0, OnePoint.hasBasis_nhds_infty.tendsto_right_iff]
    rintro s ⟨-, hsk⟩
    obtain ⟨R, hR⟩ := hsk.exists_bound_of_continuousOn
      (f := fun q : AffPt L.weierstrassCurve => q.1.1) (by fun_prop)
    filter_upwards [eventually_large_weierstrassP L hz R] with w hw
    by_cases hwΛ : w ∈ L.lattice
    · right
      simp only [Function.comp_apply, pointHomeo_apply, L.toPoint_of_mem _ hwΛ]; rfl
    · left
      simp only [Function.comp_apply, pointHomeo_apply, L.toPoint_of_notMem _ hwΛ]
      refine ⟨_, fun hmem => ?_, rfl⟩
      have := hR _ hmem
      simp only at this
      linarith [hw hwΛ]
  · have hopen : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
    refine ContinuousOn.continuousAt ?_ (hopen.mem_nhds hz)
    rw [continuousOn_iff_continuous_domRestrict]
    have e : (L.lattice : Set ℂ)ᶜ.domRestrict (pointHomeo L.weierstrassCurve ∘ ξL) =
        fun s : ((L.lattice : Set ℂ)ᶜ : Set ℂ) => ((⟨(℘[L] s, ℘'[L] s / 2), (WeierstrassCurve.Affine.equation_iff_nonsingular_of_Δ_ne_zero
          L.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero).mp (L.equation_weierstrassP s.property)⟩ :
            AffPt L.weierstrassCurve) : OnePoint (AffPt L.weierstrassCurve)) := by
      funext s
      show toOnePoint _ (L.toPoint _ (s : ℂ)) = _
      rw [L.toPoint_of_notMem _ s.property]
      rfl
    rw [e]
    refine OnePoint.continuous_coe.comp (Continuous.subtype_mk (Continuous.prodMk ?_ ?_) _)
    · exact (L.analyticOnNhd_weierstrassP.continuousOn).restrict
    · exact ((L.analyticOnNhd_derivWeierstrassP.continuousOn).restrict).div_const _

/-- A compact set meeting every coset of the lattice. -/
theorem exists_compact_fund : ∃ K : Set ℂ, IsCompact K ∧ ∀ z, ∃ l ∈ L.lattice, z + l ∈ K := by
  refine ⟨(fun p : ℝ × ℝ => (p.1 : ℂ) * L.ω₁ + (p.2 : ℂ) * L.ω₂) '' (Icc 0 1 ×ˢ Icc 0 1),
    (isCompact_Icc.prod isCompact_Icc).image (by fun_prop), fun z => ?_⟩
  set a := L.basis.repr z 0
  set b := L.basis.repr z 1
  have hz : z = (a : ℂ) * L.ω₁ + (b : ℂ) * L.ω₂ := by
    have := L.basis.sum_repr z
    rw [Fin.sum_univ_two, L.basis_zero, L.basis_one, Complex.real_smul, Complex.real_smul] at this
    exact this.symm
  refine ⟨-((⌊a⌋ : ℂ) * L.ω₁ + (⌊b⌋ : ℂ) * L.ω₂),
    neg_mem (PeriodPair.mem_lattice.mpr ⟨⌊a⌋, ⌊b⌋, rfl⟩), ⟨(Int.fract a, Int.fract b), ?_, ?_⟩⟩
  · exact ⟨⟨Int.fract_nonneg a, (Int.fract_lt_one a).le⟩, ⟨Int.fract_nonneg b, (Int.fract_lt_one b).le⟩⟩
  · simp only [Int.fract, Complex.ofReal_sub, Complex.ofReal_intCast]
    rw [hz]; ring

theorem isOpenMap_toPoint : IsOpenMap (ξL) := by
  intro U hU
  obtain ⟨K, hK, hKf⟩ := exists_compact_fund L
  set V := {z : ℂ | ∃ l ∈ L.lattice, z - l ∈ U}
  have hV : IsOpen V := by
    have : V = ⋃ l : L.lattice, (· - (l : ℂ)) ⁻¹' U := by
      ext z; simp [V]
    rw [this]
    exact isOpen_iUnion fun l => hU.preimage (continuous_id.sub continuous_const)
  have hset : ((ξL) '' U)ᶜ = (ξL) '' (K ∩ Vᶜ) := by
    ext P
    simp only [mem_compl_iff, mem_image, not_exists, not_and, mem_inter_iff]
    constructor
    · intro hP
      obtain ⟨w, rfl⟩ := toPoint_surjective L P
      obtain ⟨l, hl, hwl⟩ := hKf w
      refine ⟨w + l, ⟨hwl, ?_⟩, ?_⟩
      · rintro ⟨l', hl', hU'⟩
        exact hP _ hU' ((toPoint_eq_iff L _ _).2 (by
          rw [show w + l - l' - w = l - l' by ring]; exact sub_mem hl hl'))
      · exact (toPoint_eq_iff L _ _).2 (by simpa using hl)
    · rintro ⟨k, ⟨-, hkV⟩, rfl⟩ u hu hEq
      exact hkV ⟨k - u, (toPoint_eq_iff L _ _).1 hEq.symm, by simpa using hu⟩
  rw [← isClosed_compl_iff, hset]
  exact ((hK.inter_right hV.isClosed_compl).image (continuous_toPoint L)).isClosed

/-! ### `℘''` -/

theorem countable_lattice : (L.lattice : Set ℂ).Countable := by
  have : Countable L.lattice := Countable.of_equiv _ L.latticeEquivProd.toEquiv.symm
  exact Set.countable_coe_iff.mp this

theorem isPreconnected_compl_lattice : IsPreconnected (L.lattice : Set ℂ)ᶜ :=
  ((countable_lattice L).isPathConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected

theorem deriv_derivWeierstrassP {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) :
    deriv ℘'[L] z₀ = 6 * ℘[L] z₀ ^ 2 - L.g₂ / 2 := by
  set S := (L.lattice : Set ℂ)ᶜ
  have hS : IsOpen S := L.isClosed_lattice.isOpen_compl
  have hP : AnalyticOnNhd ℂ ℘[L] S := L.analyticOnNhd_weierstrassP
  have hP' : AnalyticOnNhd ℂ ℘'[L] S := L.analyticOnNhd_derivWeierstrassP
  -- `℘' · (2℘'' - 12℘² + g₂) = 0` on `S`
  have hprod : ∀ z ∈ S, ℘'[L] z * (2 * deriv ℘'[L] z - 12 * ℘[L] z ^ 2 + L.g₂) = 0 := by
    intro z hz
    have hPd : HasDerivAt ℘[L] (℘'[L] z) z := by
      have := (hP z hz).differentiableAt.hasDerivAt; rwa [PeriodPair.deriv_weierstrassP] at this
    have hP'd : HasDerivAt ℘'[L] (deriv ℘'[L] z) z := (hP' z hz).differentiableAt.hasDerivAt
    have hF := (hP'd.pow 2).sub (((hPd.pow 3).const_mul 4).sub (hPd.const_mul L.g₂) |>.sub
      (hasDerivAt_const z L.g₃))
    have hF0 : HasDerivAt (fun w => ℘'[L] w ^ 2 - (4 * ℘[L] w ^ 3 - L.g₂ * ℘[L] w - L.g₃)) 0 z := by
      refine (hasDerivAt_const z (0 : ℂ)).congr_of_eventuallyEq ?_
      filter_upwards [hS.mem_nhds hz] with w hw
      rw [L.derivWeierstrassP_sq w hw]; ring
    have := hF.unique hF0
    simp only [Nat.cast_ofNat] at this
    linear_combination this
  set G := fun z => 2 * deriv ℘'[L] z - 12 * ℘[L] z ^ 2 + L.g₂
  have hG : AnalyticOnNhd ℂ G S := by
    intro z hz
    have h1 := hP'.deriv z hz
    have h2 := hP z hz
    simp only [G]
    fun_prop
  suffices G z₀ = 0 by simp only [G] at this; linear_combination this / 2
  rcases (hP' z₀ hz₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have := hP'.eqOn_zero_of_preconnected_of_eventuallyEq_zero (isPreconnected_compl_lattice L) hz₀ h
    exact ZInQ.Contrib.HCMDict.derivWeierstrassP_omega_div_four_ne L
      (this (ZInQ.Contrib.HCMDict.omega_div_four_notMem L))
  · have hev : ∀ᶠ z in 𝓝[≠] z₀, G z = 0 := by
      filter_upwards [h, mem_nhdsWithin_of_mem_nhds (hS.mem_nhds hz₀)] with z hz hzS
      exact (mul_eq_zero.mp (hprod z hzS)).resolve_left hz
    have h1 : Tendsto G (𝓝[≠] z₀) (𝓝 (G z₀)) :=
      (hG z₀ hz₀).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have h2 : Tendsto G (𝓝[≠] z₀) (𝓝 0) := tendsto_const_nhds.congr' (hev.mono fun _ h => h.symm)
    exact tendsto_nhds_unique h1 h2

/-! ### Chart data for `ξ_L` -/

theorem exists_chartDatum_zero :
    ∃ D : ChartDatum (ξL), D.c = tC ∧ (0 : ℂ) ∈ D.e.source := by
  set Ex := L.weierstrassPExcept 0
  set Dx := L.derivWeierstrassPExcept 0
  set S0 := ((L.lattice : Set ℂ) \ {0})ᶜ
  have hS0 : IsOpen S0 := L.isOpen_compl_lattice_sdiff
  have hEx : AnalyticOnNhd ℂ Ex S0 := L.analyticOnNhd_weierstrassPExcept 0
  have hDx : AnalyticOnNhd ℂ Dx S0 := L.analyticOnNhd_derivWeierstrassPExcept 0
  set U := S0 ∩ (fun z => 2 - z ^ 3 * Dx z) ⁻¹' {0}ᶜ
  have hU : IsOpen U := by
    refine ContinuousOn.isOpen_inter_preimage ?_ hS0 isOpen_compl_singleton
    exact (continuousOn_const.sub ((continuousOn_pow 3).mul hDx.continuousOn))
  have h0U : (0 : ℂ) ∈ U := ⟨by simp [S0], by simp⟩
  set H := fun z : ℂ => 2 * (z + z ^ 3 * Ex z) / (2 - z ^ 3 * Dx z)
  have hH : AnalyticOnNhd ℂ H U := by
    intro z hz
    have h1 := hEx z hz.1
    have h2 := hDx z hz.1
    exact (by fun_prop : AnalyticAt ℂ (fun z => 2 * (z + z ^ 3 * Ex z)) z).div
      (by fun_prop : AnalyticAt ℂ (fun z => 2 - z ^ 3 * Dx z) z) hz.2
  have hd : deriv H 0 = 1 := by
    have hE : HasDerivAt Ex (deriv Ex 0) 0 := (hEx 0 h0U.1).differentiableAt.hasDerivAt
    have hD : HasDerivAt Dx (deriv Dx 0) 0 := (hDx 0 h0U.1).differentiableAt.hasDerivAt
    have hN := (((hasDerivAt_id (0 : ℂ)).add ((hasDerivAt_pow 3 (0 : ℂ)).mul hE)).const_mul 2)
    have hM := (hasDerivAt_const (0 : ℂ) (2 : ℂ)).sub ((hasDerivAt_pow 3 (0 : ℂ)).mul hD)
    have := hN.div hM (by simp)
    refine this.deriv.trans ?_
    simp; norm_num
  refine exists_chartDatum tC hU h0U hH (by rw [hd]; exact one_ne_zero) fun z hz => ?_
  by_cases hz0 : z = 0
  · subst hz0; simp [H, L.toPoint_zero, tC]
  have hzΛ : z ∉ L.lattice := fun h => hz.1 ⟨h, hz0⟩
  rw [tC_toPoint L hzΛ]
  have hP : ℘[L] z = Ex z + 1 / z ^ 2 := by
    have := L.weierstrassPExcept_add ⟨0, zero_mem _⟩ z
    simp only [sub_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, div_zero] at this
    rw [← this]
  have hP' : ℘'[L] z = Dx z - 2 / z ^ 3 := by
    have := L.derivWeierstrassPExcept_sub ⟨0, zero_mem _⟩ z
    simp only [sub_zero] at this
    rw [← this]
  have hden : 2 - z ^ 3 * Dx z ≠ 0 := hz.2
  have hz3 : z ^ 3 ≠ 0 := pow_ne_zero 3 hz0
  have hP'ne : ℘'[L] z / 2 ≠ 0 := by
    rw [hP']
    intro h
    apply hden
    field_simp at h
    linear_combination -h
  rw [div_eq_div_iff hP'ne hden, hP, hP']
  field_simp
  ring

theorem exists_chartDatum_some {x y : ℂ} (h : L.weierstrassCurve.toAffine.Nonsingular x y) :
    ∃ D : ChartDatum (ξL), D.c = coordFor (Point.some x y h) ∧
      Point.some x y h ∈ (ξL) '' D.e.source := by
  obtain ⟨z₀, hz₀⟩ := toPoint_surjective L (Point.some x y h)
  have hz₀Λ : z₀ ∉ L.lattice := by
    intro hm; rw [L.toPoint_of_mem _ hm] at hz₀; exact Point.some_ne_zero h hz₀.symm
  have hxy : ℘[L] z₀ = x ∧ ℘'[L] z₀ / 2 = y := by
    rw [L.toPoint_of_notMem _ hz₀Λ, Point.some.injEq] at hz₀; exact hz₀
  have hS : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  by_cases hy : y = 0
  · have hc : coordFor (Point.some x y h) = yC := by simp [coordFor, hy]
    have hd : deriv (fun z => ℘'[L] z / 2) z₀ ≠ 0 := by
      rw [deriv_div_const, deriv_derivWeierstrassP L hz₀Λ, hxy.1]
      have hns := (WeierstrassCurve.Affine.nonsingular_iff' x y).mp h
      simp only [PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
        PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄, hy] at hns
      intro h0
      rcases hns.2 with h1 | h1
      · apply h1; linear_combination (-1 : ℂ) * h0
      · apply h1; ring
    obtain ⟨D, hDc, hD⟩ := exists_chartDatum yC hS hz₀Λ
      (L.analyticOnNhd_derivWeierstrassP.div_const) hd fun z hz => yC_toPoint L hz
    exact ⟨D, hDc.trans hc.symm, z₀, hD, hz₀⟩
  · have hc : coordFor (Point.some x y h) = xC := by simp [coordFor, hy]
    have hd : deriv ℘[L] z₀ ≠ 0 := by
      rw [PeriodPair.deriv_weierstrassP]
      intro h0; apply hy; rw [← hxy.2, h0, zero_div]
    obtain ⟨D, hDc, hD⟩ := exists_chartDatum xC hS hz₀Λ L.analyticOnNhd_weierstrassP hd
      fun z hz => xC_toPoint L hz
    exact ⟨D, hDc.trans hc.symm, z₀, hD, hz₀⟩

theorem exists_chartDatum_toPoint (P : L.weierstrassCurve.toAffine.Point) :
    ∃ D : ChartDatum (ξL), D.c = coordFor P ∧ P ∈ (ξL) '' D.e.source := by
  cases P with
  | zero =>
    obtain ⟨D, hDc, hD⟩ := exists_chartDatum_zero L
    exact ⟨D, hDc, 0, hD, L.toPoint_zero _⟩
  | some x y h => exact exists_chartDatum_some L h

end Weierstrass

end HCMW
