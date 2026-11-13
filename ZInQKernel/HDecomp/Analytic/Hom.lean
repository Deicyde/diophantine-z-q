import ZInQKernel.HDecomp.Analytic.Torus

/-! Glue of `docs/research/h-decomposition.md`, adopted by task hdec-adopt4 from
`scratch/bp-analytic/Torus.lean`, §8-§9.
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

/-! ## §8. Continuous homomorphisms of tori are linear (node T2)

A continuous group homomorphism `f : E ⧸ Λ → E' ⧸ Λ'` lifts (covering theory: `E` is simply
connected) to a continuous additive, hence `ℝ`-linear, map `T : E → E'` with `T(Λ) ⊆ Λ'`. If `f`
is holomorphic, `T` is `ℂ`-linear. This is the glue that turns endomorphisms of an abelian variety
into linear maps preserving its period lattice (R1an, T11, T12). -/

section Hom

variable {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℂ E']
variable (Λ' : Submodule ℤ E') [DiscreteTopology Λ']

/-- A continuous map with values in a discrete subgroup is locally constant. -/
theorem eventuallyEq_const_of_mem {X : Type*} [TopologicalSpace X] {G : X → E'} {x : X}
    (hG : ContinuousAt G x) (hmem : ∀ᶠ z in 𝓝 x, G z ∈ Λ') (hx : G x ∈ Λ') :
    G =ᶠ[𝓝 x] fun _ => G x := by
  obtain ⟨ε, hε, hgap⟩ := exists_gap Λ'
  filter_upwards [hG.eventually (Metric.ball_mem_nhds _ hε), hmem] with z hz hzm
  have h0 := hgap _ (Λ'.sub_mem hzm hx) (by simpa [dist_eq_norm] using hz)
  exact sub_eq_zero.mp h0

/-- **Continuous homomorphisms of tori are induced by `ℝ`-linear maps.** -/
theorem exists_realLinear_lift (f : Torus Λ →+ Torus Λ') (hf : Continuous f) :
    ∃ T : E →L[ℝ] E', (∀ v ∈ Λ, T v ∈ Λ') ∧ ∀ v, f (proj Λ v) = proj Λ' (T v) := by
  obtain ⟨F, ⟨hF0, hFp⟩, -⟩ := (isCoveringMap_proj Λ').existsUnique_continuousMap_lifts
    ⟨f ∘ proj Λ, hf.comp (isLocalHomeomorph_proj Λ).continuous⟩ (0 : E) (0 : E') (by simp)
  have hFp' : ∀ v, proj Λ' (F v) = f (proj Λ v) := fun v => congrFun hFp v
  have hmem : ∀ p : E × E, F (p.1 + p.2) - (F p.1 + F p.2) ∈ Λ' := by
    intro p
    rw [← proj_eq_iff]
    simp only [proj, QuotientAddGroup.mk_add]
    rw [show (QuotientAddGroup.mk (F (p.1 + p.2)) : Torus Λ') = f (proj Λ (p.1 + p.2)) from
        hFp' _, show (QuotientAddGroup.mk (F p.1) : Torus Λ') = f (proj Λ p.1) from hFp' _,
      show (QuotientAddGroup.mk (F p.2) : Torus Λ') = f (proj Λ p.2) from hFp' _, ← map_add]
    rfl
  have hc : Continuous fun p : E × E => F (p.1 + p.2) - (F p.1 + F p.2) := by
    have := F.continuous; fun_prop
  have hadd : ∀ x y, F (x + y) = F x + F y := by
    intro x y
    have hconst := PreconnectedSpace.constant (inferInstance : PreconnectedSpace (E × E))
      (f := fun p => (⟨_, hmem p⟩ : Λ')) (hc.subtype_mk _) (x := (x, y)) (y := (0, 0))
    have := congrArg Subtype.val hconst
    simp only [add_zero, hF0, sub_zero] at this
    exact sub_eq_zero.mp this
  let Fa : E →+ E' := { toFun := F, map_zero' := hF0, map_add' := hadd }
  refine ⟨Fa.toRealLinearMap F.continuous, ?_, ?_⟩
  · intro v hv
    have h := hFp' v
    rw [show proj Λ v = 0 from (QuotientAddGroup.eq_zero_iff v).mpr hv, map_zero] at h
    exact (QuotientAddGroup.eq_zero_iff _).mp h
  · intro v
    exact (hFp' v).symm

/-- **Holomorphic homomorphisms of tori are induced by `ℂ`-linear maps** (node T2). -/
theorem exists_complexLinear_lift (f : Torus Λ →+ Torus Λ')
    (hf : MDifferentiable 𝓘(ℂ, E) 𝓘(ℂ, E') f) :
    ∃ T : E →L[ℂ] E', (∀ v ∈ Λ, T v ∈ Λ') ∧ ∀ v, f (proj Λ v) = proj Λ' (T v) := by
  obtain ⟨T, hTΛ, hTf⟩ := exists_realLinear_lift Λ Λ' f hf.continuous
  set q : Torus Λ := proj Λ 0
  set x' : E := chartOf Λ q.out q
  set c' := chartOf Λ' (f q).out
  have hq : q ∈ (chartOf Λ q.out).source := mem_chart_source E q
  have hx' : proj Λ x' = q := proj_chartOf Λ hq
  have hfq : f q ∈ c'.source := mem_chart_source E' (f q)
  -- the coordinate expression of `f` at `q` is `ℂ`-differentiable
  have hfun : writtenInExtChartAt 𝓘(ℂ, E) 𝓘(ℂ, E') q f = c' ∘ f ∘ proj Λ := by
    funext z
    simp [writtenInExtChartAt, chartAt_torus, chartOf_symm_apply, c']
  have hpt : extChartAt 𝓘(ℂ, E) q q = x' := by
    simp [chartAt_torus, x']
  have hdiff : DifferentiableAt ℂ (c' ∘ f ∘ proj Λ) x' := by
    have h1 := (hf q).differentiableWithinAt_writtenInExtChartAt
    rw [hfun, hpt, modelWithCornersSelf_coe, range_id, differentiableWithinAt_univ] at h1
    exact h1
  -- `T` agrees near `x'` with the coordinate expression up to a lattice constant
  have hU : ∀ᶠ v in 𝓝 x', f (proj Λ v) ∈ c'.source := by
    have hcont : Continuous (f ∘ proj Λ) := hf.continuous.comp (isLocalHomeomorph_proj Λ).continuous
    have : f (proj Λ x') ∈ c'.source := by rw [hx']; exact hfq
    exact hcont.continuousAt.preimage_mem_nhds (c'.open_source.mem_nhds this)
  have hmemG : ∀ v, f (proj Λ v) ∈ c'.source → T v - c' (f (proj Λ v)) ∈ Λ' := by
    intro v hv
    rw [← proj_eq_iff, ← hTf v, proj_chartOf Λ' hv]
  have hG := eventuallyEq_const_of_mem Λ' (G := fun v => T v - c' (f (proj Λ v))) (x := x')
    (T.continuous.continuousAt.sub hdiff.continuousAt) (hU.mono hmemG)
    (hmemG x' (by rw [hx']; exact hfq))
  have hTeq : (T : E → E') =ᶠ[𝓝 x'] fun v => c' (f (proj Λ v)) + (T x' - c' (f (proj Λ x'))) := by
    filter_upwards [hG] with v hv
    rw [← hv]; abel
  have hTdiff : DifferentiableAt ℂ (T : E → E') x' :=
    (hdiff.add_const _).congr_of_eventuallyEq hTeq
  -- compare the `ℂ`-derivative with the `ℝ`-derivative `T`
  set D := fderiv ℂ (T : E → E') x'
  have hD : (D.restrictScalars ℝ : E →L[ℝ] E') = T :=
    (hTdiff.hasFDerivAt.restrictScalars ℝ).unique T.hasFDerivAt
  refine ⟨D, fun v hv => ?_, fun v => ?_⟩
  · have : D v = T v := congrArg (fun L : E →L[ℝ] E' => L v) hD
    rw [this]; exact hTΛ v hv
  · have : D v = T v := congrArg (fun L : E →L[ℝ] E' => L v) hD
    rw [this]; exact hTf v

end Hom

/-! ## §9. The covolume of `Ωℤ^g + ℤ^g` is `|det Im Ω|` (node P3)

With bp-faltings' `torusMetricSq Λ c = ‖c‖²·covol(Λ)`, this gives the archimedean Faltings term
of a torus with normalized period matrix `Ω` as `‖c‖²·det Im Ω`: the integral over `A(ℂ)` through
the period matrix alone. -/

section Covolume

open MeasureTheory Matrix

variable {g : ℕ}

/-- `(Σ j, Fin 2) ≃ Fin g ⊕ Fin g`: `(j, 0) ↦ inr j` (real part), `(j, 1) ↦ inl j` (imaginary
part). -/
def sigmaEquiv (g : ℕ) : (Σ _ : Fin g, Fin 2) ≃ Fin g ⊕ Fin g where
  toFun p := if p.2 = 0 then Sum.inr p.1 else Sum.inl p.1
  invFun := Sum.elim (fun j => ⟨j, 1⟩) (fun j => ⟨j, 0⟩)
  left_inv := by
    rintro ⟨j, k⟩
    fin_cases k <;> rfl
  right_inv := by
    rintro (j | j) <;> rfl

/-- The standard real basis of `ℂ^g`: `inl j ↦ i·e_j`, `inr j ↦ e_j`. -/
def stdRealBasis (g : ℕ) : Module.Basis (Fin g ⊕ Fin g) ℝ (Fin g → ℂ) :=
  (Pi.basis fun _ : Fin g => Complex.basisOneI).reindex (sigmaEquiv g)

theorem stdRealBasis_repr_inl (z : Fin g → ℂ) (j : Fin g) :
    (stdRealBasis g).repr z (Sum.inl j) = (z j).im := by
  simp [stdRealBasis, sigmaEquiv, Complex.coe_basisOneI_repr]

theorem stdRealBasis_repr_inr (z : Fin g → ℂ) (j : Fin g) :
    (stdRealBasis g).repr z (Sum.inr j) = (z j).re := by
  simp [stdRealBasis, sigmaEquiv, Complex.coe_basisOneI_repr]

/-- The unit square in `ℂ` has volume one. -/
theorem volume_unitSquare :
    volume {w : ℂ | w.re ∈ Set.Ico (0 : ℝ) 1 ∧ w.im ∈ Set.Ico (0 : ℝ) 1} = 1 := by
  have : {w : ℂ | w.re ∈ Set.Ico (0 : ℝ) 1 ∧ w.im ∈ Set.Ico (0 : ℝ) 1} =
      Complex.measurableEquivRealProd ⁻¹' (Set.Ico (0 : ℝ) 1 ×ˢ Set.Ico (0 : ℝ) 1) := by
    ext w; simp [Complex.measurableEquivRealProd_apply]
  rw [this, Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Ico.prod measurableSet_Ico).nullMeasurableSet,
    Measure.volume_eq_prod, Measure.prod_prod, Real.volume_Ico]
  simp

theorem volume_fundamentalDomain_stdRealBasis :
    volume (ZSpan.fundamentalDomain (stdRealBasis g)) = 1 := by
  have : ZSpan.fundamentalDomain (stdRealBasis g) =
      Set.univ.pi fun _ : Fin g => {w : ℂ | w.re ∈ Set.Ico (0 : ℝ) 1 ∧ w.im ∈ Set.Ico (0 : ℝ) 1} :=
          by
    ext z
    simp only [ZSpan.mem_fundamentalDomain, Set.mem_pi, Set.mem_univ, true_imp_iff,
      Set.mem_ofPred_eq]
    constructor
    · intro h j
      exact ⟨by simpa [stdRealBasis_repr_inr] using h (Sum.inr j),
        by simpa [stdRealBasis_repr_inl] using h (Sum.inl j)⟩
    · rintro h (j | j)
      · simpa [stdRealBasis_repr_inl] using (h j).2
      · simpa [stdRealBasis_repr_inr] using (h j).1
  rw [this, volume_pi_pi]
  simp only [volume_unitSquare, Finset.prod_const_one]

/-- The coordinate matrix of the period basis in the standard real basis is
`[[Im Ω, 0], [Re Ω, 1]]`. -/
theorem toMatrix_periodVec (Ω : Matrix (Fin g) (Fin g) ℂ) :
    (stdRealBasis g).toMatrix (periodVec Ω) =
      Matrix.fromBlocks (Ω.map Complex.im) 0 (Ω.map Complex.re) 1 := by
  ext (r | r) (l | l) <;>
    simp [Module.Basis.toMatrix_apply, stdRealBasis_repr_inl, stdRealBasis_repr_inr, periodVec,
      Pi.single_apply, Matrix.one_apply] <;> split_ifs <;> simp

/-- **`covol(Ωℤ^g + ℤ^g) = |det Im Ω|`** for Lebesgue measure on `ℂ^g`. -/
theorem covolume_periodLattice (Ω : Matrix (Fin g) (Fin g) ℂ)
    (hΩ : (Ω.map Complex.im).det ≠ 0) :
    ZLattice.covolume (periodLattice Ω hΩ) = |(Ω.map Complex.im).det| := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain (periodLattice Ω hΩ) volume
      (ZSpan.isAddFundamentalDomain (periodBasis Ω hΩ) volume),
    ZSpan.measureReal_fundamentalDomain (periodBasis Ω hΩ) volume (stdRealBasis g),
    measureReal_def, volume_fundamentalDomain_stdRealBasis, ENNReal.toReal_one, mul_one,
    Module.Basis.det_apply, coe_periodBasis, toMatrix_periodVec, det_fromBlocks_zero₁₂, det_one,
    mul_one]

/-- For `Ω` in the Siegel space the covolume is `det Im Ω`. -/
theorem covolume_periodLattice_of_mem {Ω : Matrix (Fin g) (Fin g) ℂ} (h : Ω ∈ SiegelSpace g) :
    ZLattice.covolume (periodLattice Ω (det_im_ne_zero_of_mem_siegelSpace h)) =
      (Ω.map Complex.im).det := by
  rw [covolume_periodLattice, abs_of_pos h.2.det_pos]

end Covolume

end BPAnalytic
