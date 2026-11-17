import ZInQKernel.Contrib.OneProof.HeightDictionary
import ZInQKernel.Contrib.OneProof.RaynaudSemistableOr

open CategoryTheory AlgebraicGeometry MeasureTheory Topology Set MonObj
open MonoidalCategory CartesianMonoidalCategory
open ZInQ.DefFaltings ZInQ.HeightSplit ZInQ.HeightGlue ZInQ.HeightDict
open scoped NumberField

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option warn.classDefReducibility false

namespace ZInQ.HeightFix

/-! ## §1. Two finite measures with the same local density are equal -/

section Density

variable {X : Type*} [TopologicalSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X]

/-- **Uniqueness of a measure with given local densities.** On a compact space, let `v p E ≥ 0`
be a "chart volume" of `E` near `p` and `c > 0`. Two finite measures `nu₁, nu₂` that both satisfy
`|nuᵢ(E) − c v_p(E)| ≤ ε v_p(E)` for all measurable `E` in a neighbourhood of each `p` (depending on
`ε`) are equal. -/
theorem eq_of_density (nu₁ nu₂ : Measure X) [IsFiniteMeasure nu₁] [IsFiniteMeasure nu₂]
    (v : X → Set X → ℝ) (hv : ∀ p E, 0 ≤ v p E) (c : ℝ) (hc : 0 < c)
    (h₁ : ∀ p, ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
      |nu₁.real E - c * v p E| ≤ ε * v p E)
    (h₂ : ∀ p, ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
      |nu₂.real E - c * v p E| ≤ ε * v p E) : nu₁ = nu₂ := by
  -- the bound `|nu₁ E − nu₂ E| ≤ 2ε/(c−ε) nu₁ E`
  have key : ∀ ε : ℝ, 0 < ε → ε < c → ∀ E, MeasurableSet E →
      |nu₁.real E - nu₂.real E| ≤ 2 * ε / (c - ε) * nu₁.real E := by
    intro ε hε hεc
    have hW : ∀ p, ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
        |nu₁.real E - c * v p E| ≤ ε * v p E ∧ |nu₂.real E - c * v p E| ≤ ε * v p E := fun p => by
      obtain ⟨W1, h1, hW1⟩ := h₁ p ε hε
      obtain ⟨W2, h2, hW2⟩ := h₂ p ε hε
      exact ⟨W1 ∩ W2, Filter.inter_mem h1 h2, fun E hE hm =>
        ⟨hW1 E (hE.trans inter_subset_left) hm, hW2 E (hE.trans inter_subset_right) hm⟩⟩
    choose W hWn hWb using hW
    have hce : 0 < c - ε := by linarith
    have loc : ∀ p F, F ⊆ W p → MeasurableSet F →
        |nu₁.real F - nu₂.real F| ≤ 2 * ε / (c - ε) * nu₁.real F := by
      intro p F hF hFm
      obtain ⟨b1, b2⟩ := hWb p F hF hFm
      have hv0 := hv p F
      have h1' : (c - ε) * v p F ≤ nu₁.real F := by
        have := (abs_le.mp b1).1; nlinarith
      have hvle : v p F ≤ nu₁.real F / (c - ε) := by
        rw [le_div_iff₀ hce]; linarith
      have htri : |nu₁.real F - nu₂.real F| ≤ 2 * ε * v p F := by
        have e1 := abs_le.mp b1
        have e2 := abs_le.mp b2
        rw [abs_le]; constructor <;> linarith
      calc |nu₁.real F - nu₂.real F| ≤ 2 * ε * v p F := htri
        _ ≤ 2 * ε * (nu₁.real F / (c - ε)) := by gcongr
        _ = 2 * ε / (c - ε) * nu₁.real F := by ring
    obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun p => interior (W p))
      (fun p => isOpen_interior)
      (fun p _ => mem_iUnion.mpr ⟨p, mem_interior_iff_mem_nhds.mpr (hWn p)⟩)
    have ind : ∀ s : Finset X, ∀ F, MeasurableSet F → F ⊆ ⋃ p ∈ s, interior (W p) →
        |nu₁.real F - nu₂.real F| ≤ 2 * ε / (c - ε) * nu₁.real F := by
      classical
      intro s
      induction s using Finset.induction_on with
      | empty =>
        intro F _ hF
        have : F = ∅ := by simpa using hF
        subst this
        simp
      | insert p s hp ih =>
        intro F hFm hF
        have hFo : MeasurableSet (interior (W p)) := isOpen_interior.measurableSet
        have b1 := loc p (F ∩ interior (W p)) (inter_subset_right.trans interior_subset)
          (hFm.inter hFo)
        have b2 := ih (F \ interior (W p)) (hFm.diff hFo) (by
          intro x hx
          have h := hF hx.1
          simp only [Finset.set_biUnion_insert, mem_union] at h
          rcases h with h | h
          · exact absurd h hx.2
          · exact h)
        have hsplit : F = (F ∩ interior (W p)) ∪ (F \ interior (W p)) :=
          (inter_union_sdiff F _).symm
        have hd : Disjoint (F ∩ interior (W p)) (F \ interior (W p)) :=
          disjoint_sdiff_inter.symm
        have e1 : nu₁.real F = nu₁.real (F ∩ interior (W p)) + nu₁.real (F \ interior (W p)) := by
          conv_lhs => rw [hsplit]
          exact measureReal_union hd (hFm.diff hFo) (measure_ne_top _ _) (measure_ne_top _ _)
        have e2 : nu₂.real F = nu₂.real (F ∩ interior (W p)) + nu₂.real (F \ interior (W p)) := by
          conv_lhs => rw [hsplit]
          exact measureReal_union hd (hFm.diff hFo) (measure_ne_top _ _) (measure_ne_top _ _)
        rw [e1, e2]
        calc |nu₁.real (F ∩ interior (W p)) + nu₁.real (F \ interior (W p)) -
              (nu₂.real (F ∩ interior (W p)) + nu₂.real (F \ interior (W p)))|
            ≤ |nu₁.real (F ∩ interior (W p)) - nu₂.real (F ∩ interior (W p))| +
              |nu₁.real (F \ interior (W p)) - nu₂.real (F \ interior (W p))| := by
              rw [show nu₁.real (F ∩ interior (W p)) + nu₁.real (F \ interior (W p)) -
                (nu₂.real (F ∩ interior (W p)) + nu₂.real (F \ interior (W p))) =
                (nu₁.real (F ∩ interior (W p)) - nu₂.real (F ∩ interior (W p))) +
                (nu₁.real (F \ interior (W p)) - nu₂.real (F \ interior (W p))) by ring]
              exact abs_add_le _ _
          _ ≤ 2 * ε / (c - ε) * nu₁.real (F ∩ interior (W p)) +
              2 * ε / (c - ε) * nu₁.real (F \ interior (W p)) := add_le_add b1 b2
          _ = _ := by ring
    intro E hE
    exact ind t E hE (fun x _ => ht (mem_univ x))
  ext E hE
  have hreal : nu₁.real E = nu₂.real E := by
    refine TorusVolume.eq_of_abs_le (nu₁.real E) fun δ hδ hδ1 => ?_
    have hε : 0 < δ * c / 4 := by positivity
    have hεc : δ * c / 4 < c := by nlinarith
    have hk := key _ hε hεc E hE
    have hM : 0 ≤ nu₁.real E := measureReal_nonneg
    have hcoef : 2 * (δ * c / 4) / (c - δ * c / 4) ≤ δ := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    calc |nu₁.real E - nu₂.real E| ≤ 2 * (δ * c / 4) / (c - δ * c / 4) * nu₁.real E := hk
      _ ≤ δ * nu₁.real E := by gcongr
  exact (measureReal_eq_measureReal_iff (measure_ne_top _ _) (measure_ne_top _ _)).mp hreal

end Density

/-! ## §2. Densities in translated charts on a group -/

section Generic

variable {G : Type*} [Group G] [TopologicalSpace G] [MeasurableSpace G] {g : ℕ}

/-- `nu` has density `c` at `p` relative to Lebesgue measure, in the chart `q ↦ F(p⁻¹ q)` (the chart
`F` at `1` translated to `p`). -/
def DensAt (nu : Measure G) (F : G → (Fin g → ℂ)) (c : ℝ) (p : G) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
    |nu.real E - c * (volume ((fun q => F (p⁻¹ * q)) '' E)).toReal| ≤
      ε * (volume ((fun q => F (p⁻¹ * q)) '' E)).toReal

theorem densAt_one_iff (nu : Measure G) (F : G → (Fin g → ℂ)) (c : ℝ) :
    DensAt nu F c 1 ↔ ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 (1 : G), ∀ E ⊆ W, MeasurableSet E →
      |(nu E).toReal - c * (volume (F '' E)).toReal| ≤ ε * (volume (F '' E)).toReal := by
  have h : (fun q => F ((1 : G)⁻¹ * q)) = F := by funext q; simp
  simp only [DensAt, h]
  rfl

variable [IsTopologicalGroup G] [BorelSpace G]

/-- Translating a measure translates its densities. -/
theorem densAt_map (nu : Measure G) (F : G → (Fin g → ℂ)) (c : ℝ) (a p : G)
    (h : DensAt nu F c (a⁻¹ * p)) : DensAt (nu.map (a * ·)) F c p := by
  intro ε hε
  obtain ⟨W, hW, hb⟩ := h ε hε
  refine ⟨(fun q => a⁻¹ * q) ⁻¹' W, ?_, fun E hE hEm => ?_⟩
  · exact (continuous_const_mul a⁻¹).continuousAt.preimage_mem_nhds hW
  · have hmeas : Measurable (fun q : G => a * q) := measurable_const_mul a
    have hE' : (fun q => a * q) ⁻¹' E ⊆ W := fun x hx => by
      have := hE hx
      simpa using this
    have himg : (fun q => F ((a⁻¹ * p)⁻¹ * q)) '' ((fun q => a * q) ⁻¹' E) =
        (fun q => F (p⁻¹ * q)) '' E := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨a * x, hx, by simp [_root_.mul_assoc]⟩
      · rintro ⟨x, hx, rfl⟩
        exact ⟨a⁻¹ * x, by simpa using hx, by simp [_root_.mul_assoc]⟩
    have := hb _ hE' (hmeas hEm)
    rw [himg] at this
    rwa [Measure.real, Measure.map_apply hmeas hEm]

/-- A left-invariant measure with density `c` at `1` has density `c` at every point. -/
theorem densAt_of_invariant (nu : Measure G) [nu.IsMulLeftInvariant] (F : G → (Fin g → ℂ)) (c : ℝ)
    (h1 : DensAt nu F c 1) (p : G) : DensAt nu F c p := by
  have := densAt_map nu F c p p (by rwa [inv_mul_cancel])
  rwa [map_mul_left_eq_self] at this

/-- **Uniqueness**: two finite measures with density `c > 0` at every point coincide. -/
theorem eq_of_densAt [CompactSpace G] (nu₁ nu₂ : Measure G) [IsFiniteMeasure nu₁] [IsFiniteMeasure nu₂]
    (F : G → (Fin g → ℂ)) (c : ℝ) (hc : 0 < c) (h₁ : ∀ p, DensAt nu₁ F c p)
    (h₂ : ∀ p, DensAt nu₂ F c p) : nu₁ = nu₂ :=
  eq_of_density nu₁ nu₂ (fun p E => (volume ((fun q => F (p⁻¹ * q)) '' E)).toReal)
    (fun _ _ => ENNReal.toReal_nonneg) c hc h₁ h₂

/-- **Invariance**: a finite measure with density `c > 0` at every point (in the translated charts)
is left-invariant. -/
theorem isMulLeftInvariant_of_densAt [CompactSpace G] (nu : Measure G) [IsFiniteMeasure nu]
    (F : G → (Fin g → ℂ)) (c : ℝ) (hc : 0 < c) (h : ∀ p, DensAt nu F c p) :
    nu.IsMulLeftInvariant :=
  ⟨fun a => eq_of_densAt (nu.map (a * ·)) nu F c hc (fun p => densAt_map nu F c a p (h _)) h⟩

end Generic

/-! ## §3. The printed metric: the measure of `(i/2)^g η ∧ η̄` defined chart by chart -/

section Defs

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The chart at `p` obtained by translating algebraic coordinates `F = (f₁, …, f_g)` at the origin:
`q ↦ F(p⁻¹ q)`. -/
noncomputable def chartAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (U : Fin g → 𝒢.G.left.Opens) (s : ∀ i, Γ(𝒢.G.left, U i)) (p : 𝒢.Pts τ) :
    𝒢.Pts τ → (Fin g → ℂ) :=
  fun q => coordMap 𝒢 τ U s (p⁻¹ * q)

/-- **`nu` is the measure `(i/2)^g η ∧ η̄` near `p`**, for the invariant `g`-form `η` with value
`η(1) = η`. Let `fᵢ ∈ Γ(Uᵢ, 𝒪_𝒢)` be regular functions defined and vanishing at the origin `ξ` of
the generic fibre with `η = l · df₁ ∧ ⋯ ∧ df_g` at the origin. In the chart `q ↦ F(p⁻¹ q)` at `p`
(`chartAt`), the invariant form has coefficient `l` at `p` (it is the translate of its value at
`1`), so `(i/2)^g η ∧ η̄` has density `|τ(l)|²` relative to Lebesgue measure
`dx₁dy₁⋯dx_gdy_g` at the centre of the chart: near `p`,
`|nu(E) − |τ l|² λ(chart(E))| ≤ ε λ(chart(E))`. -/
def HasFormDensityAt (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) (p : 𝒢.Pts τ) : Prop :=
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i) (s : ∀ i, Γ(𝒢.G.left, U i))
    (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal 𝒢.genStalk)
    (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
    ∀ ε : ℝ, 0 < ε → ∃ W ∈ 𝓝 p, ∀ E ⊆ W, MeasurableSet E →
      |(nu E).toReal - ‖τ l‖ ^ 2 * (volume (chartAt 𝒢 τ U s p '' E)).toReal| ≤
        ε * (volume (chartAt 𝒢 τ U s p '' E)).toReal

/-- **`nu` is the measure `(i/2)^g η ∧ η̄` on `A_τ(ℂ)`**: a finite Borel measure (analytic
topology) with the density of `(i/2)^g η ∧ η̄` at every point, in the charts of `HasFormDensityAt`.
No invariance of `nu` is assumed (it is proved: `isFormMeasure_iff`). -/
def IsFormMeasure (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) : Prop :=
  @IsFiniteMeasure _ (anBorel 𝒢 τ) nu ∧ ∀ p, HasFormDensityAt 𝒢 τ nu eta p

/-- **The printed archimedean Faltings metric** `‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄ = r`: the measure
`(i/2)^g η ∧ η̄` exists, and every such measure has total mass `r`. -/
def IsPrintedMetricSq (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ} (eta : 𝒢.hodgeSpace g) (r : ℝ) :
    Prop :=
  letI := anBorel 𝒢 τ
  (∃ nu : Measure (𝒢.Pts τ), IsFormMeasure 𝒢 τ nu eta) ∧
    ∀ nu : Measure (𝒢.Pts τ), IsFormMeasure 𝒢 τ nu eta → (nu univ).toReal = r

theorem hasFormDensityAt_iff (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) (p : 𝒢.Pts τ) :
    HasFormDensityAt 𝒢 τ nu eta p ↔
      ∀ (U : Fin g → 𝒢.G.left.Opens) (hU : ∀ i, 𝒢.genericUnit ∈ U i)
        (s : ∀ i, Γ(𝒢.G.left, U i))
        (hm : ∀ i, 𝒢.G.left.presheaf.germ (U i) 𝒢.genericUnit (hU i) (s i) ∈
          IsLocalRing.maximalIdeal 𝒢.genStalk)
        (l : L), eta = l • 𝒢.wedge (fun i => ⟨_, hm i⟩) →
        @DensAt _ _ (anTop 𝒢 τ) (anBorel 𝒢 τ) g nu (coordMap 𝒢 τ U s) (‖τ l‖ ^ 2) p :=
  Iff.rfl

theorem isNormalizedBy_iff (𝒢 : GroupModel A L) (τ : L →+* ℂ) {g : ℕ}
    (nu : @Measure (𝒢.Pts τ) (anBorel 𝒢 τ)) (eta : 𝒢.hodgeSpace g) :
    IsNormalizedBy 𝒢 τ nu eta ↔ HasFormDensityAt 𝒢 τ nu eta 1 := by
  rw [hasFormDensityAt_iff]
  letI := anTop 𝒢 τ
  letI := anBorel 𝒢 τ
  simp only [densAt_one_iff]
  rfl

end Defs

section Metrized

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- The archimedean setup of a metrized model: `A_τ(ℂ)` is a compact topological group, and a
nonzero `η` has a representation `η = l · df₁ ∧ ⋯ ∧ df_g` with `τ(l) ≠ 0`. -/
theorem metrized_setup {g : ℕ} (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (eta : M.model.hodgeSpace g) (heta : eta ≠ 0) :
    @IsTopologicalGroup (M.model.Pts τ) (anTop M.model τ) _ ∧
    @CompactSpace (M.model.Pts τ) (anTop M.model τ) ∧
    ∃ (U : Fin g → M.model.G.left.Opens) (hU : ∀ i, M.model.genericUnit ∈ U i)
      (s : ∀ i, Γ(M.model.G.left, U i))
      (hm : ∀ i, M.model.G.left.presheaf.germ (U i) M.model.genericUnit (hU i) (s i) ∈
        IsLocalRing.maximalIdeal M.model.genStalk) (l : L),
      eta = l • M.model.wedge (fun i => ⟨_, hm i⟩) ∧ τ l ≠ 0 := by
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  letI := anTop M.model τ
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  refine ⟨hUnif.isTopologicalGroup, hUnif.compactSpace, ?_⟩
  have hw : ∃ f : Fin g → IsLocalRing.maximalIdeal M.model.genStalk, M.model.wedge f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply M.hodge.coeff_ne_zero τ
    refine GroupModel.semilinear_ext_wedge M.model _ _ fun f => ?_
    rw [hcon f, map_zero, LinearMap.zero_apply]
  obtain ⟨f, hf⟩ := hw
  obtain ⟨l, hl⟩ := (finrank_eq_one_iff_of_nonzero' _ hf).mp M.hodge.finrank_eq_one eta
  let U : Fin g → M.model.G.left.Opens := fun i => (M.model.exists_rep (f i)).choose
  have hU : ∀ i, M.model.genericUnit ∈ U i := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose
  let s : ∀ i, Γ(M.model.G.left, U i) := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose_spec.choose
  have hgerm : ∀ i, M.model.G.left.presheaf.germ (U i) M.model.genericUnit (hU i) (s i) =
      (f i : M.model.genStalk) := fun i =>
    (M.model.exists_rep (f i)).choose_spec.choose_spec.choose_spec
  have hm : ∀ i, M.model.G.left.presheaf.germ (U i) M.model.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal M.model.genStalk := fun i => by rw [hgerm]; exact (f i).2
  have hwf : M.model.wedge (fun i => ⟨_, hm i⟩) = M.model.wedge f := by
    congr 1; funext i; exact Subtype.ext (hgerm i)
  refine ⟨U, hU, s, hm, l, by rw [hwf, hl], ?_⟩
  intro h0
  apply heta
  rw [← hl, (map_eq_zero_iff τ τ.injective).mp h0, zero_smul]

/-- **The measure `(i/2)^g η ∧ η̄`, characterized.** For `η ≠ 0`, a Borel measure on `A_τ(ℂ)` has the
density of `(i/2)^g η ∧ η̄` at every point (in translated algebraic charts) iff it is finite,
left-invariant and has that density at the identity. Invariance is proved, from the uniqueness of
measures with given local densities. -/
theorem isFormMeasure_iff {g : ℕ} (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (eta : M.model.hodgeSpace g) (heta : eta ≠ 0) (nu : @Measure (M.model.Pts τ) (anBorel M.model τ)) :
    IsFormMeasure M.model τ nu eta ↔
      @IsFiniteMeasure _ (anBorel M.model τ) nu ∧ @Measure.IsMulLeftInvariant _ (anBorel M.model τ) _ nu ∧
        IsNormalizedBy M.model τ nu eta := by
  obtain ⟨hTG, hC, U, hU, s, hm, l, hrep, hl⟩ := metrized_setup M τ eta heta
  letI := anTop M.model τ
  letI := anBorel M.model τ
  haveI : BorelSpace (M.model.Pts τ) := ⟨rfl⟩
  constructor
  · rintro ⟨hfin, hden⟩
    refine ⟨hfin, ?_, (isNormalizedBy_iff _ _ _ _).mpr (hden 1)⟩
    exact isMulLeftInvariant_of_densAt nu (coordMap M.model τ U s) (‖τ l‖ ^ 2)
      (by positivity) fun p => (hasFormDensityAt_iff _ _ _ _ _).mp (hden p) U hU s hm l hrep
  · rintro ⟨hfin, hinv, hnorm⟩
    refine ⟨hfin, fun p => (hasFormDensityAt_iff _ _ _ _ _).mpr fun U' hU' s' hm' l' hrep' => ?_⟩
    exact densAt_of_invariant nu _ _
      ((hasFormDensityAt_iff _ _ _ _ _).mp ((isNormalizedBy_iff _ _ _ _).mp hnorm) U' hU' s' hm' l'
        hrep') p

/-- **The printed metric is the kernel's metric**: for `η ≠ 0`, the measure `(i/2)^g η ∧ η̄` exists and
`(i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄ = |c_τ η|² covol(Λ_τ)` (`torusMetricSq`). -/
theorem isPrintedMetricSq_iff {g : ℕ} (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (eta : M.model.hodgeSpace g) (heta : eta ≠ 0) (r : ℝ) :
    IsPrintedMetricSq M.model τ eta r ↔
      r = torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta) := by
  letI := anBorel M.model τ
  have hmass : ∀ nu : Measure (M.model.Pts τ), IsFormMeasure M.model τ nu eta →
      (nu univ).toReal = torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta) := by
    intro nu hnu
    obtain ⟨h1, h2, h3⟩ := (isFormMeasure_iff M τ eta heta nu).mp hnu
    exact isFaltingsMetricSq_of_metrized M τ eta nu h1 h2 h3
  have hex : ∃ nu : Measure (M.model.Pts τ), IsFormMeasure M.model τ nu eta := by
    obtain ⟨nu, h1, h2, h3⟩ := exists_isNormalizedBy M τ eta heta
    exact ⟨nu, (isFormMeasure_iff M τ eta heta nu).mpr ⟨h1, h2, h3⟩⟩
  constructor
  · rintro ⟨-, hall⟩
    obtain ⟨nu, hnu⟩ := hex
    rw [← hall nu hnu, hmass nu hnu]
  · rintro rfl
    exact ⟨hex, hmass⟩

end Metrized

/-! ## §3b. The translated algebraic coordinates are charts of `A_τ(ℂ)` (inverse function theorem) -/

section Charts

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- **Charts.** Let `η ≠ 0` and `η = l · df₁ ∧ ⋯ ∧ df_g` at the origin. Then for every point `p` the
translated algebraic coordinates `q ↦ F(p⁻¹ q)` (`chartAt`) are a chart of `A_τ(ℂ)` at `p`: they agree,
on an open neighbourhood of `p`, with a homeomorphism onto an open subset of `ℂ^g`. Proof: `F ∘ Φ`
is holomorphic (`Holomorphic.hasStrictFDerivAt`) with derivative of determinant `jacDet Φ f ≠ 0` at
`0`, so the inverse function theorem applies; `Φ` is injective and open on a small ball. -/
theorem exists_chart {g : ℕ} (M : MetrizedModel A L g) (τ : L →+* ℂ)
    (eta : M.model.hodgeSpace g) (heta : eta ≠ 0) (U : Fin g → M.model.G.left.Opens)
    (hU : ∀ i, M.model.genericUnit ∈ U i) (s : ∀ i, Γ(M.model.G.left, U i))
    (hm : ∀ i, M.model.G.left.presheaf.germ (U i) M.model.genericUnit (hU i) (s i) ∈
      IsLocalRing.maximalIdeal M.model.genStalk) (l : L)
    (hrep : eta = l • M.model.wedge (fun i => ⟨_, hm i⟩)) (p : M.model.Pts τ) :
    letI := anTop M.model τ
    ∃ e : OpenPartialHomeomorph (M.model.Pts τ) (Fin g → ℂ), p ∈ e.source ∧
      Set.EqOn (chartAt M.model τ U s p) e e.source := by
  obtain ⟨Φ, hΦ, hc⟩ := M.arch τ
  letI := anTop M.model τ
  haveI : T2Space (M.model.Pts τ) := analyticPointsT2 K A L M.model τ
  haveI := M.hodge.periods_discrete τ
  haveI := M.hodge.periods_isZLattice τ
  have hUnif : TorusVolume.IsUnif (M.hodge.periods τ) Φ :=
    ⟨continuous_of_isAnalyticUniformization M.model τ hΦ, hΦ.1, hΦ.2.1, hΦ.2.2.1⟩
  haveI := hUnif.isTopologicalGroup
  set F := coordMap M.model τ U s
  -- the derivative of `F ∘ Φ` at `0` is invertible
  have hdet := det_fderiv_coordMap M.model hΦ U hU s hm
  have hcoeff : M.hodge.coeff τ eta = τ l * M.model.jacDet Φ (fun i => ⟨_, hm i⟩) := by
    rw [hrep, map_smulₛₗ, hc, smul_eq_mul]
  have hdet0 : LinearMap.det ((fderiv ℂ (F ∘ Φ) 0 : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) :
      (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) ≠ 0 := by
    rw [hdet]
    intro h0
    apply M.hodge.coeff_apply_ne_zero τ heta
    rw [hcoeff, h0, mul_zero]
  set D := fderiv ℂ (F ∘ Φ) 0
  let De : (Fin g → ℂ) ≃L[ℂ] (Fin g → ℂ) :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hdet0)).toContinuousLinearEquiv
  have hDe : (De : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) = D := by
    ext x
    simp [De]
  set V := ⋂ i, M.model.dom Φ (U i)
  have hVo : IsOpen V := isOpen_iInter_of_finite fun i => hΦ.2.2.2.1 (U i)
  have h0V : (0 : Fin g → ℂ) ∈ V :=
    mem_iInter.mpr fun i => ZInQ.Metrization.zero_mem_dom M.model hΦ (U i) (hU i)
  have hψd : DifferentiableOn ℂ (F ∘ Φ) V :=
    differentiableOn_pi.mpr fun i => (hΦ.2.2.2.2 (U i) (s i)).mono (iInter_subset _ i)
  have hstrict : HasStrictFDerivAt (F ∘ Φ) (De : (Fin g → ℂ) →L[ℂ] (Fin g → ℂ)) 0 := by
    rw [hDe]; exact Holomorphic.hasStrictFDerivAt hVo hψd h0V
  let e := hstrict.toOpenPartialHomeomorph (F ∘ Φ)
  -- `Φ` on a small ball
  obtain ⟨r₀, hr₀, hsep⟩ := TorusVolume.exists_ball_sub_mem (M.hodge.periods τ)
  have hinj : Set.InjOn Φ (Metric.ball 0 r₀) := fun x hx y hy hxy =>
    hsep x hx y hy ((hUnif.eq_iff x y).mp hxy)
  let Φl := OpenPartialHomeomorph.ofContinuousOpen (hinj.toPartialEquiv Φ (Metric.ball 0 r₀))
    hUnif.cont.continuousOn hUnif.isOpenMap Metric.isOpen_ball
  have hΦl : ∀ z, Φl z = Φ z := fun z => rfl
  have hΦls : Φl.source = Metric.ball 0 r₀ := rfl
  have h0s : (0 : Fin g → ℂ) ∈ Φl.source := by rw [hΦls]; exact Metric.mem_ball_self hr₀
  let c := Φl.symm.trans e
  have h1 : (1 : M.model.Pts τ) ∈ c.source := by
    have h1t : (1 : M.model.Pts τ) ∈ Φl.target := by
      rw [← hUnif.map_zero, ← hΦl]; exact Φl.map_source h0s
    have hsym : Φl.symm 1 = 0 := by
      rw [← hUnif.map_zero, ← hΦl]; exact Φl.left_inv h0s
    refine ⟨by simpa using h1t, ?_⟩
    show Φl.symm 1 ∈ e.source
    rw [hsym]; exact hstrict.mem_toOpenPartialHomeomorph_source
  have hc' : Set.EqOn F c c.source := by
    intro q hq
    have hqt : q ∈ Φl.target := by
      have := hq.1; simpa using this
    show F q = e (Φl.symm q)
    rw [hstrict.toOpenPartialHomeomorph_coe, Function.comp_apply, ← hΦl, Φl.right_inv hqt]
  -- translate to `p`
  let T := (Homeomorph.mulLeft p⁻¹).toOpenPartialHomeomorph
  refine ⟨T.trans c, ?_, ?_⟩
  · refine ⟨mem_univ _, ?_⟩
    show p⁻¹ * p ∈ c.source
    rw [inv_mul_cancel]; exact h1
  · intro q hq
    exact hc' hq.2

end Charts

/-! ## §4. Existence of the measure `(i/2)^g η ∧ η̄` for every group model (from T35) -/

section Existence

variable {K : Type} [Field K] [NumberField K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L]
  [Algebra K L]

/-- Every group model of `A_L` of dimension `g = dim A` carries a metrization (T35). -/
theorem exists_metrized (hT35 : ZInQ.LeafPush2.UniformizationExists) (𝒢 : GroupModel A L) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞)) : ∃ M : MetrizedModel A L g, M.model = 𝒢 :=
  metrizationOfUniformization K A L 𝒢 g hg fun τ =>
    ZInQ.Metrization2.analyticUniformizationOfDim_of_uniformizationExists hT35 K A L 𝒢 τ g hg

/-- **Existence (soundness of the printed metric).** For every group model `𝒢` of `A_L` (in particular
every Néron model), `g = dim A`, every `τ : L → ℂ` and every `η ≠ 0` in `L ⊗ ⋀^g ω`, the measure
`(i/2)^g η ∧ η̄` on `A_τ(ℂ)` exists (`|c_τ η|²` times the Haar measure `Φ_*(Lebesgue|_D)` of the
compact group `A_τ(ℂ)`), and its total mass is well defined. -/
theorem existsUnique_isPrintedMetricSq (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (eta : 𝒢.hodgeSpace g) (heta : eta ≠ 0) : ∃! r : ℝ, IsPrintedMetricSq 𝒢 τ eta r := by
  obtain ⟨M, rfl⟩ := exists_metrized hT35 𝒢 g hg
  exact ⟨_, (isPrintedMetricSq_iff M τ eta heta _).mpr rfl,
    fun r hr => (isPrintedMetricSq_iff M τ eta heta r).mp hr⟩

theorem exists_isFormMeasure (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (𝒢 : GroupModel A L) (g : ℕ) (hg : A.dim = (g : WithBot ℕ∞)) (τ : L →+* ℂ)
    (eta : 𝒢.hodgeSpace g) (heta : eta ≠ 0) :
    letI := anBorel 𝒢 τ
    ∃ nu : Measure (𝒢.Pts τ), IsFormMeasure 𝒢 τ nu eta := by
  obtain ⟨r, hr, -⟩ := existsUnique_isPrintedMetricSq hT35 𝒢 g hg τ eta heta
  exact hr.1

end Existence

/-! ## §5. Semistable reduction over `k(𝔭)` (SGA 7 IX Déf. 2.2/3.2 as printed) -/

section Semistable

open DictModels.RaynaudOr ReductGlue

variable {K : Type} [Field K] {A : PkgI3.AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

/-- `Spec k(𝔭) → Spec 𝓞_L`. -/
noncomputable abbrev sResP (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    Spec (CommRingCat.of 𝔭.ResidueField) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) 𝔭.ResidueField))

/-- The special fibre `𝒢 ×_{𝓞_L} k(𝔭)` of a group model at `𝔭`, over the residue field itself. -/
noncomputable def resFibre (𝒢 : GroupModel A L) (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    Over (Spec (CommRingCat.of 𝔭.ResidueField)) :=
  (Over.pullback (sResP 𝔭)).obj 𝒢.G

noncomputable instance (𝒢 : GroupModel A L) (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    GrpObj (resFibre 𝒢 𝔭) :=
  Functor.grpObjObj

/-- **Semistable reduction everywhere, as SGA 7 IX Déf. 2.2/3.2 print it** (over the residue field
`k(𝔭)`; locators UNVERIFIED): at every maximal ideal `𝔭` of `𝓞_L`, the identity component of the
special fibre `𝒩 ×_{𝓞_L} k(𝔭)` is an extension of an abelian variety over `k(𝔭)` by a torus
(a group with `T_{k̄} ≅ 𝔾_m^r`): `HasSemiAbelianIdCompTorus` (dict-models). -/
def IsSemistableRes (𝒢 : GroupModel A L) : Prop :=
  ∀ (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal], HasSemiAbelianIdCompTorus (resFibre 𝒢 𝔭)

theorem spec_bar_compP (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] :
    sφ (φbar 𝔭.ResidueField) ≫ sResP 𝔭 =
      Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (ResBar 𝔭))) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- **Ascent: the `k(𝔭)` form gives the geometric form** `IsSemistable` (the kernel's, on
`𝒢 ×_{𝓞_L} κ̄(𝔭)`), from Stacks 04KV (`GeomConnOfRationalPoint`, a textbook field) through
dict-models' `hasSemiAbelian_pullback_bar`. -/
theorem isSemistable_of_res (hGC : AVGlue.GeomConnOfRationalPoint) (𝒢 : GroupModel A L)
    (h : IsSemistableRes 𝒢) : IsSemistable 𝒢 := by
  intro 𝔭 _
  haveI : LocallyOfFiniteType (resFibre 𝒢 𝔭).hom := by
    change LocallyOfFiniteType (Limits.pullback.snd 𝒢.G.hom (sResP 𝔭)); infer_instance
  haveI : QuasiCompact (resFibre 𝒢 𝔭).hom := by
    change QuasiCompact (Limits.pullback.snd 𝒢.G.hom (sResP 𝔭)); infer_instance
  have h2 := hasSemiAbelian_pullback_bar hGC (resFibre 𝒢 𝔭) (h 𝔭)
  let E := pbCompIso _ _ _ (spec_bar_compP 𝔭) (Grp.mk 𝒢.G)
  exact @hasSemiAbelian_of_iso _ _ _ (geomFibre 𝒢 𝔭) Functor.grpObjObj _
      (isoX E) (inferInstanceAs (IsMonHom E.hom.hom.hom)) h2

/-- **GLUE `SemiAbelianDescendsPerfect`** (descent from `k̄` to a perfect field `k`). Let `G` be a group
scheme of finite type over a perfect field `k`. If the identity component of `G_{k̄}` is an extension
of an abelian variety by a (split) torus, then the identity component of `G` is an extension of an
abelian variety over `k` by a torus. STANDARD argument (SPECULATIVE as a Lean statement; locators
UNVERIFIED): `G⁰` is defined over `k` with `(G⁰)_{k̄} = (G_{k̄})⁰` (Stacks 04KV); Chevalley's theorem
over a perfect field (Conrad, J. Ramanujan Math. Soc. 17 (2002), Thm 1.1) gives `1 → H → G⁰ → B → 1`
over `k` with `H` smooth connected affine and `B` an abelian variety, compatible with base change;
`H_{k̄}` is the affine part of `(G_{k̄})⁰`, a torus. Complements unipotent-b's
`UnipotentForward.SemiAbelianDescendsSepClosed` (separably closed residue fields). -/
def SemiAbelianDescendsPerfect : Prop :=
  ∀ (k : Type) [Field k] [PerfectField k] (G : Over (Spec (CommRingCat.of k))) [GrpObj G]
    [LocallyOfFiniteType G.hom] [QuasiCompact G.hom],
    letI : GrpObj ((Over.pullback (sφ (φbar k))).obj G) := Functor.grpObjObj
    HasSemiAbelianIdentityComponent ((Over.pullback (sφ (φbar k))).obj G) →
      HasSemiAbelianIdCompTorus G

/-- The residue fields of `𝓞_L` at maximal ideals are finite, hence perfect. -/
theorem perfectField_residueField (𝔭 : Ideal (𝓞 L)) [𝔭.IsMaximal] : PerfectField 𝔭.ResidueField := by
  have hne : 𝔭 ≠ ⊥ := by
    intro h
    apply NumberField.RingOfIntegers.not_isField L
    rw [Ring.isField_iff_maximal_bot, ← h]
    infer_instance
  haveI := Ideal.finiteQuotientOfFreeOfNeBot 𝔭 hne
  infer_instance

/-- **Descent: the geometric form gives the `k(𝔭)` form**, from the glue `SemiAbelianDescendsPerfect`
(residue fields of number rings are finite). -/
theorem isSemistableRes_of_geom (hD : SemiAbelianDescendsPerfect) (𝒢 : GroupModel A L)
    (h : IsSemistable 𝒢) : IsSemistableRes 𝒢 := by
  intro 𝔭 _
  haveI := perfectField_residueField 𝔭
  haveI : LocallyOfFiniteType (resFibre 𝒢 𝔭).hom := by
    change LocallyOfFiniteType (Limits.pullback.snd 𝒢.G.hom (sResP 𝔭)); infer_instance
  haveI : QuasiCompact (resFibre 𝒢 𝔭).hom := by
    change QuasiCompact (Limits.pullback.snd 𝒢.G.hom (sResP 𝔭)); infer_instance
  letI : GrpObj ((Over.pullback (sφ (φbar 𝔭.ResidueField))).obj (resFibre 𝒢 𝔭)) :=
    Functor.grpObjObj
  refine hD 𝔭.ResidueField (resFibre 𝒢 𝔭) ?_
  let E := pbCompIso _ _ _ (spec_bar_compP 𝔭) (Grp.mk 𝒢.G)
  exact @hasSemiAbelian_of_iso _ _ (geomFibre 𝒢 𝔭) _ _ Functor.grpObjObj
      (isoX E).symm (inferInstanceAs (IsMonHom E.inv.hom.hom)) (h 𝔭)

end Semistable

/-! ## §6. The printed stable height and the two leaves -/

open DictModels.RaynaudOr

/-- **Faltings' stable height, as the print builds it** (Faltings 1983 §1; Deligne, Sém. Bourbaki 616
§1; locators UNVERIFIED): `x = deg(ω̄_𝒩)/[L:ℚ]` for the Néron model `𝒩` of `A_L` over a number field
`L ⊇ K` over which `A` has semistable reduction everywhere in the sense of SGA 7 IX Déf. 2.2/3.2
(`IsSemistableRes`, over the residue fields `k(𝔭)`), `g = dim A`, `ω_𝒩 = ⋀^g Γ(S, e*Ω¹)`
(`printedDetLattice`), computed with any nonzero section `η`:
`deg = log #(ω_𝒩/𝓞_L η) − ½ ∑_{τ : L → ℂ} log ‖η‖²_τ`, where `‖η‖²_τ = (i/2)^g ∫_{A_τ(ℂ)} η ∧ η̄` is the
total mass of the measure `(i/2)^g η ∧ η̄`, defined chart by chart (`IsPrintedMetricSq`: it exists and
every such measure has that mass). -/
def IsPrintedStableHeight {K : Type} [Field K] (A : PkgI3.AbVar K) (x : ℝ) : Prop :=
  ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L) (𝒩 : GroupModel A L) (g : ℕ),
    𝒩.IsNeronModel ∧ IsSemistableRes 𝒩 ∧ A.dim = (g : WithBot ℕ∞) ∧
    ∃ eta ∈ printedDetLattice 𝒩 g, eta ≠ 0 ∧ secIndex (printedDetLattice 𝒩 g) eta ≠ 0 ∧
      ∃ r : (L →+* ℂ) → ℝ, (∀ τ, IsPrintedMetricSq 𝒩 τ eta (r τ)) ∧
        x = (Real.log (secIndex (printedDetLattice 𝒩 g) eta) -
          (1 / 2) * ∑ τ : L →+* ℂ, Real.log (r τ)) / Module.finrank ℚ L

/-- **Leaf R21-Bost over the printed height** (J.-B. Bost, Sém. Bourbaki 795 (1994/95), Astérisque
237 (1996); display UNVERIFIED): `ZInQ.HeightSplit.BostLowerBound` with `IsStableFaltingsHeight`
replaced by `IsPrintedStableHeight` (Deligne's normalization `h_D = h_F + (g/2) log π`). -/
def BostLowerBoundPrinted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∀ x : ℝ, IsPrintedStableHeight A x →
      -((g : ℝ) / 2 * Real.log (2 * Real.pi)) ≤ x + (g : ℝ) / 2 * Real.log Real.pi

/-- **Leaf R19-GR over the printed height** (Gaudron–Rémond, Duke Math. J. 163 (2014), Thm 1.4,
p. 2060; `κ` p. 2058; read by the locator audit): `ZInQ.HeightSplit.GaudronRemondThm14` with
`IsStableFaltingsHeight` replaced by `IsPrintedStableHeight` (stable height, Faltings' original
normalization). -/
def GaudronRemondThm14Printed : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
    A.dim = (g : WithBot ℕ∞) → IsPrintedStableHeight A x →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
    (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
    (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)

/-- **Kernel height ⇒ printed height** (T35 and the descent glue). -/
theorem isPrintedStableHeight_of (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hD : SemiAbelianDescendsPerfect) {K : Type} [Field K] {A : PkgI3.AbVar K} {x : ℝ}
    (hx : IsStableFaltingsHeight A x) : IsPrintedStableHeight A x := by
  have hU := analyticUniformizationUnique_of_t35 hT35
  have hDim := uniformizationDim_of_t35 hT35
  obtain ⟨L, iF, iN, iA, 𝒩, hN, hS, hh⟩ := hx
  have hM : ∃ (g : ℕ) (M : MetrizedModel A L g), M.model = 𝒩 := by
    by_contra hcon
    push Not at hcon
    have htop : 𝒩.height = ⊤ :=
      le_antisymm le_top (le_iInf fun g => le_iInf fun M => le_iInf fun h => absurd h (hcon g M))
    rw [htop] at hh
    exact EReal.coe_ne_top x hh.symm
  obtain ⟨g, M, rfl⟩ := hM
  have hxM : x = M.hodge.modelHeight := by
    have := groupModel_height_eq hU metrizedDimUnique M
    rw [hh] at this
    exact_mod_cast this
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨Φ₀, hΦ₀, -⟩ := M.arch τ₀
  have hdim : A.dim = (g : WithBot ℕ∞) := hDim K A L M.model τ₀ g _ Φ₀
    (M.hodge.periods_discrete τ₀) (M.hodge.periods_isZLattice τ₀) hΦ₀
  obtain ⟨eta, hetaM, heta0, hsec⟩ := M.hodge.isLattice
  have hetaM' : eta ∈ printedDetLattice M.model g := by
    rw [printedDetLattice_eq]; exact M.lattice_eq ▸ hetaM
  have hsec' : secIndex (printedDetLattice M.model g) eta ≠ 0 := by
    rw [printedDetLattice_eq]; exact M.lattice_eq ▸ hsec
  refine ⟨L, iF, iN, iA, M.model, g, hN, isSemistableRes_of_geom hD M.model hS, hdim, eta, hetaM',
    heta0, hsec', fun τ => torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta),
    fun τ => (isPrintedMetricSq_iff M τ eta heta0 _).mpr rfl, ?_⟩
  rw [hxM, M.hodge.modelHeight_eq hetaM heta0, M.lattice_eq, printedDetLattice_eq]

/-- **Printed height ⇒ kernel height** (T35 and Stacks 04KV; no Néron-metrizability hypothesis:
`NeronMetrizable` is proved from T35, `neronMetrizable_of_t35`). -/
theorem isStableFaltingsHeight_of_printed (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hGC : AVGlue.GeomConnOfRationalPoint) {K : Type} [Field K] [NumberField K]
    {A : PkgI3.AbVar K} {x : ℝ} (hx : IsPrintedStableHeight A x) : IsStableFaltingsHeight A x := by
  have hU := analyticUniformizationUnique_of_t35 hT35
  have hDim := uniformizationDim_of_t35 hT35
  obtain ⟨L, iF, iN, iA, 𝒩, g, hN, hS, hdim, eta, hetaM, heta0, hsec, r, hr, hxr⟩ := hx
  obtain ⟨g', M, rfl⟩ := neronMetrizable_of_t35 hT35 K A L 𝒩 hN
  obtain ⟨τ₀⟩ : Nonempty (L →+* ℂ) := ⟨(IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom⟩
  obtain ⟨Φ₀, hΦ₀, -⟩ := M.arch τ₀
  have hdim' : A.dim = (g' : WithBot ℕ∞) := hDim K A L M.model τ₀ g' _ Φ₀
    (M.hodge.periods_discrete τ₀) (M.hodge.periods_isZLattice τ₀) hΦ₀
  have hgg : g = g' := by
    have := hdim.symm.trans hdim'
    exact_mod_cast this
  subst hgg
  have hrτ : ∀ τ, r τ = torusMetricSq (M.hodge.periods τ) (M.hodge.coeff τ eta) := fun τ =>
    (isPrintedMetricSq_iff M τ eta heta0 (r τ)).mp (hr τ)
  rw [printedDetLattice_eq] at hetaM hxr
  have hetaL : eta ∈ M.hodge.lattice := M.lattice_eq ▸ hetaM
  refine ⟨L, iF, iN, iA, M.model, hN, isSemistable_of_res hGC M.model hS, ?_⟩
  rw [groupModel_height_eq hU metrizedDimUnique M, M.hodge.modelHeight_eq hetaL heta0, hxr,
    M.lattice_eq]
  simp only [hrτ]

/-- **The printed stable height and the kernel's coincide** (given T35, Stacks 04KV and the descent
glue). -/
theorem isPrintedStableHeight_iff (hT35 : ZInQ.LeafPush2.UniformizationExists)
    (hGC : AVGlue.GeomConnOfRationalPoint) (hD : SemiAbelianDescendsPerfect) {K : Type} [Field K]
    [NumberField K] (A : PkgI3.AbVar K) (x : ℝ) :
    IsPrintedStableHeight A x ↔ IsStableFaltingsHeight A x :=
  ⟨isStableFaltingsHeight_of_printed hT35 hGC, isPrintedStableHeight_of hT35 hD⟩

/-- **The field `bostLowerBound`** from the printed leaf, the textbook fields `uniformizationLeafAll`,
`mumfordTorsionAlgClosed` (which give T35) and the descent glue. -/
theorem bostLowerBound_of_printed (hB : BostLowerBoundPrinted)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) (hD : SemiAbelianDescendsPerfect) : BostLowerBound :=
  fun K _ _ A g hg x hx => hB K A g hg x (isPrintedStableHeight_of (AvSplit.Final.h38 hUL hMT) hD hx)

/-- **The field `gaudronRemondThm14`** from the printed leaf, the textbook fields
`uniformizationLeafAll`, `mumfordTorsionAlgClosed` and the descent glue. -/
theorem gaudronRemondThm14_of_printed (hGR : GaudronRemondThm14Printed)
    (hUL : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hMT : AvSplit.MumfordTorsionAlgClosed) (hD : SemiAbelianDescendsPerfect) :
    GaudronRemondThm14 :=
  fun K _ _ A B g x hg hx hiso =>
    hGR K A B g x hg (isPrintedStableHeight_of (AvSplit.Final.h38 hUL hMT) hD hx) hiso

/-- The new leaf is implied by the old kernel row (given T35 and Stacks 04KV): it is never stronger than
`BostLowerBound`. -/
theorem bostLowerBoundPrinted_of_kernel (h : BostLowerBound)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) (hGC : AVGlue.GeomConnOfRationalPoint) :
    BostLowerBoundPrinted :=
  fun K _ _ A g hg x hx => h K A g hg x (isStableFaltingsHeight_of_printed hT35 hGC hx)

/-- The new leaf is implied by the old kernel row (given T35 and Stacks 04KV). -/
theorem gaudronRemondThm14Printed_of_kernel (h : GaudronRemondThm14)
    (hT35 : ZInQ.LeafPush2.UniformizationExists) (hGC : AVGlue.GeomConnOfRationalPoint) :
    GaudronRemondThm14Printed :=
  fun K _ _ A B g x hg hx hiso => h K A B g x hg (isStableFaltingsHeight_of_printed hT35 hGC hx) hiso

end ZInQ.HeightFix
