import PGLight
/-! # period-glue: `SphereFactorAffine` from three textbook facts of one-variable complex analysis

Task period-glue, 2026-11-13. `SphereFactorAffine` (period-map, `PGLight`, unchanged) is proved
(`sphereFactorAffine_of`) from
* `HolP1OpenMap` (open mapping theorem for maps `ℍ → P¹`),
* `HolP1FactorHol` (a continuous `φ` with `h = φ ∘ f`, `f` onto and holomorphic, is
  holomorphic on `P¹`: local inverse off the critical values, removable singularities), and
* `SphereInjAffine` (an injective holomorphic self-map of `P¹` fixing `∞` is affine).
All three are **GLUE** (textbook complex analysis, not in Mathlib v4.35 in this form). Proved
here: holomorphy into `P¹` (`IsHolP1At`) implies continuity (`continuousAt_of_isHolP1At`); `φ`
is well defined, injective, continuous (`f` is open), and fixes `∞`. -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open Complex Filter Topology HSyn.G0Split.FibreQM HSyn.G0Split.FibreQM.PeriodMap

/-- `g : ℂ → P¹(ℂ)` is holomorphic at `z` (the shape of `IsHolP1At`, on `ℂ`). -/
def IsHolC1At (g : ℂ → OnePoint ℂ) (z : ℂ) : Prop :=
  (∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ ∀ᶠ w in 𝓝 z, g w = (G w : OnePoint ℂ)) ∨
  (∃ G : ℂ → ℂ, AnalyticAt ℂ G z ∧ G z = 0 ∧
      ∀ᶠ w in 𝓝 z, g w = if G w = 0 then OnePoint.infty else (((G w)⁻¹ : ℂ) : OnePoint ℂ))

/-- The chart of `P¹` at `∞`: `w ↦ 1/w`, `0 ↦ ∞`. -/
def chartInf (w : ℂ) : OnePoint ℂ := if w = 0 then OnePoint.infty else ((w⁻¹ : ℂ) : OnePoint ℂ)

/-- `φ : P¹ → P¹` is holomorphic: in the chart `ℂ` at every point, and in the chart at `∞`. -/
def IsHolSphere (φ : OnePoint ℂ → OnePoint ℂ) : Prop :=
  (∀ z : ℂ, IsHolC1At (fun w => φ (w : OnePoint ℂ)) z) ∧ IsHolC1At (fun w => φ (chartInf w)) 0

/-- **GLUE (open mapping theorem on `ℍ`, maps to `P¹`).** A map `g : ℍ → P¹(ℂ)` that is
holomorphic into `P¹` at every point and not constant is an open map.

Why true: `ℍ` is connected, so by the identity theorem (applied in charts) `g` is nowhere locally
constant; locally `g` or `1/g` is a non-constant analytic function, which is open (Mathlib:
`AnalyticOnNhd.is_constant_or_isOpen`), and `w ↦ 1/w` is a homeomorphism of `P¹`. (Ahlfors,
*Complex Analysis*, Ch. 4, §3.3; UNVERIFIED locator.) Size: small-medium. -/
def HolP1OpenMap : Prop :=
  ∀ g : UpperHalfPlane → OnePoint ℂ, (∀ τ, IsHolP1At g τ) → (∃ τ τ', g τ ≠ g τ') → IsOpenMap g

/-- **GLUE (holomorphic factorization).** If `f, h : ℍ → P¹(ℂ)` are holomorphic into `P¹`,
`f` is onto, and `h = φ ∘ f` with `φ : P¹ → P¹` continuous, then `φ` is holomorphic on `P¹`.

Why true: at `p = f(τ₀)`, the critical points of `f` near `τ₀` are isolated, so on a punctured
neighbourhood of `p` the map `φ = h ∘ f⁻¹` (local holomorphic inverse, Mathlib's
`HasStrictDerivAt.localInverse` in charts) is holomorphic; `φ` is continuous at `p`, so the
singularity is removable (Mathlib: `Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt`,
applied to `φ` or `1/φ` in charts). (Ahlfors Ch. 4 §3.2-3.3; UNVERIFIED locators.)
Size: medium. -/
def HolP1FactorHol : Prop :=
  ∀ (f h : UpperHalfPlane → OnePoint ℂ) (φ : OnePoint ℂ → OnePoint ℂ),
    (∀ τ, IsHolP1At f τ) → (∀ τ, IsHolP1At h τ) → Function.Surjective f → Continuous φ →
    (∀ τ, h τ = φ (f τ)) → IsHolSphere φ

/-- **GLUE (textbook: injective holomorphic maps of the sphere).** An injective holomorphic
`φ : P¹ → P¹` with `φ(∞) = ∞` is `z ↦ az + b`, `a ≠ 0`.

Why true: `φ(ℂ) ⊆ ℂ` (injective, `φ(∞) = ∞`), so `φ|ℂ` is entire; holomorphy at `∞` with value
`∞` gives `|φ(z)| → ∞`, so `φ|ℂ` is a polynomial (Liouville / pole at `∞`); an injective
polynomial has degree one (a polynomial of degree `≥ 2` has a critical point or a value taken
twice). (Ahlfors Ch. 4; Conway, *Functions of One Complex Variable*, Ch. V; UNVERIFIED locators.)
Size: medium (polynomial from a pole at `∞`). -/
def SphereInjAffine : Prop :=
  ∀ φ : OnePoint ℂ → OnePoint ℂ, IsHolSphere φ → Function.Injective φ →
    φ OnePoint.infty = OnePoint.infty →
    ∃ a b : ℂ, a ≠ 0 ∧ ∀ z : ℂ, φ (z : OnePoint ℂ) = ((a * z + b : ℂ) : OnePoint ℂ)

/-! ### Holomorphic into `P¹` implies continuous (proved) -/

theorem tendsto_ite_inv {G : ℂ → ℂ} {z0 : ℂ} (hG : ContinuousAt G z0) (h0 : G z0 = 0) :
    Tendsto (fun z => if G z = 0 then (OnePoint.infty : OnePoint ℂ)
      else (((G z)⁻¹ : ℂ) : OnePoint ℂ)) (𝓝 z0) (𝓝 OnePoint.infty) := by
  rw [OnePoint.nhds_infty_eq]
  intro s hs
  rw [Filter.mem_sup, Filter.mem_map, Filter.mem_pure] at hs
  obtain ⟨hs1, hs2⟩ := hs
  obtain ⟨t, ⟨-, htc⟩, hts⟩ := hasBasis_coclosedCompact.mem_iff.mp hs1
  obtain ⟨R, hR⟩ := htc.isBounded.subset_closedBall 0
  set R' := max R 1 with hR'
  have hR'pos : 0 < R' := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hev : ∀ᶠ z in 𝓝 z0, ‖G z‖ < R'⁻¹ := by
    have h' : Tendsto (fun x => ‖G x‖) (𝓝 z0) (𝓝 0) := by
      have h'' : Tendsto (fun x => ‖G x‖) (𝓝 z0) (𝓝 ‖G z0‖) := hG.norm
      rwa [h0, norm_zero] at h''
    exact h' (Iio_mem_nhds (inv_pos.mpr hR'pos))
  rw [Filter.mem_map]
  filter_upwards [hev] with z hz
  rw [Set.mem_preimage]
  by_cases hz0 : G z = 0
  · rw [if_pos hz0]; exact hs2
  · rw [if_neg hz0]
    apply hts
    intro ht
    have h1 := hR ht
    rw [Metric.mem_closedBall, dist_zero_right, norm_inv] at h1
    have h2 : R' < ‖G z‖⁻¹ := by
      rw [lt_inv_comm₀ hR'pos (norm_pos_iff.mpr hz0)]; exact hz
    have : R ≤ R' := le_max_left _ _
    linarith

theorem continuousAt_of_isHolP1At {h : UpperHalfPlane → OnePoint ℂ} {τ : UpperHalfPlane}
    (hh : IsHolP1At h τ) : ContinuousAt h τ := by
  have hc : ContinuousAt (fun w : UpperHalfPlane => (w : ℂ)) τ :=
    UpperHalfPlane.continuous_coe.continuousAt
  rcases hh with ⟨G, hG, hev⟩ | ⟨G, hG, hG0, hev⟩
  · have hF : ContinuousAt (fun z : ℂ => (G z : OnePoint ℂ)) (τ : ℂ) :=
      OnePoint.continuous_coe.continuousAt.comp hG.continuousAt
    refine (hF.comp hc).congr ?_
    filter_upwards [hc.eventually hev] with w hw
    exact (hw w.im_pos).symm
  · have hF : ContinuousAt (fun z : ℂ => if G z = 0 then (OnePoint.infty : OnePoint ℂ)
        else (((G z)⁻¹ : ℂ) : OnePoint ℂ)) (τ : ℂ) := by
      unfold ContinuousAt
      simp only [hG0, ite_true]
      exact tendsto_ite_inv hG.continuousAt hG0
    refine (hF.comp hc).congr ?_
    filter_upwards [hc.eventually hev] with w hw
    exact (hw w.im_pos).symm

/-! ### The reduction -/

/-- **`SphereFactorAffine` from `HolP1OpenMap`, `HolP1FactorHol`, `SphereInjAffine` (proved).** -/
theorem sphereFactorAffine_of (hA : HolP1OpenMap) (hB : HolP1FactorHol) (hC : SphereInjAffine) :
    SphereFactorAffine := by
  intro f h hf hh hsurj hfib ⟨τ0, hf0, hh0⟩
  have hcont : Continuous h :=
    continuous_iff_continuousAt.mpr fun τ => continuousAt_of_isHolP1At (hh τ)
  have hnc : ∃ τ τ', f τ ≠ f τ' := by
    obtain ⟨τ, hτ⟩ := hsurj ((0 : ℂ) : OnePoint ℂ)
    exact ⟨τ, τ0, by rw [hτ, hf0]; exact OnePoint.coe_ne_infty 0⟩
  have hopen : IsOpenMap f := hA f hf hnc
  choose g hg using hsurj
  set φ : OnePoint ℂ → OnePoint ℂ := fun w => h (g w) with hφdef
  have hφ : ∀ τ, h τ = φ (f τ) := fun τ => (hfib _ _).mp (hg (f τ)).symm
  have hφc : Continuous φ := by
    rw [continuous_def]
    intro U hU
    have : φ ⁻¹' U = f '' (h ⁻¹' U) := by
      ext w
      constructor
      · intro hw
        exact ⟨g w, by simpa [hφdef] using hw, hg w⟩
      · rintro ⟨τ, hτ, rfl⟩
        show φ (f τ) ∈ U
        rw [← hφ]; exact hτ
    rw [this]
    exact hopen _ (hU.preimage hcont)
  have hinj : Function.Injective φ := by
    intro w w' hww
    have := (hfib (g w) (g w')).mpr hww
    rwa [hg, hg] at this
  have hinf : φ OnePoint.infty = OnePoint.infty := by
    have := (hφ τ0).symm
    rw [hf0] at this
    rw [this, hh0]
  have hsurj' : Function.Surjective f := fun w => ⟨g w, hg w⟩
  obtain ⟨a, b, ha, hab⟩ := hC φ (hB f h φ hf hh hsurj' hφc hφ) hinj hinf
  refine ⟨a, b, ha, fun τ => ?_⟩
  rw [hφ]
  generalize f τ = w
  induction w using OnePoint.rec with
  | infty => rw [hinf, OnePoint.map_infty]
  | coe z => rw [hab, OnePoint.map_some]

/-! ### `HolP1OpenMap` (proved) -/

theorem chartInf_injective : Function.Injective chartInf := by
  intro w w' h
  unfold chartInf at h
  by_cases hw : w = 0 <;> by_cases hw' : w' = 0
  · rw [hw, hw']
  · rw [if_pos hw, if_neg hw'] at h; exact absurd h.symm (OnePoint.coe_ne_infty _)
  · rw [if_neg hw, if_pos hw'] at h; exact absurd h (OnePoint.coe_ne_infty _)
  · rw [if_neg hw, if_neg hw'] at h
    exact inv_injective (OnePoint.coe_injective h)

theorem nhds_le_map_chartInf : 𝓝 (OnePoint.infty : OnePoint ℂ) ≤ map chartInf (𝓝 0) := by
  intro s hs
  rw [Filter.mem_map] at hs
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hs
  rw [OnePoint.nhds_infty_eq, Filter.mem_sup, Filter.mem_map, Filter.mem_pure]
  have h0 : chartInf 0 ∈ s := hball (Metric.mem_ball_self hε)
  have hc0 : chartInf 0 = OnePoint.infty := by simp [chartInf]
  rw [hc0] at h0
  refine ⟨?_, h0⟩
  rw [hasBasis_coclosedCompact.mem_iff]
  refine ⟨Metric.closedBall 0 ε⁻¹, ⟨Metric.isClosed_closedBall, isCompact_closedBall 0 _⟩, ?_⟩
  intro z hz
  simp only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] at hz
  have hz0 : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; linarith [inv_pos.mpr hε]
  have hmem : z⁻¹ ∈ Metric.ball (0 : ℂ) ε := by
    rw [Metric.mem_ball, dist_zero_right, norm_inv]
    exact inv_lt_of_inv_lt₀ hε hz
  have := hball hmem
  rw [Set.mem_preimage, chartInf, if_neg (inv_ne_zero hz0), inv_inv] at this
  exact this

/-- The chart of a holomorphic `P¹`-valued map at a point. -/
theorem chart_of_isHolP1At {g : UpperHalfPlane → OnePoint ℂ} {τ : UpperHalfPlane}
    (hg : IsHolP1At g τ) :
    ∃ (F : ℂ → OnePoint ℂ) (G : ℂ → ℂ), Function.Injective F ∧
      𝓝 (F (G τ)) ≤ map F (𝓝 (G τ)) ∧
      ∃ r > 0, (∀ z ∈ Metric.ball (τ : ℂ) r, 0 < z.im) ∧
        AnalyticOnNhd ℂ G (Metric.ball (τ : ℂ) r) ∧
        ∀ z (hz : 0 < z.im), z ∈ Metric.ball (τ : ℂ) r → g ⟨z, hz⟩ = F (G z) := by
  have him : ∀ᶠ z in 𝓝 (τ : ℂ), 0 < z.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ.im_pos
  rcases hg with ⟨G, hG, hev⟩ | ⟨G, hG, hG0, hev⟩
  · obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hev.and hG.eventually_analyticAt).and him)
    exact ⟨(↑), G, OnePoint.coe_injective, (OnePoint.isOpenEmbedding_coe.map_nhds_eq _).ge,
      r, hr, fun z hz => (hb z hz).2, fun z hz => (hb z hz).1.2,
      fun z hz hzb => (hb z hzb).1.1 hz⟩
  · obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp
      ((hev.and hG.eventually_analyticAt).and him)
    refine ⟨chartInf, G, chartInf_injective, ?_, r, hr, fun z hz => (hb z hz).2,
      fun z hz => (hb z hz).1.2, fun z hz hzb => (hb z hzb).1.1 hz⟩
    rw [hG0]
    have : chartInf 0 = OnePoint.infty := by simp [chartInf]
    rw [this]
    exact nhds_le_map_chartInf

theorem eventually_coe_iff {τ : UpperHalfPlane} {P : UpperHalfPlane → Prop} :
    (∀ᶠ σ in 𝓝 τ, P σ) ↔ ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, P ⟨z, hz⟩ := by
  rw [← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, Filter.eventually_map]
  constructor
  · intro h
    filter_upwards [h] with σ hσ
    intro hz
    exact hσ
  · intro h
    filter_upwards [h] with σ hσ
    exact hσ σ.im_pos

/-- **`HolP1OpenMap` (proved).** -/
theorem holP1OpenMap_proof : HolP1OpenMap := by
  intro g hg hnc
  choose F G hFi hFn r hr hpos hGan hgFG using fun τ => chart_of_isHolP1At (hg τ)
  have hgτ : ∀ τ : UpperHalfPlane, g τ = F τ (G τ τ) := fun τ =>
    hgFG τ τ τ.im_pos (Metric.mem_ball_self (hr τ))
  -- `g = F τ ∘ G τ` near `τ`, as a filter statement on `ℍ`
  have hloc : ∀ τ : UpperHalfPlane, ∀ᶠ σ in 𝓝 τ, g σ = F τ (G τ σ) := by
    intro τ
    rw [eventually_coe_iff]
    filter_upwards [Metric.ball_mem_nhds _ (hr τ)] with z hz hzi
    exact hgFG τ z hzi hz
  set S : Set UpperHalfPlane := {τ | ∀ᶠ σ in 𝓝 τ, g σ = g τ} with hSdef
  have hSopen : IsOpen S := by
    rw [isOpen_iff_mem_nhds]
    intro τ hτ
    obtain ⟨U, hU, hUo, hτU⟩ := eventually_nhds_iff.mp hτ
    filter_upwards [hUo.mem_nhds hτU] with σ hσ
    show ∀ᶠ σ' in 𝓝 σ, g σ' = g σ
    filter_upwards [hUo.mem_nhds hσ] with σ' hσ'
    rw [hU σ' hσ', hU σ hσ]
  -- if `g` is locally constant at some point of a chart ball, it is constant on the ball
  have hball_const : ∀ τ : UpperHalfPlane, ∀ σ : UpperHalfPlane,
      (σ : ℂ) ∈ Metric.ball (τ : ℂ) (r τ) → σ ∈ S →
      Set.EqOn (G τ) (fun _ => G τ σ) (Metric.ball (τ : ℂ) (r τ)) := by
    intro τ σ hσB hσS
    apply (hGan τ).eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const
      (convex_ball _ _).isPreconnected hσB
    have h1 := eventually_coe_iff.mp hσS
    filter_upwards [h1, Metric.isOpen_ball.mem_nhds hσB] with z hz hzB
    apply hFi τ
    rw [← hgFG τ z (hpos τ z hzB) hzB, hz (hpos τ z hzB), hgFG τ σ σ.im_pos hσB]
  have hSclosed : IsClosed S := by
    rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
    intro τ hτ
    show ∀ᶠ σ in 𝓝 τ, σ ∉ S
    rw [eventually_coe_iff]
    filter_upwards [Metric.ball_mem_nhds _ (hr τ)] with z hzB hzi hzS
    apply hτ
    have hc := hball_const τ ⟨z, hzi⟩ hzB hzS
    show ∀ᶠ σ in 𝓝 τ, g σ = g τ
    rw [eventually_coe_iff]
    filter_upwards [Metric.ball_mem_nhds _ (hr τ)] with w hwB hwi
    rw [hgFG τ w hwi hwB, hgτ τ, hc hwB, hc (Metric.mem_ball_self (hr τ))]
  have hSempty : S = ∅ := by
    rcases isClopen_iff.mp ⟨hSclosed, hSopen⟩ with h | h
    · exact h
    · exfalso
      obtain ⟨τ0, τ1, hne⟩ := hnc
      set T : Set UpperHalfPlane := {σ | g σ = g τ0} with hT
      have hTo : IsOpen T := by
        rw [isOpen_iff_mem_nhds]
        intro σ hσ
        have : σ ∈ S := h ▸ Set.mem_univ σ
        filter_upwards [this] with σ' hσ'
        show g σ' = g τ0
        rw [hσ']; exact hσ
      have hTc : IsClosed T := by
        rw [← isOpen_compl_iff, isOpen_iff_mem_nhds]
        intro σ hσ
        have : σ ∈ S := h ▸ Set.mem_univ σ
        filter_upwards [this] with σ' hσ'
        show ¬ g σ' = g τ0
        rw [hσ']; exact hσ
      rcases isClopen_iff.mp ⟨hTc, hTo⟩ with hT0 | hT1
      · have : τ0 ∈ T := rfl
        rw [hT0] at this; exact this
      · have : τ1 ∈ T := hT1 ▸ Set.mem_univ τ1
        exact hne this.symm
  -- open mapping at every point
  rw [isOpenMap_iff_nhds_le]
  intro τ
  have hnot : ¬ ∀ᶠ z in 𝓝 (τ : ℂ), G τ z = G τ τ := by
    intro hc
    have : τ ∈ S := by
      show ∀ᶠ σ in 𝓝 τ, g σ = g τ
      rw [eventually_coe_iff]
      filter_upwards [hc, Metric.ball_mem_nhds _ (hr τ)] with z hz hzB hzi
      rw [hgFG τ z hzi hzB, hgτ τ, hz]
    rw [hSempty] at this; exact this
  have hopen := ((hGan τ) τ (Metric.mem_ball_self (hr τ))).eventually_constant_or_nhds_le_map_nhds
  rcases hopen with h | h
  · exact absurd h hnot
  · calc 𝓝 (g τ) = 𝓝 (F τ (G τ τ)) := by rw [hgτ]
      _ ≤ map (F τ) (𝓝 (G τ τ)) := hFn τ
      _ ≤ map (F τ) (map (G τ) (𝓝 (τ : ℂ))) := Filter.map_mono h
      _ = map (fun σ : UpperHalfPlane => F τ (G τ σ)) (𝓝 τ) := by
          rw [Filter.map_map, ← UpperHalfPlane.isOpenEmbedding_coe.map_nhds_eq, Filter.map_map]
          rfl
      _ = map g (𝓝 τ) := Filter.map_congr (by
          filter_upwards [hloc τ] with σ hσ
          exact hσ.symm)

/-- **`SphereFactorAffine` from `HolP1FactorHol` and `SphereInjAffine` (proved).** -/
theorem sphereFactorAffine_of' (hB : HolP1FactorHol) (hC : SphereInjAffine) :
    SphereFactorAffine :=
  sphereFactorAffine_of holP1OpenMap_proof hB hC

/-! ### `SphereInjAffine` (proved)

`f = φ|ℂ` is entire and injective. Pick `z₁` with `f'(z₁) ≠ 0`; then `q = dslope f z₁` is entire
and never `0`, so `r = 1/q`, `r(z) = (z − z₁)/(f(z) − f(z₁))`, is entire. Near `∞`,
`f(z) = 1/G(1/z)` with `G(0) = 0`, so `r(z) → G'(0)`. By Liouville `r` is constant, and
`f(z) = f(z₁) + (z − z₁)/G'(0)`. -/

/-- **`SphereInjAffine` (proved).** -/
theorem sphereInjAffine_proof : SphereInjAffine := by
  intro φ ⟨hfin_hol, hinf_hol⟩ hinj hinf
  -- `φ` is finite on `ℂ`
  have hfin : ∀ z : ℂ, ∃ v : ℂ, φ (z : OnePoint ℂ) = (v : OnePoint ℂ) := by
    intro z
    have hne : φ (z : OnePoint ℂ) ≠ OnePoint.infty := by
      rw [← hinf]; intro h; exact OnePoint.coe_ne_infty z (hinj h)
    obtain ⟨v, hv⟩ := OnePoint.ne_infty_iff_exists.mp hne
    exact ⟨v, hv.symm⟩
  choose f hf using hfin
  have hfinj : Function.Injective f := by
    intro z z' h
    have : φ (z : OnePoint ℂ) = φ (z' : OnePoint ℂ) := by rw [hf, hf, h]
    exact OnePoint.coe_injective (hinj this)
  -- `f` is entire
  have hdiff : Differentiable ℂ f := by
    intro z
    rcases hfin_hol z with ⟨G, hG, hev⟩ | ⟨G, hG, hG0, hev⟩
    · have : f =ᶠ[𝓝 z] G := by
        filter_upwards [hev] with w hw
        rw [hf] at hw
        exact OnePoint.coe_injective hw
      exact hG.differentiableAt.congr_of_eventuallyEq this
    · exfalso
      have h0 := hev.self_of_nhds
      simp only [hG0, ite_true] at h0
      rw [hf] at h0
      exact OnePoint.coe_ne_infty _ h0
  -- the chart at `∞`
  obtain ⟨G, hG, hG0, hev⟩ : ∃ G : ℂ → ℂ, AnalyticAt ℂ G 0 ∧ G 0 = 0 ∧
      ∀ᶠ w in 𝓝 (0 : ℂ), φ (chartInf w) =
        if G w = 0 then OnePoint.infty else (((G w)⁻¹ : ℂ) : OnePoint ℂ) := by
    rcases hinf_hol with ⟨G, hG, hev⟩ | h
    · exfalso
      have h0 : φ (chartInf 0) = ((G 0 : ℂ) : OnePoint ℂ) := hev.self_of_nhds
      have hc0 : chartInf 0 = OnePoint.infty := by simp [chartInf]
      rw [hc0, hinf] at h0
      exact OnePoint.coe_ne_infty _ h0.symm
    · exact h
  -- a point with `f' ≠ 0`
  obtain ⟨z1, hz1⟩ : ∃ z1, deriv f z1 ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have := is_const_of_deriv_eq_zero hdiff hcon 0 1
    exact zero_ne_one (hfinj this)
  set q := dslope f z1 with hqdef
  have hq : Differentiable ℂ q := by
    have := (Complex.differentiableOn_dslope (c := z1) (s := Set.univ) Filter.univ_mem).mpr
      hdiff.differentiableOn
    exact fun z => (this z (Set.mem_univ z)).differentiableAt Filter.univ_mem
  have hq0 : ∀ z, q z ≠ 0 := by
    intro z
    by_cases hz : z = z1
    · rw [hz, hqdef, dslope_same]; exact hz1
    · rw [hqdef, dslope_of_ne _ hz, slope_def_field]
      exact div_ne_zero (sub_ne_zero.mpr (fun h => hz (hfinj h))) (sub_ne_zero.mpr hz)
  set L := deriv G 0 with hL
  -- `1/q → G'(0)` at `∞`
  set rt : ℂ → ℂ := fun w => (1 - z1 * w) * dslope G 0 w / (1 - f z1 * G w) with hrt
  have hrt_cont : ContinuousAt rt 0 := by
    have h1 : ContinuousAt (dslope G 0) 0 :=
      continuousAt_dslope_same.mpr hG.differentiableAt
    have h2 : ContinuousAt G 0 := hG.continuousAt
    apply ContinuousAt.div ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).mul h1)
      (continuousAt_const.sub (continuousAt_const.mul h2))
    simp [hG0]
  have hrt0 : rt 0 = L := by simp [hrt, hG0, dslope_same, hL]
  have hev' : ∀ᶠ z in Bornology.cobounded ℂ, (q z)⁻¹ = rt z⁻¹ := by
    have h1 := (Filter.tendsto_inv₀_cobounded (α := ℂ)).eventually hev
    filter_upwards [h1, Bornology.eventually_ne_cobounded z1, Bornology.eventually_ne_cobounded 0]
      with z hz hzz1 hz0
    have hw0 : z⁻¹ ≠ 0 := inv_ne_zero hz0
    have hcz : chartInf z⁻¹ = (z : OnePoint ℂ) := by simp [chartInf, hz0]
    rw [hcz, hf] at hz
    have hGw : G z⁻¹ ≠ 0 := by
      intro h; rw [if_pos h] at hz; exact OnePoint.coe_ne_infty _ hz
    rw [if_neg hGw] at hz
    have hfz : f z = (G z⁻¹)⁻¹ := OnePoint.coe_injective hz
    have hne : f z - f z1 ≠ 0 := sub_ne_zero.mpr (fun h => hzz1 (hfinj h))
    have hne' : 1 - f z1 * G z⁻¹ ≠ 0 := by
      intro h
      have h2 : f z1 = (G z⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left (by linear_combination -h)
      exact hne (by rw [hfz, h2, sub_self])
    have hA : (G z⁻¹)⁻¹ - f z1 ≠ 0 := by rw [← hfz]; exact hne
    have hzz : z - z1 ≠ 0 := sub_ne_zero.mpr hzz1
    rw [hqdef, dslope_of_ne _ hzz1, slope_def_field, hrt]
    simp only
    rw [dslope_of_ne _ hw0, slope_def_field, hG0, sub_zero, sub_zero, hfz]
    rw [inv_div]
    have e1 : (G z⁻¹)⁻¹ - f z1 = (1 - f z1 * G z⁻¹) / G z⁻¹ := by
      rw [eq_div_iff hGw, sub_mul, inv_mul_cancel₀ hGw]
    have e2 : (1 - z1 * z⁻¹) * (G z⁻¹ / z⁻¹) = (z - z1) * G z⁻¹ := by
      rw [div_inv_eq_mul]
      linear_combination (-(z1 * G z⁻¹)) * (inv_mul_cancel₀ hz0)
    rw [e1, e2, div_div_eq_mul_div]
  have htend : Filter.Tendsto (fun z => (q z)⁻¹) (Filter.cocompact ℂ) (𝓝 L) := by
    rw [← Metric.cobounded_eq_cocompact]
    refine Filter.Tendsto.congr' (Filter.EventuallyEq.symm hev') ?_
    rw [← hrt0]
    exact (hrt_cont.tendsto.mono_left nhdsWithin_le_nhds).comp
      (Filter.tendsto_inv₀_cobounded' (α := ℂ))
  have hconst : ∀ z, (q z)⁻¹ = L := fun z =>
    (hq.inv hq0).apply_eq_of_tendsto_cocompact z htend
  have hL0 : L ≠ 0 := by
    rw [← hconst 0]; exact inv_ne_zero (hq0 0)
  refine ⟨L⁻¹, f z1 - z1 * L⁻¹, inv_ne_zero hL0, fun z => ?_⟩
  rw [hf]
  congr 1
  by_cases hz : z = z1
  · rw [hz]; ring
  · have h1 := hconst z
    rw [hqdef, dslope_of_ne _ hz, slope_def_field, inv_div] at h1
    have hzz : z - z1 ≠ 0 := sub_ne_zero.mpr hz
    have hfne : f z - f z1 ≠ 0 := sub_ne_zero.mpr (fun h => hz (hfinj h))
    field_simp at h1 ⊢
    linear_combination -h1

/-! ### `HolP1FactorHol` (proved) -/

/-- **Removable singularity through a branched cover.** If `Ψ ∘ A = H` near `t₀` with `A, H`
analytic, `A` not locally constant and `Ψ` continuous at `A t₀`, then `Ψ` is analytic at `A t₀`:
off the (isolated) critical points `A` has an analytic local inverse, so `Ψ` is holomorphic on a
punctured neighbourhood of `A t₀` (open mapping), and continuity removes the singularity. -/
theorem core_removable {A H Ψ : ℂ → ℂ} {t0 : ℂ} (hA : AnalyticAt ℂ A t0) (hH : AnalyticAt ℂ H t0)
    (hnc : ¬ ∀ᶠ t in 𝓝 t0, A t = A t0) (hΨ : ContinuousAt Ψ (A t0))
    (hrel : ∀ᶠ t in 𝓝 t0, Ψ (A t) = H t) : AnalyticAt ℂ Ψ (A t0) := by
  -- critical points of `A` are isolated
  have hd : ∀ᶠ t in 𝓝[≠] t0, deriv A t ≠ 0 := by
    rcases hA.deriv.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      apply hnc
      obtain ⟨r, hr, hb⟩ := Metric.eventually_nhds_iff_ball.mp (h.and hA.eventually_analyticAt)
      filter_upwards [Metric.ball_mem_nhds t0 hr] with t ht
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball t0 r).isPreconnected
        (fun y hy => (hb y hy).2.differentiableAt.differentiableWithinAt)
        (fun y hy => (hb y hy).1) ht (Metric.mem_ball_self hr)
    · exact h
  have hopen : 𝓝 (A t0) ≤ map A (𝓝 t0) :=
    (hA.eventually_constant_or_nhds_le_map_nhds).resolve_left hnc
  -- the good set
  have hgood : ∀ᶠ t in 𝓝 t0, t ≠ t0 → AnalyticAt ℂ Ψ (A t) := by
    have h1 := eventually_nhdsWithin_iff.mp hd
    filter_upwards [h1, hrel.eventually_nhds, hH.eventually_analyticAt,
      hA.eventually_analyticAt] with t ht hrt hHt hAt hne
    have hcomp : AnalyticAt ℂ (Ψ ∘ A) t := hHt.congr (by
      filter_upwards [hrt] with t' ht'; exact ht'.symm)
    exact (analyticAt_comp_iff_of_deriv_ne_zero hAt (ht hne)).mp hcomp
  obtain ⟨V, hV, hVgood⟩ := hgood.exists_mem
  have hAV : A '' V ∈ 𝓝 (A t0) :=
    hopen (Filter.mem_map.mpr (Filter.mem_of_superset hV (Set.subset_preimage_image A V)))
  apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt _ hΨ
  rw [eventually_nhdsWithin_iff]
  filter_upwards [hAV] with s hs hs0
  obtain ⟨t, htV, rfl⟩ := hs
  have hne : t ≠ t0 := fun h => hs0 (by rw [h]; rfl)
  exact (hVgood t htV hne).differentiableAt

/-- `ℂ`-coordinate of a point of `P¹` (junk `0` at `∞`). -/
def toC (x : OnePoint ℂ) : ℂ := x.elim 0 id
/-- The coordinate of the chart at `∞` (`∞ ↦ 0`, `z ↦ 1/z`). -/
def invC (x : OnePoint ℂ) : ℂ := x.elim 0 (fun z => z⁻¹)

theorem toC_coe (z : ℂ) : toC (z : OnePoint ℂ) = z := rfl
theorem invC_coe (z : ℂ) : invC (z : OnePoint ℂ) = z⁻¹ := rfl
theorem invC_infty : invC OnePoint.infty = 0 := rfl

theorem continuousAt_toC (z : ℂ) : ContinuousAt toC (z : OnePoint ℂ) := by
  rw [← OnePoint.isOpenEmbedding_coe.continuousAt_iff]
  exact continuousAt_id

theorem continuousAt_invC_infty : ContinuousAt invC OnePoint.infty := by
  unfold ContinuousAt
  rw [invC_infty, OnePoint.nhds_infty_eq, Filter.tendsto_sup]
  constructor
  · rw [Filter.tendsto_map'_iff]
    have : invC ∘ ((↑) : ℂ → OnePoint ℂ) = fun z => z⁻¹ := rfl
    rw [this, Filter.coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded
  · rw [Filter.tendsto_pure_left]
    intro s hs
    rw [invC_infty]; exact mem_of_mem_nhds hs

theorem chartInf_invC {x : OnePoint ℂ} (hx : x ≠ ((0 : ℂ) : OnePoint ℂ)) : chartInf (invC x) = x := by
  induction x using OnePoint.rec with
  | infty => simp [chartInf, invC_infty]
  | coe z =>
    have hz : z ≠ 0 := fun h => hx (by rw [h])
    rw [invC_coe, chartInf, if_neg (inv_ne_zero hz), inv_inv]

theorem invC_chartInf (w : ℂ) : invC (chartInf w) = w := by
  by_cases hw : w = 0
  · rw [hw]; simp [chartInf, invC_infty]
  · rw [chartInf, if_neg hw, invC_coe, inv_inv]

theorem continuous_chartInf : Continuous chartInf := by
  rw [continuous_iff_continuousAt]
  intro w
  by_cases hw : w = 0
  · rw [hw]
    unfold ContinuousAt
    have : chartInf 0 = OnePoint.infty := by simp [chartInf]
    rw [this]
    exact tendsto_ite_inv continuousAt_id rfl
  · have hev : chartInf =ᶠ[𝓝 w] (fun w' => ((w'⁻¹ : ℂ) : OnePoint ℂ)) := by
      filter_upwards [isOpen_ne.mem_nhds hw] with w' hw'
      rw [chartInf, if_neg hw']
    exact (OnePoint.continuous_coe.continuousAt.comp (continuousAt_inv₀ hw)).congr hev.symm

theorem not_isOpen_singleton_P1 (x : OnePoint ℂ) : ¬ IsOpen ({x} : Set (OnePoint ℂ)) := by
  induction x using OnePoint.rec with
  | infty =>
    intro h
    rw [OnePoint.isOpen_iff_of_mem (Set.mem_singleton _)] at h
    obtain ⟨-, h2⟩ := h
    have : (OnePoint.some ⁻¹' ({OnePoint.infty} : Set (OnePoint ℂ)))ᶜ = (Set.univ : Set ℂ) := by
      ext z; simp
    rw [this] at h2
    exact noncompact_univ ℂ h2
  | coe z =>
    intro h
    have h2 : IsOpen (((↑) : ℂ → OnePoint ℂ) ⁻¹' {(z : OnePoint ℂ)}) :=
      h.preimage OnePoint.continuous_coe
    have : ((↑) : ℂ → OnePoint ℂ) ⁻¹' {(z : OnePoint ℂ)} = {z} := by
      ext w; simp
    rw [this] at h2
    exact not_isOpen_singleton z h2

/-- **`HolP1FactorHol` (proved).** -/
theorem holP1FactorHol_proof : HolP1FactorHol := by
  intro f h φ hf hh hsurj hφc hfac
  have hnc : ∃ τ τ', f τ ≠ f τ' := by
    obtain ⟨τ, hτ⟩ := hsurj ((0 : ℂ) : OnePoint ℂ)
    obtain ⟨τ', hτ'⟩ := hsurj OnePoint.infty
    exact ⟨τ, τ', by rw [hτ, hτ']; exact OnePoint.coe_ne_infty 0⟩
  have hopen : IsOpenMap f := holP1OpenMap_proof f hf hnc
  -- `f` is not locally constant anywhere
  have hfnc : ∀ τ0 : UpperHalfPlane, ¬ ∀ᶠ τ in 𝓝 τ0, f τ = f τ0 := by
    intro τ0 hc
    obtain ⟨U, hU, hUo, hτU⟩ := eventually_nhds_iff.mp hc
    have himg : f '' U = {f τ0} := by
      ext x; constructor
      · rintro ⟨τ, hτ, rfl⟩; exact hU τ hτ
      · intro hx; rw [Set.mem_singleton_iff] at hx; exact ⟨τ0, hτU, hx.symm⟩
    exact not_isOpen_singleton_P1 _ (himg ▸ hopen U hUo)
  -- the key step, in a source chart `f = C ∘ A`
  have key : ∀ (τ0 : UpperHalfPlane) (C : ℂ → OnePoint ℂ) (A : ℂ → ℂ),
      ContinuousAt C (A τ0) → AnalyticAt ℂ A τ0 →
      (∀ᶠ z in 𝓝 (τ0 : ℂ), ∀ hz : 0 < z.im, f ⟨z, hz⟩ = C (A z)) →
      IsHolC1At (fun w => φ (C w)) (A τ0) := by
    intro τ0 C A hC hA hfA
    have hAnc : ¬ ∀ᶠ t in 𝓝 (τ0 : ℂ), A t = A τ0 := by
      intro hc
      apply hfnc τ0
      rw [eventually_coe_iff]
      filter_upwards [hc, hfA] with z hz hfz hzi
      rw [hfz hzi, hz]
      have := (hfA.self_of_nhds) τ0.im_pos
      exact this.symm
    have hΦ : ContinuousAt (fun w => φ (C w)) (A τ0) := hφc.continuousAt.comp hC
    have hhA : ∀ᶠ z in 𝓝 (τ0 : ℂ), ∀ hz : 0 < z.im, h ⟨z, hz⟩ = φ (C (A z)) := by
      filter_upwards [hfA] with z hz hzi
      rw [hfac, hz hzi]
    have hh0 : h τ0 = φ (C (A τ0)) := (hhA.self_of_nhds) τ0.im_pos
    have him : ∀ᶠ z in 𝓝 (τ0 : ℂ), 0 < z.im :=
      (isOpen_lt continuous_const Complex.continuous_im).mem_nhds τ0.im_pos
    rcases hh τ0 with ⟨H, hH, hevH⟩ | ⟨H, hH, hH0, hevH⟩
    · -- finite value
      have hval : φ (C (A τ0)) = ((H τ0 : ℂ) : OnePoint ℂ) := by
        rw [← hh0]; exact (hevH.self_of_nhds) τ0.im_pos
      left
      refine ⟨fun w => toC (φ (C w)), ?_, ?_⟩
      · apply core_removable hA hH hAnc
        · show ContinuousAt (toC ∘ fun w => φ (C w)) (A τ0)
          apply ContinuousAt.comp _ hΦ
          rw [hval]; exact continuousAt_toC _
        · filter_upwards [hhA, hevH, him] with z hz hHz hzi
          show toC (φ (C (A z))) = H z
          rw [← hz hzi, hHz hzi, toC_coe]
      · have hfin : ∀ᶠ w in 𝓝 (A τ0), φ (C w) ∈ Set.range ((↑) : ℂ → OnePoint ℂ) :=
          hΦ (OnePoint.isOpen_range_coe.mem_nhds (by
            show φ (C (A (τ0 : ℂ))) ∈ _
            rw [hval]; exact ⟨_, rfl⟩))
        filter_upwards [hfin] with w hw
        obtain ⟨v, hv⟩ := hw
        rw [← hv, toC_coe]
    · -- the value `∞`
      have hval : φ (C (A τ0)) = OnePoint.infty := by
        rw [← hh0]
        have := (hevH.self_of_nhds) τ0.im_pos
        rw [this, if_pos hH0]
      right
      refine ⟨fun w => invC (φ (C w)), ?_, ?_, ?_⟩
      · apply core_removable hA hH hAnc
        · show ContinuousAt (invC ∘ fun w => φ (C w)) (A τ0)
          apply ContinuousAt.comp _ hΦ
          rw [hval]; exact continuousAt_invC_infty
        · filter_upwards [hhA, hevH, him] with z hz hHz hzi
          show invC (φ (C (A z))) = H z
          rw [← hz hzi, hHz hzi]
          exact invC_chartInf (H z)
      · show invC (φ (C (A τ0))) = 0
        rw [hval, invC_infty]
      · have hne0 : ∀ᶠ w in 𝓝 (A τ0), φ (C w) ≠ ((0 : ℂ) : OnePoint ℂ) :=
          hΦ (isOpen_ne.mem_nhds (by
            show φ (C (A (τ0 : ℂ))) ≠ _
            rw [hval]; exact (OnePoint.coe_ne_infty 0).symm))
        filter_upwards [hne0] with w hw
        exact (chartInf_invC hw).symm
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨τ0, hτ0⟩ := hsurj (z : OnePoint ℂ)
    rcases hf τ0 with ⟨G, hG, hevG⟩ | ⟨G, hG, hG0, hevG⟩
    · have hGz : G τ0 = z := by
        have := (hevG.self_of_nhds) τ0.im_pos
        rw [show (⟨(τ0 : ℂ), τ0.im_pos⟩ : UpperHalfPlane) = τ0 from rfl, hτ0] at this
        exact (OnePoint.coe_injective this).symm
      have := key τ0 (↑) G OnePoint.continuous_coe.continuousAt hG hevG
      rwa [hGz] at this
    · exfalso
      have := (hevG.self_of_nhds) τ0.im_pos
      rw [show (⟨(τ0 : ℂ), τ0.im_pos⟩ : UpperHalfPlane) = τ0 from rfl, hτ0, if_pos hG0] at this
      exact OnePoint.coe_ne_infty z this
  · obtain ⟨τ0, hτ0⟩ := hsurj OnePoint.infty
    rcases hf τ0 with ⟨G, hG, hevG⟩ | ⟨G, hG, hG0, hevG⟩
    · exfalso
      have := (hevG.self_of_nhds) τ0.im_pos
      rw [show (⟨(τ0 : ℂ), τ0.im_pos⟩ : UpperHalfPlane) = τ0 from rfl, hτ0] at this
      exact OnePoint.coe_ne_infty _ this.symm
    · have := key τ0 chartInf G continuous_chartInf.continuousAt hG hevG
      rwa [hG0] at this

/-- **`SphereFactorAffine` (proved, from Mathlib alone).** -/
theorem sphereFactorAffine_proof : SphereFactorAffine :=
  sphereFactorAffine_of holP1OpenMap_proof holP1FactorHol_proof sphereInjAffine_proof

/-- **`SphereFactorAffine` from `HolP1FactorHol` alone (proved).** -/
theorem sphereFactorAffine_of'' (hB : HolP1FactorHol) : SphereFactorAffine :=
  sphereFactorAffine_of holP1OpenMap_proof hB sphereInjAffine_proof

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.sphereFactorAffine_of
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.sphereInjAffine_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.sphereFactorAffine_of''
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.holP1FactorHol_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.sphereFactorAffine_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.holP1OpenMap_proof
