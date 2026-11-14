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

end HSyn.G0Split.FibreQM.PeriodGlue

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.sphereFactorAffine_of
