/-! ## period-glue: `SphereFactorAffine` proved (Mathlib only)

Task period-glue, 2026-11-13. `PeriodMap.SphereFactorAffine` (period-map's `part_light.lean`,
unchanged) is proved outright: `sphereFactorAffine_proof`. Hence `HauptmodulUnique` follows from
`S8Nonzero` alone (`hauptmodulUnique_of_S8`). -/

noncomputable section

namespace HSyn.G0Split.FibreQM.PeriodGlue

open Complex Filter Topology Set
open HSyn.G0Split.FibreQM

/-- The value in `ℂ` of a point of `P¹` (`∞ ↦ 0`). -/
def toC (p : OnePoint ℂ) : ℂ := p.elim 0 id

@[simp] theorem toC_coe (c : ℂ) : toC (c : OnePoint ℂ) = c := rfl

theorem coe_toC {p : OnePoint ℂ} (hp : p ≠ OnePoint.infty) : ((toC p : ℂ) : OnePoint ℂ) = p := by
  induction p using OnePoint.rec with
  | infty => exact absurd rfl hp
  | coe c => rfl

/-- The inversion `w ↦ 1/w` of `P¹`. -/
def pinv (p : OnePoint ℂ) : OnePoint ℂ :=
  p.elim ((0 : ℂ) : OnePoint ℂ) (fun c => if c = 0 then OnePoint.infty else ((c⁻¹ : ℂ) : OnePoint ℂ))

theorem pinv_coe (c : ℂ) :
    pinv (c : OnePoint ℂ) = if c = 0 then OnePoint.infty else ((c⁻¹ : ℂ) : OnePoint ℂ) := rfl

theorem pinv_infty : pinv OnePoint.infty = ((0 : ℂ) : OnePoint ℂ) := rfl

theorem pinv_pinv (p : OnePoint ℂ) : pinv (pinv p) = p := by
  induction p using OnePoint.rec with
  | infty => rw [pinv_infty, pinv_coe, if_pos rfl]
  | coe c =>
    by_cases hc : c = 0
    · subst hc; rw [pinv_coe, if_pos rfl, pinv_infty]
    · rw [pinv_coe, if_neg hc, pinv_coe, if_neg (inv_ne_zero hc), inv_inv]

theorem pinv_injective : Function.Injective pinv := fun p q h => by
  rw [← pinv_pinv p, h, pinv_pinv]

/-- At a point with a finite value, the analytic chart of `IsHolP1At`. -/
theorem hol_fin {f : UpperHalfPlane → OnePoint ℂ} {τ : UpperHalfPlane} (hf : IsHolP1At f τ)
    (hτ : f τ ≠ OnePoint.infty) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧
      ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, f ⟨z, hz⟩ = (g z : OnePoint ℂ) := by
  rcases hf with h | ⟨g, -, hg0, hg⟩
  · exact h
  · exfalso; apply hτ
    have := hg.self_of_nhds τ.im_pos
    rw [hg0, if_pos rfl] at this
    exact this

/-- At a pole, the chart `f = 1/g` of `IsHolP1At`, written with `pinv`. -/
theorem hol_pole {f : UpperHalfPlane → OnePoint ℂ} {τ : UpperHalfPlane} (hf : IsHolP1At f τ)
    (hτ : f τ = OnePoint.infty) : ∃ g : ℂ → ℂ, AnalyticAt ℂ g (τ : ℂ) ∧ g τ = 0 ∧
      ∀ᶠ z in 𝓝 (τ : ℂ), ∀ hz : 0 < z.im, f ⟨z, hz⟩ = pinv (g z : OnePoint ℂ) := by
  rcases hf with ⟨g, -, hg⟩ | ⟨g, hga, hg0, hg⟩
  · exfalso
    have := hg.self_of_nhds τ.im_pos
    rw [show (⟨(τ : ℂ), τ.im_pos⟩ : UpperHalfPlane) = τ from rfl, hτ] at this
    exact OnePoint.infty_ne_coe _ this
  · exact ⟨g, hga, hg0, hg.mono fun z hz hz' => by rw [hz hz', pinv_coe]⟩

/-- **A holomorphic map `ℍ → P¹` that is onto is nowhere locally constant (proved).** The set of
points near which `f ≡ c` is open, and closed in `ℍ` by the identity theorem in both charts. -/
theorem not_locally_const {f : UpperHalfPlane → OnePoint ℂ} (hf : ∀ τ, IsHolP1At f τ)
    (hs : Function.Surjective f) (τ₀ : UpperHalfPlane) :
    ¬ ∀ᶠ z in 𝓝 (τ₀ : ℂ), ∀ hz : 0 < z.im, f ⟨z, hz⟩ = f τ₀ := by
  intro h0
  set c := f τ₀ with hc
  set P : ℂ → Prop := fun w => ∀ hw : 0 < w.im, f ⟨w, hw⟩ = c with hP
  set u : Set ℂ := {z | ∀ᶠ w in 𝓝 z, P w} with hu
  have huo : IsOpen u := isOpen_setOfPred_eventually_nhds
  have hcl : closure u ∩ PeriodMap.U ⊆ u := by
    rintro z₀ ⟨hz₀c, hz₀⟩
    by_contra hnot
    have hfreq : ∃ᶠ w in 𝓝[≠] z₀, P w := by
      rw [frequently_nhdsWithin_iff]
      refine (mem_closure_iff_frequently.mp hz₀c).mono fun x hx => ⟨hx.self_of_nhds, ?_⟩
      rintro rfl; exact hnot hx
    have him : ∀ᶠ w in 𝓝[≠] z₀, 0 < w.im :=
      nhdsWithin_le_nhds ((PeriodMap.isOpen_U).mem_nhds hz₀)
    set τ₁ : UpperHalfPlane := ⟨z₀, hz₀⟩
    rcases hf τ₁ with ⟨g, hga, hg⟩ | ⟨g, hga, hg0, hg⟩
    · have hg' : ∀ᶠ w in 𝓝[≠] z₀, ∀ hw : 0 < w.im, f ⟨w, hw⟩ = (g w : OnePoint ℂ) :=
        nhdsWithin_le_nhds hg
      by_cases hci : c = OnePoint.infty
      · obtain ⟨w, hPw, hgw, hw⟩ := (hfreq.and_eventually (hg'.and him)).exists
        exact OnePoint.coe_ne_infty _ ((hgw hw).symm.trans ((hPw hw).trans hci))
      · obtain ⟨c', hc'⟩ : ∃ c' : ℂ, c = (c' : OnePoint ℂ) := ⟨toC c, (coe_toC hci).symm⟩
        have hfr : ∃ᶠ w in 𝓝[≠] z₀, g w = c' := by
          refine (hfreq.and_eventually (hg'.and him)).mono fun w ⟨hPw, hgw, hw⟩ => ?_
          exact OnePoint.coe_injective ((hgw hw).symm.trans ((hPw hw).trans hc'))
        have hev := (hga.frequently_eq_iff_eventually_eq analyticAt_const).mp hfr
        apply hnot
        show ∀ᶠ w in 𝓝 z₀, P w
        filter_upwards [hev, hg] with w hw1 hw2 hw
        rw [hw2 hw, hw1, hc']
    · have hg' : ∀ᶠ w in 𝓝[≠] z₀, ∀ hw : 0 < w.im, f ⟨w, hw⟩ =
          if g w = 0 then OnePoint.infty else (((g w)⁻¹ : ℂ) : OnePoint ℂ) := nhdsWithin_le_nhds hg
      by_cases hci : c = OnePoint.infty
      · have hfr : ∃ᶠ w in 𝓝[≠] z₀, g w = 0 := by
          refine (hfreq.and_eventually (hg'.and him)).mono fun w ⟨hPw, hgw, hw⟩ => ?_
          by_contra hne
          have := (hgw hw).symm.trans ((hPw hw).trans hci)
          rw [if_neg hne] at this
          exact OnePoint.coe_ne_infty _ this
        have hev := hga.frequently_zero_iff_eventually_zero.mp hfr
        apply hnot
        show ∀ᶠ w in 𝓝 z₀, P w
        filter_upwards [hev, hg] with w hw1 hw2 hw
        rw [hw2 hw, if_pos hw1, hci]
      · obtain ⟨c', hc'⟩ : ∃ c' : ℂ, c = (c' : OnePoint ℂ) := ⟨toC c, (coe_toC hci).symm⟩
        have hfr : ∃ᶠ w in 𝓝[≠] z₀, g w ≠ 0 ∧ (g w)⁻¹ = c' := by
          refine (hfreq.and_eventually (hg'.and him)).mono fun w ⟨hPw, hgw, hw⟩ => ?_
          have := (hgw hw).symm.trans ((hPw hw).trans hc')
          by_cases hne : g w = 0
          · rw [if_pos hne] at this; exact absurd this (OnePoint.infty_ne_coe _)
          · rw [if_neg hne] at this; exact ⟨hne, OnePoint.coe_injective this⟩
        obtain ⟨w, hw0, hwc⟩ := hfr.exists
        have hc' : c' ≠ 0 := by rw [← hwc]; exact inv_ne_zero hw0
        have hfr' : ∃ᶠ w in 𝓝[≠] z₀, g w = c'⁻¹ :=
          hfr.mono fun w ⟨_, hw⟩ => by rw [← hw, inv_inv]
        have hev := (hga.frequently_eq_iff_eventually_eq analyticAt_const).mp hfr'
        have : g z₀ = c'⁻¹ := hev.self_of_nhds
        rw [show z₀ = (τ₁ : ℂ) from rfl, hg0] at this
        exact inv_ne_zero hc' this.symm
  have hsub := PeriodMap.isPreconnected_U.subset_of_closure_inter_subset huo
    ⟨τ₀, τ₀.im_pos, h0⟩ hcl
  have hall : ∀ τ : UpperHalfPlane, f τ = c := fun τ =>
    (hsub τ.im_pos).self_of_nhds τ.im_pos
  by_cases hci : c = OnePoint.infty
  · obtain ⟨τ, hτ⟩ := hs ((0 : ℂ) : OnePoint ℂ)
    exact OnePoint.coe_ne_infty _ (hτ.symm.trans ((hall τ).trans hci))
  · obtain ⟨τ, hτ⟩ := hs OnePoint.infty
    exact hci (hτ.symm.trans (hall τ)).symm

/-- `f` extended by `∞` off `ℍ`. -/
def extH (f : UpperHalfPlane → OnePoint ℂ) (z : ℂ) : OnePoint ℂ :=
  if hz : 0 < z.im then f ⟨z, hz⟩ else OnePoint.infty

theorem extH_of {f : UpperHalfPlane → OnePoint ℂ} {z : ℂ} (hz : 0 < z.im) :
    extH f z = f ⟨z, hz⟩ := dif_pos hz

/-- **`SphereFactorAffine` holds (proved).** `φ(f(τ)) := h(τ)` is a well-defined injection of `P¹`
fixing `∞`. Its finite part `ψ` is entire (`descent` in the chart of `f` at finite values), its
chart `χ(w) = 1/ψ(1/w)` at `∞` is analytic and injective near `0` (`descent` in the pole charts),
so `χ'(0) ≠ 0`, `ψ` has linear growth and is affine (`affine_of_growth`). -/
theorem sphereFactorAffine_proof : PeriodMap.SphereFactorAffine := by
  intro f h hf hh hsurj hfib ⟨τi, hfi, hhi⟩
  -- the induced map `φ` of `P¹`
  set s := Function.surjInv hsurj with hsdef
  have hfs : ∀ c, f (s c) = c := Function.surjInv_eq hsurj
  set φ : OnePoint ℂ → OnePoint ℂ := fun c => h (s c) with hφdef
  have hφ : ∀ τ, h τ = φ (f τ) := fun τ => ((hfib _ _).mp (hfs (f τ))).symm
  have hφinj : Function.Injective φ := fun c c' hcc => by
    rw [← hfs c, ← hfs c']; exact (hfib _ _).mpr hcc
  have hφi : φ OnePoint.infty = OnePoint.infty := by
    have := hφ τi; rw [hfi, hhi] at this; exact this.symm
  have hφfin : ∀ c : ℂ, φ (c : OnePoint ℂ) ≠ OnePoint.infty := fun c hc =>
    OnePoint.coe_ne_infty c (hφinj (hc.trans hφi.symm))
  set ψ : ℂ → ℂ := fun c => toC (φ c) with hψdef
  have hψφ : ∀ c : ℂ, ((ψ c : ℂ) : OnePoint ℂ) = φ c := fun c => coe_toC (hφfin c)
  have hnlc := not_locally_const hf hsurj
  -- Step 1: `ψ` is entire
  have hψd : Differentiable ℂ ψ := by
    set O : Set ℂ := {z | ∃ hz : 0 < z.im, f ⟨z, hz⟩ ≠ OnePoint.infty} with hOdef
    set F : ℂ → ℂ := fun z => toC (extH f z) with hFdef
    set H : ℂ → ℂ := fun z => toC (extH h z) with hHdef
    have hrep : ∀ z ∈ O, ∃ hz : 0 < z.im, ∃ g gh : ℂ → ℂ, AnalyticAt ℂ g z ∧ AnalyticAt ℂ gh z ∧
        (∀ᶠ w in 𝓝 z, ∀ hw : 0 < w.im, f ⟨w, hw⟩ = (g w : OnePoint ℂ)) ∧
        (∀ᶠ w in 𝓝 z, ∀ hw : 0 < w.im, h ⟨w, hw⟩ = (gh w : OnePoint ℂ)) := by
      rintro z ⟨hz, hfz⟩
      obtain ⟨g, hga, hg⟩ := hol_fin (hf ⟨z, hz⟩) hfz
      have hhz : h ⟨z, hz⟩ ≠ OnePoint.infty := by
        rw [hφ, ← coe_toC hfz]; exact hφfin _
      obtain ⟨gh, hgha, hgh⟩ := hol_fin (hh ⟨z, hz⟩) hhz
      exact ⟨hz, g, gh, hga, hgha, hg, hgh⟩
    have himev : ∀ z : ℂ, 0 < z.im → ∀ᶠ w in 𝓝 z, 0 < w.im := fun z hz =>
      PeriodMap.isOpen_U.mem_nhds hz
    have hFeq : ∀ z ∈ O, ∃ g : ℂ → ℂ, AnalyticAt ℂ g z ∧ F =ᶠ[𝓝 z] g ∧
        ∀ᶠ w in 𝓝 z, ∀ hw : 0 < w.im, f ⟨w, hw⟩ = (g w : OnePoint ℂ) := by
      intro z hzO
      obtain ⟨hz, g, -, hga, -, hg, -⟩ := hrep z hzO
      refine ⟨g, hga, ?_, hg⟩
      filter_upwards [hg, himev z hz] with w hw1 hw2
      simp only [hFdef, extH_of hw2, hw1 hw2, toC_coe]
    have hOo : IsOpen O := by
      refine isOpen_iff_mem_nhds.mpr fun z hzO => ?_
      obtain ⟨hz, g, -, -, -, hg, -⟩ := hrep z hzO
      filter_upwards [hg, himev z hz] with w hw1 hw2
      exact ⟨hw2, by rw [hw1 hw2]; exact OnePoint.coe_ne_infty _⟩
    have hFa : AnalyticOnNhd ℂ F O := fun z hzO => by
      obtain ⟨g, hga, hFg, -⟩ := hFeq z hzO
      exact hga.congr hFg.symm
    have hHa : AnalyticOnNhd ℂ H O := fun z hzO => by
      obtain ⟨hz, -, gh, -, hgha, -, hgh⟩ := hrep z hzO
      refine hgha.congr ?_
      filter_upwards [hgh, himev z hz] with w hw1 hw2
      simp only [hHdef, extH_of hw2, hw1 hw2, toC_coe]
    have hnc : ∀ z ∈ O, ¬ ∀ᶠ w in 𝓝 z, F w = F z := by
      intro z hzO hc
      obtain ⟨g, -, hFg, hg⟩ := hFeq z hzO
      obtain ⟨hz, -⟩ := hzO
      apply hnlc ⟨z, hz⟩
      filter_upwards [hc, hFg, hg, himev z hz] with w hw1 hw2 hw3 hw4 hw
      rw [hw3 hw, ← hw2, hw1, hFg.self_of_nhds, ← (hg.self_of_nhds hz)]
    have hGF : ∀ z ∈ O, ψ (F z) = H z := by
      rintro z ⟨hz, hfz⟩
      simp only [hψdef, hFdef, hHdef, extH_of hz, coe_toC hfz, ← hφ]
    obtain ⟨-, hd⟩ := descent hOo hFa hHa hnc hGF
    have himg : F '' O = univ := by
      refine eq_univ_of_forall fun c => ⟨s c, ⟨(s c).im_pos, ?_⟩, ?_⟩
      · rw [show (⟨((s c : UpperHalfPlane) : ℂ), (s c).im_pos⟩ : UpperHalfPlane) = s c from rfl,
          hfs]
        exact OnePoint.coe_ne_infty _
      · simp only [hFdef, extH_of (s c).im_pos]
        rw [show (⟨((s c : UpperHalfPlane) : ℂ), (s c).im_pos⟩ : UpperHalfPlane) = s c from rfl,
          hfs, toC_coe]
    rw [himg] at hd
    exact differentiableOn_univ.mp hd
  -- Step 2: the chart `χ` at `∞`
  obtain ⟨gf, hgfa, hgf0, hgf⟩ := hol_pole (hf τi) hfi
  obtain ⟨gh, hgha, hgh0, hgh⟩ := hol_pole (hh τi) hhi
  set χ : ℂ → ℂ := fun w => toC (pinv (φ (pinv (w : OnePoint ℂ)))) with hχdef
  set Q : ℂ → Prop := fun z => (0 < z.im ∧ AnalyticAt ℂ gf z ∧ AnalyticAt ℂ gh z) ∧
    (∀ hz : 0 < z.im, f ⟨z, hz⟩ = pinv (gf z : OnePoint ℂ)) ∧
    (∀ hz : 0 < z.im, h ⟨z, hz⟩ = pinv (gh z : OnePoint ℂ)) with hQ
  have hQev : ∀ᶠ z in 𝓝 (τi : ℂ), Q z := by
    filter_upwards [PeriodMap.isOpen_U.mem_nhds τi.im_pos, hgfa.eventually_analyticAt,
      hgha.eventually_analyticAt, hgf, hgh] with z h1 h2 h3 h4 h5 using ⟨⟨h1, h2, h3⟩, h4, h5⟩
  set O' : Set ℂ := interior {z | Q z} with hO'def
  have hO'o : IsOpen O' := isOpen_interior
  have hτO' : (τi : ℂ) ∈ O' := mem_interior_iff_mem_nhds.mpr hQev
  have hQO' : ∀ z ∈ O', Q z := fun z hz => interior_subset (s := {z | Q z}) hz
  have hχgf : ∀ z ∈ O', χ (gf z) = gh z := by
    intro z hz
    obtain ⟨⟨hzi, -, -⟩, h1, h2⟩ := hQO' z hz
    simp only [hχdef, ← h1 hzi, ← hφ, h2 hzi, pinv_pinv, toC_coe]
  have hnc' : ∀ z ∈ O', ¬ ∀ᶠ w in 𝓝 z, gf w = gf z := by
    intro z hz hc
    obtain ⟨⟨hzi, -, -⟩, h1, -⟩ := hQO' z hz
    apply hnlc ⟨z, hzi⟩
    filter_upwards [hc, hO'o.mem_nhds hz] with w hw1 hw2 hw
    rw [(hQO' w hw2).2.1 hw, hw1, ← h1 hzi]
  obtain ⟨hVo, hχd⟩ := descent hO'o (fun z hz => (hQO' z hz).1.2.1)
    (fun z hz => (hQO' z hz).1.2.2) hnc' hχgf
  set V := gf '' O' with hVdef
  have h0V : (0 : ℂ) ∈ V := ⟨τi, hτO', hgf0⟩
  have hχinj : InjOn χ V := by
    rintro _ ⟨z, hz, rfl⟩ _ ⟨z', hz', rfl⟩ hzz
    rw [hχgf z hz, hχgf z' hz'] at hzz
    obtain ⟨⟨hzi, -, -⟩, h1, h2⟩ := hQO' z hz
    obtain ⟨⟨hzi', -, -⟩, h1', h2'⟩ := hQO' z' hz'
    have hhz : h ⟨z, hzi⟩ = h ⟨z', hzi'⟩ := by rw [h2, h2', hzz]
    have hfz := (hfib _ _).mpr hhz
    rw [h1, h1'] at hfz
    exact OnePoint.coe_injective (pinv_injective hfz)
  have hχ0 : χ 0 = 0 := by
    have := hχgf _ hτO'; rw [hgf0, hgh0] at this; exact this
  have hd0 : deriv χ 0 ≠ 0 :=
    deriv_ne_zero_of_injOn (hVo.mem_nhds h0V) (hχd.analyticOnNhd hVo) hχinj
  have hχψ : ∀ w ∈ V, w ≠ 0 → ψ w⁻¹ ≠ 0 ∧ χ w = (ψ w⁻¹)⁻¹ := by
    intro w hw hw0
    have hχw : χ w = toC (pinv (ψ w⁻¹ : OnePoint ℂ)) := by
      simp only [hχdef, pinv_coe, if_neg hw0, hψφ]
    by_cases hψ0 : ψ w⁻¹ = 0
    · exfalso
      rw [hψ0, pinv_coe, if_pos rfl] at hχw
      exact hw0 (hχinj hw h0V (hχw.trans hχ0.symm))
    · refine ⟨hψ0, ?_⟩
      rw [hχw, pinv_coe, if_neg hψ0, toC_coe]
  -- Step 3: linear growth of `ψ`
  set d := deriv χ 0 with hd
  have hder : HasDerivAt χ d 0 :=
    ((hχd 0 h0V).differentiableAt (hVo.mem_nhds h0V)).hasDerivAt
  have hsl := hasDerivAt_iff_tendsto_slope.mp hder
  have hdpos : 0 < ‖d‖ := norm_pos_iff.mpr hd0
  have hev : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ V ∧ ‖slope χ 0 w - d‖ < ‖d‖ / 2 :=
    (show ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∈ V from nhdsWithin_le_nhds (hVo.mem_nhds h0V)).and
      ((hsl.eventually (Metric.ball_mem_nhds d (half_pos hdpos))).mono fun w hw => by
        rwa [dist_eq_norm] at hw)
  rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hev
  obtain ⟨ε, hε, hεP⟩ := hev
  have hlow : ∀ w : ℂ, w ≠ 0 → ‖w‖ < ε → w ∈ V ∧ ‖d‖ / 2 * ‖w‖ ≤ ‖χ w‖ := by
    intro w hw0 hwε
    obtain ⟨hwV, hws⟩ := hεP (by simpa using hwε) hw0
    refine ⟨hwV, ?_⟩
    rw [slope_def_field, hχ0, sub_zero, sub_zero] at hws
    have hwpos : 0 < ‖w‖ := norm_pos_iff.mpr hw0
    have h1 : ‖d‖ - ‖d‖ / 2 ≤ ‖χ w / w‖ := by
      have := norm_sub_norm_le d (χ w / w)
      rw [norm_sub_rev] at this
      linarith
    rw [norm_div, le_div_iff₀ hwpos] at h1
    linarith
  obtain ⟨a, b, hab⟩ := affine_of_growth hψd (C := 2 / ‖d‖) (R := 2 / ε) (by positivity)
    (fun z hz => by
      have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by positivity) hz
      have hz0 : z ≠ 0 := norm_pos_iff.mp hzpos
      have hwε : ‖z⁻¹‖ < ε := by
        rw [norm_inv]
        have : 2 / ε ≤ ‖z‖ := hz
        rw [div_le_iff₀ hε] at this
        rw [inv_lt_iff_one_lt_mul₀ hzpos]
        nlinarith
      obtain ⟨hwV, hwl⟩ := hlow z⁻¹ (inv_ne_zero hz0) hwε
      obtain ⟨-, hχw⟩ := hχψ z⁻¹ hwV (inv_ne_zero hz0)
      rw [inv_inv] at hχw
      rw [hχw, norm_inv, norm_inv] at hwl
      have hψpos : 0 < ‖ψ z‖ := by
        rcases (norm_nonneg (ψ z)).lt_or_eq with h' | h'
        · exact h'
        · rw [← h', inv_zero] at hwl
          have : 0 < ‖d‖ / 2 * ‖z‖⁻¹ := by positivity
          linarith
      rw [le_inv_comm₀ (by positivity) hψpos] at hwl
      calc ‖ψ z‖ ≤ (‖d‖ / 2 * ‖z‖⁻¹)⁻¹ := hwl
        _ = 2 / ‖d‖ * ‖z‖ := by field_simp)
  -- Step 4: conclusion
  have ha : a ≠ 0 := by
    rintro rfl
    have h01 : φ ((0 : ℂ) : OnePoint ℂ) = φ ((1 : ℂ) : OnePoint ℂ) := by
      rw [← hψφ, ← hψφ, hab, hab]; simp
    exact one_ne_zero (OnePoint.coe_injective (hφinj h01)).symm
  refine ⟨a, b, ha, fun τ => ?_⟩
  rw [hφ τ]
  induction f τ using OnePoint.rec with
  | infty => rw [hφi]; rfl
  | coe c => rw [← hψφ, hab]; rfl

/-- **`HauptmodulUnique` from `S8Nonzero` alone (proved).** -/
theorem hauptmodulUnique_of_S8 (hS : PeriodMap.S8Nonzero) : HauptmodulUnique :=
  PeriodMap.hauptmodulUnique_of' hS sphereFactorAffine_proof

end HSyn.G0Split.FibreQM.PeriodGlue

end

#print axioms HSyn.G0Split.FibreQM.PeriodGlue.descent
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.deriv_ne_zero_of_injOn
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.affine_of_growth
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.sphereFactorAffine_proof
#print axioms HSyn.G0Split.FibreQM.PeriodGlue.hauptmodulUnique_of_S8
