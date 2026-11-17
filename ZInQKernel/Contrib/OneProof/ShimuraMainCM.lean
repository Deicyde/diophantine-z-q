import ZInQKernel.Contrib.OneProof.RingClassLattice
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_isUniformization_toPoint
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_discriminant_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_PeriodPair_exists_variableChange_smul_weierstrassCurve_eq

/-!
# hcm-dict: `T5Glue.ShimuraMainCM` from Shimura's Theorem 5.4 in its printed form

Task hcm-dict (2026-11-16). Report: `docs/research/hcm-dict.md`; log: `scratch/hcm-dict/log.md`.

The frozenTarget hypothesis `hCM : T5Glue.ShimuraMainCM` (`Contrib/OneProof/RingClassLattice.lean`) states the main
theorem of complex multiplication in Weierstrass coordinates (`℘_P`, `℘'_P` and a scaling `μ`). This file states the
theorem as printed (Shimura 1971, Thm. 5.4: for an analytic isomorphism `ξ : ℂ/𝔞 → E(ℂ)` there is an analytic
isomorphism `ξ' : ℂ/s⁻¹𝔞 → E^σ(ℂ)` with `ξ(u)^σ = ξ'(s⁻¹u)`), as `ZInQ.Contrib.HCMDict.ShimuraThm54`, over Mathlib's
Weierstrass curves and points, and proves

* `toPoint_isAnalyticUnif`: the Weierstrass map `z ↦ (℘_L(z), ℘'_L(z)/2)` is an analytic isomorphism
  `ℂ/L → E_L(ℂ)` (from the vendored FLT theorem `PeriodPair.isUniformization_toPoint`);
* `exists_lattice_eq`: every short Weierstrass model over `ℂ` is `L.weierstrassCurve` for a period pair `L`;
* `exists_local_lift`, `exists_eq_toPoint_mul`: an analytic isomorphism `ξ : ℂ/Λ → E_{L₀}(ℂ)` is `z ↦ ξ_{L₀}(αz)`
  (a local holomorphic lift through `℘_{L₀}`, additivity near `0` by discreteness of `L₀`, constant derivative);
* `isAnalyticUnif_iff`: the dictionary, both directions: the analytic isomorphisms `ℂ/L → E_{L₀}(ℂ)` are exactly
  `z ↦ ξ_{L₀}(αz)` with `L₀ = αL`;
* `eq_scaled_of_isAnalyticUnif`: every analytic isomorphism `ℂ/L → E(ℂ)` of a short model `E` is
  `z ↦ (μ²℘_L(z), μ³℘'_L(z)/2)`, with `E : y² = x³ − μ⁴g₂(L)/4·x − μ⁶g₃(L)/4`;
* `shimuraMainCM_of_printed : ShimuraThm54 → T5Glue.ShimuraMainCM`.

No `sorry`, no `axiom`; only `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

open Complex Topology Filter
open scoped PeriodPair

namespace ZInQ.Contrib.HCMDict

open WeierstrassCurve.Affine (Point)

/-! ## §1. Definitions -/

/-- `P ↦ P^σ` on the points of a Weierstrass curve over `ℂ`: `(x, y) ↦ (σx, σy)`, `O ↦ O`. -/
def conjPt (σ : ℂ →+* ℂ) {W : WeierstrassCurve ℂ} : W.toAffine.Point → (W.map σ).toAffine.Point
  | .zero => .zero
  | .some x y h => .some (σ x) (σ y) ((W.toAffine.map_nonsingular σ.injective x y).2 h)

/-- **Analytic isomorphism `ℂ/Λ → E(ℂ)`**, read as a map `ξ : ℂ → E(ℂ)`: a group homomorphism, onto,
with kernel exactly `Λ` (so `ξ` induces a group isomorphism `ℂ/Λ ≅ E(ℂ)`), and holomorphic in the affine
coordinates at every point not sent to `O`. -/
def IsAnalyticUnif (W : WeierstrassCurve ℂ) (Λ : Set ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  (∀ z w, ξ (z + w) = ξ z + ξ w) ∧ Function.Surjective ξ ∧ (∀ z, ξ z = 0 ↔ z ∈ Λ) ∧
    ∀ z₀, ξ z₀ ≠ 0 → ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ X Y : ℂ → ℂ,
      DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, ∃ h : W.toAffine.Nonsingular (X z) (Y z), ξ z = .some (X z) (Y z) h

/-! ## §2. The Weierstrass uniformization is an analytic isomorphism -/

theorem toPoint_isAnalyticUnif (L : PeriodPair) :
    IsAnalyticUnif L.weierstrassCurve L.lattice (L.toPoint L.discriminant_ne_zero) := by
  have hU := L.isUniformization_toPoint L.discriminant_ne_zero
  refine ⟨hU.1, hU.2.1, fun z => ⟨hU.2.2 z, fun hz => L.toPoint_of_mem _ hz⟩, fun z₀ hz₀ => ?_⟩
  have hz₀' : z₀ ∉ L.lattice := fun h => hz₀ (L.toPoint_of_mem _ h)
  refine ⟨(L.lattice : Set ℂ)ᶜ, L.isClosed_lattice.isOpen_compl, hz₀', ℘[L], fun z => ℘'[L] z / 2,
    L.analyticOnNhd_weierstrassP.differentiableOn,
    (L.analyticOnNhd_derivWeierstrassP.differentiableOn).div_const 2, fun z hz => ?_⟩
  exact ⟨_, L.toPoint_of_notMem _ hz⟩

/-! ## §3. Scaling lattices; every short Weierstrass model over `ℂ` is `L.weierstrassCurve` -/

theorem scale_isScale (L : PeriodPair) (α : ℂˣ) : T5Glue.IsScale (L.scale α) L α := by
  refine ⟨α.ne_zero, ?_⟩
  ext x
  simp only [SetLike.mem_coe, Set.mem_smul_set, PeriodPair.mem_lattice, PeriodPair.scale_ω₁,
    PeriodPair.scale_ω₂, smul_eq_mul]
  constructor
  · rintro ⟨m, n, rfl⟩
    exact ⟨m * L.ω₁ + n * L.ω₂, ⟨m, n, rfl⟩, by ring⟩
  · rintro ⟨y, ⟨m, n, rfl⟩, rfl⟩
    exact ⟨m, n, by ring⟩

theorem exists_lattice_eq (W : WeierstrassCurve ℂ) [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) : ∃ L : PeriodPair, L.weierstrassCurve = W := by
  obtain ⟨L, C, hC⟩ := PeriodPair.exists_variableChange_smul_weierstrassCurve_eq W
  have e₁ := congrArg WeierstrassCurve.a₁ hC
  have e₂ := congrArg WeierstrassCurve.a₂ hC
  have e₃ := congrArg WeierstrassCurve.a₃ hC
  have e₄ := congrArg WeierstrassCurve.a₄ hC
  have e₆ := congrArg WeierstrassCurve.a₆ hC
  simp only [WeierstrassCurve.variableChange_a₁, WeierstrassCurve.variableChange_a₂,
    WeierstrassCurve.variableChange_a₃, WeierstrassCurve.variableChange_a₄,
    WeierstrassCurve.variableChange_a₆, PeriodPair.weierstrassCurve_a₁,
    PeriodPair.weierstrassCurve_a₂, PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄,
    PeriodPair.weierstrassCurve_a₆, h₁, h₂, h₃] at e₁ e₂ e₃ e₄ e₆
  have hu : ((C.u⁻¹ : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hs : C.s = 0 := by
    have := (mul_eq_zero.1 e₁).resolve_left hu; linear_combination this / 2
  have hr : C.r = 0 := by
    have := (mul_eq_zero.1 e₂).resolve_left (pow_ne_zero _ hu); rw [hs] at this
    linear_combination this / 3
  have ht : C.t = 0 := by
    have := (mul_eq_zero.1 e₃).resolve_left (pow_ne_zero _ hu); rw [hr] at this
    linear_combination this / 2
  simp only [hs, hr, ht] at e₄ e₆
  refine ⟨L.scale C.u, ?_⟩
  have hsc := scale_isScale L C.u
  ext
  · simp [h₁]
  · simp [h₂]
  · simp [h₃]
  · rw [PeriodPair.weierstrassCurve_a₄, hsc.g₂, ← e₄]
    simp only [Units.val_inv_eq_inv_val]; ring
  · rw [PeriodPair.weierstrassCurve_a₆, hsc.g₃, ← e₆]
    simp only [Units.val_inv_eq_inv_val]; ring

/-! ## §4. Local holomorphic lift through `ℂ → E(ℂ)`

Adapted from the vendored FLT proof `ModularCurve.kw_surgehgf4_hH2d_betweenCurvesCocountableHoloLift_of_affineHoloCoords`
(anthropics/fermats-last-theorem, Apache-2.0; `Vendor/AnthropicFLT`): the local inverse of `℘` composed with the
`x`-coordinate, the sign of `y` fixed by continuity. -/

theorem omega_div_four_notMem (L : PeriodPair) : L.ω₁ / 4 ∉ L.lattice := by
  intro h
  apply L.ω₁_div_two_notMem_lattice
  have : L.ω₁ / 2 = L.ω₁ / 4 + L.ω₁ / 4 := by ring
  rw [this]; exact add_mem h h

theorem derivWeierstrassP_omega_div_four_ne (L : PeriodPair) : ℘'[L] (L.ω₁ / 4) ≠ 0 := by
  intro h0
  have hU := L.isUniformization_toPoint L.discriminant_ne_zero
  have hw := omega_div_four_notMem L
  have h2 : L.toPoint L.discriminant_ne_zero (L.ω₁ / 4 + L.ω₁ / 4) = 0 := by
    rw [hU.1, L.toPoint_of_notMem _ hw]
    classical
    apply Point.add_self_of_Y_eq
    simp [WeierstrassCurve.Affine.negY, h0]
  apply L.ω₁_div_two_notMem_lattice
  have : L.ω₁ / 2 = L.ω₁ / 4 + L.ω₁ / 4 := by ring
  rw [this]; exact hU.2.2 _ h2

theorem exists_local_lift (L₀ : PeriodPair) {Λ : Set ℂ}
    (ξ : ℂ → L₀.weierstrassCurve.toAffine.Point) (hξ : IsAnalyticUnif L₀.weierstrassCurve Λ ξ) :
    ∃ z₁ : ℂ, ∃ r > 0, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball z₁ r) ∧
      ∀ z ∈ Metric.ball z₁ r, L₀.toPoint L₀.discriminant_ne_zero (G z) = ξ z := by
  set w₀ := L₀.ω₁ / 4 with hw₀def
  have hw₀Λ : w₀ ∉ L₀.lattice := omega_div_four_notMem L₀
  have hder' : ℘'[L₀] w₀ ≠ 0 := derivWeierstrassP_omega_div_four_ne L₀
  obtain ⟨z₀, hz₀⟩ := hξ.2.1 (L₀.toPoint L₀.discriminant_ne_zero w₀)
  have hξz₀ : ξ z₀ ≠ 0 := by
    rw [hz₀, L₀.toPoint_of_notMem _ hw₀Λ]; exact Point.some_ne_zero _
  obtain ⟨U, hUo, hz₀U, X, Y, hXd, hYd, hcoord⟩ := hξ.2.2.2 z₀ hξz₀
  obtain ⟨hnsz₀, hcoord₀⟩ := hcoord z₀ hz₀U
  have hPw₀ : ℘[L₀] w₀ = X z₀ ∧ ℘'[L₀] w₀ / 2 = Y z₀ := by
    have h := hz₀
    rw [hcoord₀, L₀.toPoint_of_notMem _ hw₀Λ, Point.some.injEq] at h
    exact ⟨h.1.symm, h.2.symm⟩
  have hYz₀ : Y z₀ ≠ 0 := by
    rw [← hPw₀.2]; exact div_ne_zero hder' two_ne_zero
  have hU : U ∈ 𝓝 z₀ := hUo.mem_nhds hz₀U
  have hder : deriv ℘[L₀] w₀ ≠ 0 := by
    simp only [PeriodPair.deriv_weierstrassP]; exact hder'
  have hPa : AnalyticAt ℂ ℘[L₀] w₀ := L₀.analyticOnNhd_weierstrassP w₀ hw₀Λ
  set ψ := hPa.hasStrictDerivAt.localInverse ℘[L₀] (deriv ℘[L₀] w₀) w₀ hder with hψdef
  have hψa : AnalyticAt ℂ ψ (X z₀) := hPw₀.1 ▸ hPa.analyticAt_localInverse hder
  have hψw₀ : ψ (X z₀) = w₀ :=
    hPw₀.1 ▸ HasStrictFDerivAt.localInverse_apply_image _
  set G := ψ ∘ X with hGdef
  have hXcont : ContinuousAt X z₀ := (hXd.differentiableAt hU).continuousAt
  have hGcont : ContinuousAt G z₀ := hψa.continuousAt.comp hXcont
  have hGz₀ : G z₀ = w₀ := hψw₀
  have hevΛ : ∀ᶠ z in 𝓝 z₀, G z ∉ L₀.lattice :=
    hGcont.eventually (L₀.isClosed_lattice.isOpen_compl.mem_nhds (hGz₀ ▸ hw₀Λ))
  have hevR : ∀ᶠ z in 𝓝 z₀, ℘[L₀] (G z) = X z := by
    have h := hPw₀.1 ▸ hPa.hasStrictDerivAt.eventually_right_inverse hder
    exact hXcont.eventually h
  have hevψd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ ψ (X z) :=
    hXcont.eventually
      ((AnalyticAt.eventually_analyticAt hψa).mono fun _ hy => hy.differentiableAt)
  have hevXd : ∀ᶠ z in 𝓝 z₀, DifferentiableAt ℂ X z :=
    eventually_of_mem hU fun z hz => hXd.differentiableAt (hUo.mem_nhds hz)
  have hevU : ∀ᶠ z in 𝓝 z₀, z ∈ U := hU
  have hevSgn : ∀ᶠ z in 𝓝 z₀, ℘'[L₀] (G z) / 2 + Y z ≠ 0 := by
    have hP'cont : ContinuousAt ℘'[L₀] (G z₀) := by
      rw [hGz₀]; exact (L₀.analyticOnNhd_derivWeierstrassP w₀ hw₀Λ).continuousAt
    have hcont : ContinuousAt (fun z => ℘'[L₀] (G z) / 2 + Y z) z₀ :=
      ((hP'cont.comp hGcont).div_const 2).add (hYd.differentiableAt hU).continuousAt
    refine hcont.eventually (isOpen_ne.mem_nhds ?_)
    show ℘'[L₀] (G z₀) / 2 + Y z₀ ≠ 0
    rw [hGz₀, hPw₀.2, ← two_mul]; exact mul_ne_zero two_ne_zero hYz₀
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    (((((hevΛ.and hevR).and hevψd).and hevXd).and hevU).and hevSgn)
  refine ⟨z₀, r, hr, G, fun z hz => ?_, fun z hz => ?_⟩
  · obtain ⟨⟨⟨⟨⟨-, -⟩, hψd⟩, hXdz⟩, -⟩, -⟩ := hball z hz
    exact (hψd.comp z hXdz).differentiableWithinAt
  · obtain ⟨⟨⟨⟨⟨hGzΛ, hPGz⟩, -⟩, -⟩, hzU⟩, hsgn⟩ := hball z hz
    obtain ⟨hnsz, hcoordz⟩ := hcoord z hzU
    have hPGy : ℘'[L₀] (G z) / 2 = Y z := by
      have h1 : (℘'[L₀] (G z) / 2) ^ 2 = Y z ^ 2 := by
        have hG := (WeierstrassCurve.Affine.equation_iff _ _).mp
          (hPGz ▸ L₀.equation_weierstrassP hGzΛ)
        have hY := (WeierstrassCurve.Affine.equation_iff _ _).mp hnsz.1
        simp only [L₀.weierstrassCurve_a₁, L₀.weierstrassCurve_a₂, L₀.weierstrassCurve_a₃,
          zero_mul, add_zero] at hG hY
        exact hG.trans hY.symm
      have hfac : (℘'[L₀] (G z) / 2 - Y z) * (℘'[L₀] (G z) / 2 + Y z) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp hfac with h | h
      · exact sub_eq_zero.mp h
      · exact absurd h hsgn
    rw [L₀.toPoint_of_notMem _ hGzΛ, hcoordz, Point.some.injEq]
    exact ⟨hPGz, hPGy⟩

/-! ## §5. A holomorphic group isomorphism `ℂ/Λ → E(ℂ)` is `z ↦ ξ_{L₀}(αz)` -/

theorem exists_lattice_small (L : PeriodPair) :
    ∃ ε > 0, ∀ l ∈ L.lattice, ‖l‖ < ε → l = 0 := by
  have ho : IsOpen ({0} : Set L.lattice) := isOpen_discrete _
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp ho 0 rfl
  refine ⟨ε, hε, fun l hl hlε => ?_⟩
  have : (⟨l, hl⟩ : L.lattice) ∈ Metric.ball (0 : L.lattice) ε := by
    rw [Metric.mem_ball, Subtype.dist_eq]; simpa using hlε
  have h0 := hball this
  simpa using congrArg Subtype.val (Set.mem_singleton_iff.mp h0)

theorem exists_eq_toPoint_mul (L₀ : PeriodPair) {Λ : Set ℂ}
    (ξ : ℂ → L₀.weierstrassCurve.toAffine.Point) (hξ : IsAnalyticUnif L₀.weierstrassCurve Λ ξ) :
    ∃ α : ℂ, ∀ z, ξ z = L₀.toPoint L₀.discriminant_ne_zero (α * z) := by
  set D := L₀.discriminant_ne_zero
  have hU := L₀.isUniformization_toPoint D
  let ξh : ℂ →+ L₀.weierstrassCurve.toAffine.Point := AddMonoidHom.mk' ξ hξ.1
  let ξ₀h : ℂ →+ L₀.weierstrassCurve.toAffine.Point := AddMonoidHom.mk' (L₀.toPoint D) hU.1
  have hξh : ∀ z, ξh z = ξ z := fun _ => rfl
  have hξ₀h : ∀ z, ξ₀h z = L₀.toPoint D z := fun _ => rfl
  obtain ⟨z₁, r, hr, G, hGd, hGeq⟩ := exists_local_lift L₀ ξ hξ
  set g : ℂ → ℂ := fun t => G (z₁ + t) - G z₁ with hgdef
  have hmem : ∀ t, ‖t‖ < r → z₁ + t ∈ Metric.ball z₁ r := fun t ht => by
    simpa [Metric.mem_ball, dist_eq_norm] using ht
  have hgξ : ∀ t, ‖t‖ < r → ξ t = L₀.toPoint D (g t) := fun t ht => by
    have h1 : ξ (z₁ + t) = ξ z₁ + ξ t := hξ.1 z₁ t
    have h2 : ξ t = ξ (z₁ + t) - ξ z₁ := by rw [h1]; abel
    rw [h2, ← hGeq _ (hmem t ht), ← hGeq _ (Metric.mem_ball_self hr), ← hξ₀h, ← hξ₀h, ← map_sub]
    rfl
  have hgd : ∀ t, ‖t‖ < r → DifferentiableAt ℂ g t := fun t ht => by
    have hG : DifferentiableAt ℂ G (z₁ + t) :=
      hGd.differentiableAt (Metric.isOpen_ball.mem_nhds (hmem t ht))
    exact (hG.comp t ((differentiableAt_id).const_add z₁)).sub_const _
  have hg0 : g 0 = 0 := by simp [hgdef]
  obtain ⟨ε, hε, hsmall⟩ := exists_lattice_small L₀
  have hgc : ContinuousAt g 0 := (hgd 0 (by simpa using hr)).continuousAt
  obtain ⟨δ₁, hδ₁, hδ₁g⟩ := Metric.continuousAt_iff.mp hgc (ε / 3) (by positivity)
  set δ := min (δ₁ / 2) (r / 2) with hδdef
  have hδ : 0 < δ := lt_min (by positivity) (by positivity)
  have hδr2 : δ ≤ r / 2 := min_le_right _ _
  have hδr : δ < r := lt_of_le_of_lt hδr2 (by linarith)
  have hgsmall : ∀ t, ‖t‖ < δ₁ → ‖g t‖ < ε / 3 := fun t ht => by
    have := hδ₁g (x := t) (by simpa [dist_eq_norm] using ht)
    simpa [dist_eq_norm, hg0] using this
  have hadd : ∀ t t', ‖t‖ < δ → ‖t'‖ < δ → g (t + t') = g t + g t' := by
    intro t t' ht ht'
    have hδ₁' : δ ≤ δ₁ / 2 := min_le_left _ _
    have htt' : ‖t + t'‖ < 2 * δ := lt_of_le_of_lt (norm_add_le _ _) (by linarith)
    have hl : g (t + t') - (g t + g t') ∈ L₀.lattice := by
      apply hU.2.2
      rw [← hξ₀h, map_sub, map_add, hξ₀h, hξ₀h, hξ₀h, ← hgξ _ (by linarith), ← hgξ _ (by linarith),
        ← hgξ _ (by linarith), hξ.1, sub_self]
    have hn : ‖g (t + t') - (g t + g t')‖ < ε := by
      have a1 := hgsmall (t + t') (by linarith)
      have a2 := hgsmall t (by linarith)
      have a3 := hgsmall t' (by linarith)
      have b1 := norm_sub_le (g (t + t')) (g t + g t')
      have b2 := norm_add_le (g t) (g t')
      linarith
    exact sub_eq_zero.mp (hsmall _ hl hn)
  set α := deriv g 0 with hαdef
  have hderiv : ∀ t, ‖t‖ < δ → deriv g t = α := by
    intro t ht
    have h1 : HasDerivAt (fun s => g (t + s)) (deriv g t) 0 := by
      have := (hgd t (by linarith)).hasDerivAt
      exact HasDerivAt.comp_const_add t 0 (by simpa using this)
    have h2 : HasDerivAt (fun s => g t + g s) α 0 :=
      ((hgd 0 (by simpa using hr)).hasDerivAt).const_add _
    have hev : (fun s => g (t + s)) =ᶠ[𝓝 0] fun s => g t + g s := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hδ] with s hs
      exact hadd t s ht (by simpa using hs)
    exact (h1.congr_of_eventuallyEq hev.symm).unique h2
  have hlin : ∀ t, ‖t‖ < δ → g t = α * t := by
    intro t ht
    have hk : ∀ s ∈ Metric.ball (0 : ℂ) δ, HasDerivAt (fun s => g s - α * s) 0 s := by
      intro s hs
      have hs' : ‖s‖ < δ := by simpa using hs
      have h1 : HasDerivAt g α s := by rw [← hderiv s hs']; exact (hgd s (by linarith)).hasDerivAt
      have h2 : HasDerivAt (fun s => α * s) α s := by
        simpa using (hasDerivAt_id s).const_mul α
      have := h1.sub h2
      rwa [sub_self] at this
    have := IsOpen.is_const_of_deriv_eq_zero (f := fun s => g s - α * s) Metric.isOpen_ball
      (convex_ball (0 : ℂ) δ).isPreconnected
      (fun s hs => (hk s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hk s hs).deriv) (Metric.mem_ball_self hδ) (show t ∈ Metric.ball (0 : ℂ) δ by simpa using ht)
    simp only [hg0, mul_zero, sub_zero] at this
    exact (sub_eq_zero.mp this.symm)
  refine ⟨α, fun z => ?_⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (‖z‖ / δ)
  have hnpos : (0 : ℝ) < n := lt_of_le_of_lt (by positivity) hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
  have hzn : ‖z / n‖ < δ := by
    rw [norm_div, Complex.norm_natCast, div_lt_iff₀ hnpos]
    rw [div_lt_iff₀ hδ] at hn; linarith
  have hz : z = n • (z / n) := by rw [nsmul_eq_mul]; field_simp
  have hαz : α * z = n • (α * (z / n)) := by rw [nsmul_eq_mul]; field_simp
  calc ξ z = ξh (n • (z / n)) := by rw [hξh, ← hz]
    _ = n • ξh (z / n) := map_nsmul _ _ _
    _ = n • ξ₀h (α * (z / n)) := by rw [hξh, hξ₀h, hgξ _ (by linarith), hlin _ hzn]
    _ = ξ₀h (n • (α * (z / n))) := (map_nsmul _ _ _).symm
    _ = _ := by rw [← hαz, hξ₀h]

/-! ## §6. Every analytic isomorphism `ℂ/L → E(ℂ)` of a short model is `(μ²℘_L, μ³℘'_L/2)` -/

theorem exists_some_eq {W : WeierstrassCurve.Affine ℂ} {x y x' y' : ℂ} (h : W.Nonsingular x y)
    (hx : x = x') (hy : y = y') : ∃ h' : W.Nonsingular x' y', Point.some x y h = .some x' y' h' := by
  subst hx; subst hy; exact ⟨h, rfl⟩

/-- The forward half of the dictionary: an analytic isomorphism `ℂ/L → E_{L₀}(ℂ)` is `z ↦ ξ_{L₀}(αz)` with
`L₀ = αL`. -/
theorem exists_isScale_eq (L₀ L : PeriodPair) (ξ : ℂ → L₀.weierstrassCurve.toAffine.Point)
    (hξ : IsAnalyticUnif L₀.weierstrassCurve L.lattice ξ) :
    ∃ α : ℂ, T5Glue.IsScale L₀ L α ∧ ∀ z, ξ z = L₀.toPoint L₀.discriminant_ne_zero (α * z) := by
  obtain ⟨α, hα⟩ := exists_eq_toPoint_mul L₀ ξ hξ
  have hU := L₀.isUniformization_toPoint L₀.discriminant_ne_zero
  have hker : ∀ z, z ∈ L.lattice ↔ α * z ∈ L₀.lattice := fun z => by
    rw [← SetLike.mem_coe, ← hξ.2.2.1 z, hα z]
    exact ⟨hU.2.2 _, fun h => L₀.toPoint_of_mem _ h⟩
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact L.ω₁_div_two_notMem_lattice ((hker _).2 (by simp))
  refine ⟨α, ⟨hα0, ?_⟩, hα⟩
  ext x
  simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul]
  constructor
  · intro hx
    refine ⟨α⁻¹ * x, (hker _).2 ?_, ?_⟩
    · rwa [mul_inv_cancel_left₀ hα0]
    · rw [mul_inv_cancel_left₀ hα0]
  · rintro ⟨y, hy, rfl⟩
    exact (hker y).1 hy

/-- The converse half: `z ↦ ξ_{L₀}(αz)` with `L₀ = αL` is an analytic isomorphism `ℂ/L → E_{L₀}(ℂ)`. -/
theorem isAnalyticUnif_comp_mul (L₀ L : PeriodPair) (α : ℂ) (hsc : T5Glue.IsScale L₀ L α) :
    IsAnalyticUnif L₀.weierstrassCurve L.lattice
      (fun z => L₀.toPoint L₀.discriminant_ne_zero (α * z)) := by
  have hU := L₀.isUniformization_toPoint L₀.discriminant_ne_zero
  have hα0 := hsc.1
  have hker : ∀ z, α * z ∈ L₀.lattice ↔ z ∈ L.lattice := fun z => by
    rw [hsc.mem_iff, inv_mul_cancel_left₀ hα0]
  refine ⟨fun z w => by simp only [mul_add]; exact hU.1 _ _, fun P => ?_, fun z => ?_, fun z₀ hz₀ => ?_⟩
  · obtain ⟨w, hw⟩ := hU.2.1 P
    exact ⟨α⁻¹ * w, by simp only [mul_inv_cancel_left₀ hα0]; exact hw⟩
  · rw [SetLike.mem_coe, ← hker]
    exact ⟨hU.2.2 _, fun h => L₀.toPoint_of_mem _ h⟩
  · have hz₀' : α * z₀ ∉ L₀.lattice := fun h => hz₀ (L₀.toPoint_of_mem _ h)
    refine ⟨(fun z => α * z) ⁻¹' (L₀.lattice : Set ℂ)ᶜ,
      L₀.isClosed_lattice.isOpen_compl.preimage (continuous_const.mul continuous_id), hz₀',
      fun z => ℘[L₀] (α * z), fun z => ℘'[L₀] (α * z) / 2, ?_, ?_, fun z hz => ⟨_, L₀.toPoint_of_notMem _ hz⟩⟩
    · exact L₀.analyticOnNhd_weierstrassP.differentiableOn.comp
        ((differentiable_id.const_mul α).differentiableOn) (fun z hz => hz)
    · exact (L₀.analyticOnNhd_derivWeierstrassP.differentiableOn.comp
        ((differentiable_id.const_mul α).differentiableOn) (fun z hz => hz)).div_const 2

/-- **The dictionary.** For a period pair `L₀` (every short Weierstrass model over `ℂ` is some
`L₀.weierstrassCurve`, `exists_lattice_eq`), the analytic isomorphisms `ℂ/L → E_{L₀}(ℂ)` in the sense of
`IsAnalyticUnif` are exactly the maps `z ↦ (℘_{L₀}(αz), ℘'_{L₀}(αz)/2)` with `L₀ = αL`. -/
theorem isAnalyticUnif_iff (L₀ L : PeriodPair) (ξ : ℂ → L₀.weierstrassCurve.toAffine.Point) :
    IsAnalyticUnif L₀.weierstrassCurve L.lattice ξ ↔
      ∃ α : ℂ, T5Glue.IsScale L₀ L α ∧ ∀ z, ξ z = L₀.toPoint L₀.discriminant_ne_zero (α * z) := by
  refine ⟨exists_isScale_eq L₀ L ξ, fun ⟨α, hsc, hξ⟩ => ?_⟩
  have : ξ = fun z => L₀.toPoint L₀.discriminant_ne_zero (α * z) := funext hξ
  rw [this]; exact isAnalyticUnif_comp_mul L₀ L α hsc

theorem eq_scaled_of_isAnalyticUnif (W : WeierstrassCurve ℂ) [W.IsElliptic] (h₁ : W.a₁ = 0)
    (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) (L : PeriodPair) (ξ : ℂ → W.toAffine.Point)
    (hξ : IsAnalyticUnif W L.lattice ξ) :
    ∃ μ : ℂ, μ ≠ 0 ∧ W.a₄ = μ ^ 4 * (-L.g₂ / 4) ∧ W.a₆ = μ ^ 6 * (-L.g₃ / 4) ∧
      ∀ z, z ∉ L.lattice →
        ∃ h : W.toAffine.Nonsingular (μ ^ 2 * ℘[L] z) (μ ^ 3 * (℘'[L] z / 2)),
          ξ z = .some _ _ h := by
  obtain ⟨L₀, rfl⟩ := exists_lattice_eq W h₁ h₂ h₃
  obtain ⟨α, hsc, hα⟩ := exists_isScale_eq L₀ L ξ hξ
  have hα0 := hsc.1
  refine ⟨α⁻¹, inv_ne_zero hα0, ?_, ?_, fun z hz => ?_⟩
  · rw [PeriodPair.weierstrassCurve_a₄, hsc.g₂, inv_pow]; ring
  · rw [PeriodPair.weierstrassCurve_a₆, hsc.g₃, inv_pow]; ring
  · have hz' : α * z ∉ L₀.lattice := fun h => hz (by
      rw [hsc.mem_iff, inv_mul_cancel_left₀ hα0] at h; exact h)
    have e1 : ℘[L₀] (α * z) = α⁻¹ ^ 2 * ℘[L] z := by rw [hsc.weierstrassP, inv_pow]
    have e2 : ℘'[L₀] (α * z) / 2 = α⁻¹ ^ 3 * (℘'[L] z / 2) := by
      rw [hsc.derivWeierstrassP, inv_pow]; ring
    obtain ⟨h', e⟩ := exists_some_eq _ e1 e2
    exact ⟨h', by rw [hα z, L₀.toPoint_of_notMem _ hz', e]⟩

/-! ## §7. The printed main theorem of complex multiplication and `ShimuraMainCM` -/

section Printed

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise T5Glue

/-- **LEAF SHIMURA-5.4-PRINTED (the main theorem of complex multiplication, Shimura 1971 Thm 5.4, in its
printed form).** Let `K = ℚ(√−m) ⊂ ℂ` (through `κ`, `√−m ↦ i√m`), `e : Kˢ → ℚ̄` normalized
(`ιC ∘ e = κ` on `K`), `σ ∈ Aut(ℂ)` and `s ∈ 𝔸_K^×` with `σ = [s, K]` on `K^ab` (`ArtinCond`; it forces `σ` to fix
`κ(K)`). Let `𝔞` be a lattice in `K` (`κ(𝔞)` is the lattice of a period pair), `E` an elliptic curve over `ℂ`
given by a short Weierstrass model `y² = x³ + a₄x + a₆` (`E(ℂ) = E.toAffine.Point`) and `ξ : ℂ/𝔞 → E(ℂ)` an
analytic isomorphism (`IsAnalyticUnif`, on `ℂ` with kernel `κ(𝔞)`). Then there is an analytic isomorphism
`ξ' : ℂ/s⁻¹𝔞 → E^σ(ℂ)` (`E^σ = E.map σ`) with `ξ(u)^σ = ξ'(s⁻¹u)` for all `u ∈ K/𝔞`; here `v ∈ K` represents
`s⁻¹u ∈ K/s⁻¹𝔞` when `s_f v − u ∈ 𝔞̂` (`s⁻¹𝔞 = sInvLat m s 𝔞 = K ∩ s_f⁻¹𝔞̂`), and `P ↦ P^σ` is `conjPt σ`.

Source: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), Thm. 5.4;
S. Lang, *Elliptic functions*, Ch. 10, Thm. 3 (numbers UNVERIFIED, from memory; not read here). Differences
from the print, each making this statement weaker or equal: the uniqueness of `ξ'` is dropped; `E` ranges over
short Weierstrass models only (every elliptic curve over `ℂ` has one); `𝔞` comes with a period pair. The
notion `IsAnalyticUnif` (a group homomorphism onto `E(ℂ)` with kernel `κ(𝔞)`, holomorphic in the affine
coordinates away from `κ(𝔞)`) is checked in Lean: by `exists_lattice_eq` and `isAnalyticUnif_iff` the maps
satisfying it are exactly `z ↦ (℘_{L₀}(αz), ℘'_{L₀}(αz)/2)` with `E = E_{L₀}` and `L₀ = α·κ(𝔞)`, i.e. the
analytic group isomorphisms `ℂ/𝔞 → E(ℂ)`. If the print's "analytic isomorphism" is read without the group
law, the printed `ξ'` still satisfies `ξ'(0) = ξ(0)^σ = O` (take `u = 0`), and a biholomorphism of complex tori
fixing `0` is a group isomorphism, so the conclusion here follows in either reading. -/
def ShimuraThm54 : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
  ∀ ξ : ℂ → E.toAffine.Point, IsAnalyticUnif E (kappa m '' 𝔞) ξ →
    ∃ ξ' : ℂ → (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticUnif (E.map (σ : ℂ →+* ℂ)) (kappa m '' sInvLat m s 𝔞) ξ' ∧
      ∀ u v : QNeg m,
        finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞 →
        conjPt (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)

/-- **`ShimuraMainCM` from the printed theorem.** -/
theorem shimuraMainCM_of_printed (h : ShimuraThm54) : ShimuraMainCM := by
  intro m _ hm e he σ s hs 𝔞 P P' hP hP'
  have : P.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr P.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩
  have hξ := toPoint_isAnalyticUnif P
  rw [hP] at hξ
  obtain ⟨ξ', hξ', hcomm⟩ := h m hm e he σ s hs 𝔞 ⟨P, hP⟩ P.weierstrassCurve
    (by simp) (by simp) (by simp) _ hξ
  rw [← hP'] at hξ'
  obtain ⟨μ, hμ, ha4, ha6, hcoord⟩ :=
    eq_scaled_of_isAnalyticUnif (P.weierstrassCurve.map (σ : ℂ →+* ℂ)) (by simp) (by simp)
      (by simp) P' ξ' hξ'
  simp only [WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, PeriodPair.weierstrassCurve_a₄,
    PeriodPair.weierstrassCurve_a₆, map_div₀, map_neg, map_ofNat] at ha4 ha6
  refine ⟨μ, ⟨hμ, ?_, ?_⟩, fun u v hu huv => ?_⟩
  · linear_combination (-4 : ℂ) * ha4
  · linear_combination (-4 : ℂ) * ha6
  · have hc := hcomm u v huv
    rw [P.toPoint_of_notMem _ hu] at hc
    have hv : kappa m v ∉ P'.lattice := by
      intro hv
      rw [← SetLike.mem_coe, ← hξ'.2.2.1] at hv
      rw [hv] at hc
      exact Point.some_ne_zero _ hc
    obtain ⟨h', e'⟩ := hcoord _ hv
    rw [e'] at hc
    simp only [conjPt, Point.some.injEq, RingEquiv.coe_toRingHom, map_div₀, map_ofNat] at hc
    refine ⟨hc.1, ?_⟩
    linear_combination 2 * hc.2

end Printed

end ZInQ.Contrib.HCMDict

