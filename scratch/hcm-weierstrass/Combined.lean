import ZInQKernel.Contrib.OneProof.ShimuraThm54Biholo

/-! hcm-weierstrass: the combined leaf (G1 from hcm-weierstrass, R2 from hcm-lattice). Lines 2–1815 below are
copied verbatim from origin/wip/hcm-lattice:scratch/hcm-lattice/HCMLattice.lean (b3d51684), only the import changed;
the new part is at the end (namespace ZInQ.Contrib.HCMWeierstrass). -/

/-!
# hcm-lattice: `hCM` as a direct instance of Shimura 1971 Thm 5.4

Task hcm-lattice (2026-11-17). Report: `docs/research/hcm-lattice.md`; log: `scratch/hcm-lattice/log.md`.
Proposed path: `ZInQKernel/Contrib/OneProof/HCMLattice.lean` (imports only `ShimuraMainCM`, not `Main`).

hcm-dict's leaf `HCMDict.ShimuraThm54` differs from the print in two steps: its hypothesis on `ξ` is the surrogate
`IsAnalyticUnif`, and its `s⁻¹𝔞` is `K ∩ s_f⁻¹𝔞̂` rather than Shimura's lattice with `p`-components `s_p⁻¹𝔞_p`. This file

* §A–§B: defines analytic isomorphisms `ℂ/Λ → E(ℂ) ⊂ ℙ²(ℂ)` over homogeneous coordinates (`IsAnalyticIso`) and
  proves that the Weierstrass map `z ↦ [℘(z) : ℘'(z)/2 : 1]` is one (`toPoint_isAnalyticIso`);
* §C: proves the Weierstrass-map step: a holomorphic map `ℂ → E_{L₀}(ℂ)` inducing a bijection `ℂ/L → E_{L₀}(ℂ)` with
  `0 ↦ O` is `z ↦ ξ_{L₀}(αz)`, `L₀ = αL` (`eq_toPoint_of_holo`; Liouville applied to `x'/(2y)`);
* §L–§O: proves Shimura's localization form `(s⁻¹𝔞)_p = s_p⁻¹𝔞_p` of hcm-dict's `sInvLat` for every lattice `𝔞`
  (`locLat_sInvLat`; `K_p = ∏_{v ∣ p} K_v`), and that `sInvLat s 𝔞` is a lattice (`exists_periodPair_sInvLat`);
* §P: states `ShimuraThm54Local` (the print's hypotheses, the print's `s⁻¹𝔞` and `s⁻¹u`) and proves
  `shimuraMainCM_of_local : ShimuraThm54Local → T5Glue.ShimuraMainCM` and
  `shimuraThm54_of_local : ShimuraThm54Local → HCMDict.ShimuraThm54`.

No `sorry`, no `axiom`; only `propext`, `Classical.choice`, `Quot.sound`.
-/

noncomputable section

open Complex Topology Filter
open scoped PeriodPair

namespace ZInQ.Contrib.HCMLattice

open WeierstrassCurve.Affine (Point)

/-! ## §A. Analytic isomorphisms `ℂ/Λ → E(ℂ) ⊂ ℙ²(ℂ)` -/

/-- `[X : Y : Z]` are homogeneous coordinates of the point `P ∈ E(ℂ) ⊂ ℙ²(ℂ)` (`E(ℂ) = W.toAffine.Point`:
the affine point `(x, y)` is `[x : y : 1]` and `O` is `[0 : 1 : 0]`). -/
def IsProjCoord (W : WeierstrassCurve ℂ) (P : W.toAffine.Point) (X Y Z : ℂ) : Prop :=
  (Z ≠ 0 ∧ ∃ h : W.toAffine.Nonsingular (X / Z) (Y / Z), P = .some _ _ h) ∨
    (X = 0 ∧ Y ≠ 0 ∧ Z = 0 ∧ P = 0)

/-- `(X, Y, Z) : U → ℂ³ ∖ 0` is a holomorphic lift of `ξ : ℂ → E(ℂ) ⊂ ℙ²(ℂ)` on the open set `U`. -/
def IsHoloLift (W : WeierstrassCurve ℂ) (ξ : ℂ → W.toAffine.Point) (U : Set ℂ) (X Y Z : ℂ → ℂ) : Prop :=
  IsOpen U ∧ DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧ DifferentiableOn ℂ Z U ∧
    ∀ z ∈ U, IsProjCoord W (ξ z) (X z) (Y z) (Z z)

/-- `ξ : ℂ → E(ℂ) ⊂ ℙ²(ℂ)` is holomorphic: near every point it lifts holomorphically to `ℂ³ ∖ 0`
(the complex structure of `ℙ²(ℂ)`, restricted to the closed curve `E(ℂ)`). -/
def IsHolomorphicMap (W : WeierstrassCurve ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  ∀ z₀ : ℂ, ∃ (U : Set ℂ) (X Y Z : ℂ → ℂ), z₀ ∈ U ∧ IsHoloLift W ξ U X Y Z

/-- `F ∧ F'` for a lift `F = (X, Y, Z)`: it vanishes at `z` iff the differential of `[X : Y : Z]` vanishes at `z`. -/
def wedge (X Y Z : ℂ → ℂ) (z : ℂ) : Fin 3 → ℂ :=
  ![Y z * deriv Z z - Z z * deriv Y z, Z z * deriv X z - X z * deriv Z z,
    X z * deriv Y z - Y z * deriv X z]

/-- `ξ` has nowhere vanishing differential (as a map into `ℙ²(ℂ)`). -/
def IsImmersion (W : WeierstrassCurve ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  ∀ z₀ : ℂ, ∃ (U : Set ℂ) (X Y Z : ℂ → ℂ), z₀ ∈ U ∧ IsHoloLift W ξ U X Y Z ∧ wedge X Y Z z₀ ≠ 0

/-- `ξ : ℂ → E(ℂ)` induces a bijection `ℂ/Λ → E(ℂ)`. -/
def InducesBij (W : WeierstrassCurve ℂ) (Λ : Set ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  (∀ z, ∀ l ∈ Λ, ξ (z + l) = ξ z) ∧ (∀ z w, ξ z = ξ w → z - w ∈ Λ) ∧ Function.Surjective ξ

/-- **Analytic isomorphism `ℂ/Λ → E(ℂ)`**, read on `ℂ`: `ξ` induces a bijection `ℂ/Λ → E(ℂ)`, is holomorphic
into `E(ℂ) ⊂ ℙ²(ℂ)` and has nowhere vanishing differential; i.e. a biholomorphism of the Riemann surfaces
`ℂ/Λ` and `E(ℂ)` (a bijective holomorphic map with nonvanishing differential has a holomorphic inverse). -/
def IsAnalyticIso (W : WeierstrassCurve ℂ) (Λ : Set ℂ) (ξ : ℂ → W.toAffine.Point) : Prop :=
  InducesBij W Λ ξ ∧ IsHolomorphicMap W ξ ∧ IsImmersion W ξ

theorem isProjCoord_some {W : WeierstrassCurve ℂ} {x y X Y Z : ℂ} (h : W.toAffine.Nonsingular x y)
    (hZ : Z ≠ 0) (hX : X / Z = x) (hY : Y / Z = y) : IsProjCoord W (.some x y h) X Y Z := by
  subst hX hY; exact Or.inl ⟨hZ, h, rfl⟩

theorem isProjCoord_zero {W : WeierstrassCurve ℂ} {Y : ℂ} (hY : Y ≠ 0) : IsProjCoord W 0 0 Y 0 :=
  Or.inr ⟨rfl, hY, rfl, rfl⟩

/-! ## §B. The Weierstrass map is an analytic isomorphism -/

section Weierstrass

variable (L : PeriodPair)

theorem toPoint_sub (z w : ℂ) :
    L.toPoint L.discriminant_ne_zero (z - w) =
      L.toPoint L.discriminant_ne_zero z - L.toPoint L.discriminant_ne_zero w := by
  have hU := L.isUniformization_toPoint L.discriminant_ne_zero
  let f : ℂ →+ L.weierstrassCurve.toAffine.Point := AddMonoidHom.mk' (L.toPoint _) hU.1
  exact map_sub f z w

theorem toPoint_inducesBij : InducesBij L.weierstrassCurve L.lattice (L.toPoint L.discriminant_ne_zero) := by
  have hU := L.isUniformization_toPoint L.discriminant_ne_zero
  refine ⟨fun z l hl => ?_, fun z w h => hU.2.2 _ ?_, hU.2.1⟩
  · rw [hU.1, L.toPoint_of_mem _ hl, add_zero]
  · rw [toPoint_sub, h, sub_self]

/-- `℘'(z₀) = 0` forces `℘''(z₀) ≠ 0` (the roots of `4x³ − g₂x − g₃` are simple). -/
theorem deriv_derivWeierstrassP_ne {z₀ : ℂ} (hz₀ : z₀ ∉ L.lattice) (h0 : ℘'[L] z₀ = 0) :
    deriv ℘'[L] z₀ ≠ 0 := by
  have hopen : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hP'a : AnalyticAt ℂ ℘'[L] z₀ := L.analyticOnNhd_derivWeierstrassP z₀ hz₀
  rcases hP'a.eventually_eq_zero_or_eventually_ne_zero with hz | hnz
  · -- `℘' ≡ 0` near `z₀`: `℘` is constant near `z₀`, so the Weierstrass map is not injective mod `L`
    exfalso
    obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hz.and (hopen.mem_nhds hz₀))
    have hconst : ∀ z ∈ Metric.ball z₀ r, ℘[L] z = ℘[L] z₀ := by
      intro z hz
      refine IsOpen.is_const_of_deriv_eq_zero (f := ℘[L]) Metric.isOpen_ball
        (convex_ball z₀ r).isPreconnected
        (fun w hw => ((L.analyticOnNhd_weierstrassP w (hball w hw).2).differentiableAt).differentiableWithinAt)
        (fun w hw => by rw [PeriodPair.deriv_weierstrassP]; exact (hball w hw).1) hz
        (Metric.mem_ball_self hr)
    obtain ⟨ε, hε, hsmall⟩ := ZInQ.Contrib.HCMDict.exists_lattice_small L
    set t : ℂ := ((min r ε / 2 : ℝ) : ℂ)
    have ht0 : t ≠ 0 := by
      simp only [t, ne_eq, Complex.ofReal_eq_zero]; positivity
    have htn : ‖t‖ = min r ε / 2 := by
      simp only [t, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    have htr : z₀ + t ∈ Metric.ball z₀ r := by
      simp only [Metric.mem_ball, dist_self_add_left, htn]
      linarith [min_le_left r ε]
    have hpt : L.toPoint L.discriminant_ne_zero (z₀ + t) = L.toPoint L.discriminant_ne_zero z₀ := by
      rw [L.toPoint_of_notMem _ (hball _ htr).2, L.toPoint_of_notMem _ hz₀, Point.some.injEq]
      exact ⟨hconst _ htr, by rw [(hball _ htr).1, h0]⟩
    have hl := (toPoint_inducesBij L).2.1 _ _ hpt
    rw [add_sub_cancel_left] at hl
    exact ht0 (hsmall t hl (by rw [htn]; linarith [min_le_right r ε]))
  · intro hd
    -- `h = 2℘'' − 12℘² + g₂` vanishes off the zeros of `℘'`, hence at `z₀`
    set h : ℂ → ℂ := fun z => 2 * deriv ℘'[L] z - 12 * ℘[L] z ^ 2 + L.g₂
    have hha : ContinuousAt h z₀ :=
      (((hP'a.deriv.continuousAt.const_mul 2).sub
        (((L.analyticOnNhd_weierstrassP z₀ hz₀).continuousAt.pow 2).const_mul 12)).add
        continuousAt_const)
    have hev : ∀ᶠ z in 𝓝[≠] z₀, h z = 0 := by
      have hn : ∀ᶠ z in 𝓝[≠] z₀, z ∈ (L.lattice : Set ℂ)ᶜ :=
        nhdsWithin_le_nhds (hopen.mem_nhds hz₀)
      filter_upwards [hnz, hn] with z hzne hzL
      have hzo : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 z := hopen.mem_nhds hzL
      have heq : (fun w => ℘'[L] w ^ 2) =ᶠ[𝓝 z] fun w => 4 * ℘[L] w ^ 3 - L.g₂ * ℘[L] w - L.g₃ :=
        Filter.eventually_of_mem hzo fun w hw => L.derivWeierstrassP_sq w hw
      have hPd : DifferentiableAt ℂ ℘[L] z := (L.analyticOnNhd_weierstrassP z hzL).differentiableAt
      have hP'd : DifferentiableAt ℂ ℘'[L] z := (L.analyticOnNhd_derivWeierstrassP z hzL).differentiableAt
      have d1 : HasDerivAt (fun w => ℘'[L] w ^ 2) (2 * ℘'[L] z * deriv ℘'[L] z) z := by
        have := (hasDerivAt_pow 2 (℘'[L] z)).comp z hP'd.hasDerivAt
        convert this using 1
        · rfl
        · push_cast; ring
      have d2 : HasDerivAt (fun w => 4 * ℘[L] w ^ 3 - L.g₂ * ℘[L] w - L.g₃)
          (4 * (3 * ℘[L] z ^ 2 * ℘'[L] z) - L.g₂ * ℘'[L] z) z := by
        have hp : HasDerivAt ℘[L] (℘'[L] z) z := by
          rw [← PeriodPair.deriv_weierstrassP]; exact hPd.hasDerivAt
        have := (((hp.pow 3).const_mul 4).sub (hp.const_mul L.g₂)).sub_const L.g₃
        simpa using this
      have hu := (d1.congr_of_eventuallyEq heq.symm).unique d2
      have : ℘'[L] z * h z = 0 := by simp only [h]; linear_combination hu
      exact (mul_eq_zero.1 this).resolve_left hzne
    have hz0 : h z₀ = 0 := by
      have t1 : Tendsto h (𝓝[≠] z₀) (𝓝 (h z₀)) := hha.tendsto.mono_left nhdsWithin_le_nhds
      have t2 : Tendsto h (𝓝[≠] z₀) (𝓝 0) := tendsto_const_nhds.congr' (hev.mono fun z hz => hz.symm)
      exact tendsto_nhds_unique t1 t2
    simp only [h, hd, mul_zero, zero_sub] at hz0
    have hsq := L.derivWeierstrassP_sq z₀ hz₀
    rw [h0] at hsq
    apply L.discriminant_ne_zero
    have hg₂ : L.g₂ = 12 * ℘[L] z₀ ^ 2 := by linear_combination hz0
    have hg₃ : L.g₃ = -8 * ℘[L] z₀ ^ 3 := by
      linear_combination hsq - ℘[L] z₀ * hg₂
    show L.g₂ ^ 3 - 27 * L.g₃ ^ 2 = 0
    rw [hg₂, hg₃]; ring

theorem IsImmersion.isHolomorphicMap {W : WeierstrassCurve ℂ} {ξ : ℂ → W.toAffine.Point}
    (h : IsImmersion W ξ) : IsHolomorphicMap W ξ := fun z₀ => by
  obtain ⟨U, X, Y, Z, hz, hL, -⟩ := h z₀
  exact ⟨U, X, Y, Z, hz, hL⟩

/-- **The Weierstrass map `z ↦ [℘(z) : ℘'(z)/2 : 1]` has nowhere vanishing differential** into `ℙ²(ℂ)`:
off `L` because `℘'` and `℘''` have no common zero, at `l₀ ∈ L` through the lift
`[w + w³h : (−2 + w³k)/2 : w³]` (`w = z − l₀`, `℘ = w⁻² + h`, `℘' = −2w⁻³ + k`), whose third wedge component is `1`. -/
theorem toPoint_isImmersion : IsImmersion L.weierstrassCurve (L.toPoint L.discriminant_ne_zero) := by
  intro z₀
  by_cases hz₀ : z₀ ∈ L.lattice
  · set l₀ : L.lattice := ⟨z₀, hz₀⟩
    set U : Set ℂ := ((L.lattice : Set ℂ) \ {z₀})ᶜ with hU
    have hUo : IsOpen U := L.isOpen_compl_lattice_sdiff
    have hz₀U : z₀ ∈ U := by simp [hU]
    set h : ℂ → ℂ := fun z => ℘[L - z₀] z - 1 / z₀ ^ 2
    set k : ℂ → ℂ := ℘'[L - z₀]
    have hhd : DifferentiableOn ℂ h U := (L.differentiableOn_weierstrassPExcept z₀).sub_const _
    have hkd : DifferentiableOn ℂ k U := L.differentiableOn_derivWeierstrassPExcept z₀
    have hwd : Differentiable ℂ fun z : ℂ => z - z₀ := differentiable_id.sub_const _
    set X : ℂ → ℂ := fun z => (z - z₀) + (z - z₀) ^ 3 * h z
    set Y : ℂ → ℂ := fun z => (-2 + (z - z₀) ^ 3 * k z) / 2
    set Z : ℂ → ℂ := fun z => (z - z₀) ^ 3
    have hXd : DifferentiableOn ℂ X U :=
      hwd.differentiableOn.add ((hwd.pow 3).differentiableOn.mul hhd)
    have hYd : DifferentiableOn ℂ Y U :=
      ((differentiableOn_const _).add ((hwd.pow 3).differentiableOn.mul hkd)).div_const 2
    have hZd : DifferentiableOn ℂ Z U := (hwd.pow 3).differentiableOn
    refine ⟨U, X, Y, Z, hz₀U, ⟨hUo, hXd, hYd, hZd, fun z hz => ?_⟩, ?_⟩
    · by_cases hzz : z = z₀
      · subst hzz
        rw [L.toPoint_of_mem _ hz₀]
        have hX : X z = 0 := by simp [X]
        have hY : Y z = -1 := by norm_num [Y]
        have hZ : Z z = 0 := by simp [Z]
        rw [hX, hY, hZ]
        exact isProjCoord_zero (by norm_num)
      · have hzL : z ∉ L.lattice := fun hl => hz ⟨hl, hzz⟩
        have hw : z - z₀ ≠ 0 := sub_ne_zero.2 hzz
        rw [L.toPoint_of_notMem _ hzL]
        refine isProjCoord_some _ (pow_ne_zero 3 hw) ?_ ?_
        · have e := L.weierstrassPExcept_add l₀ z
          simp only [l₀] at e
          simp only [X, Z, h]
          rw [← e]
          field_simp
          ring
        · have e := L.derivWeierstrassPExcept_sub l₀ z
          simp only [l₀] at e
          simp only [Y, Z, k]
          rw [← e]
          field_simp
          ring
    · intro hw
      have h3 := congrFun hw 2
      have hU' : U ∈ 𝓝 z₀ := hUo.mem_nhds hz₀U
      have dX : HasDerivAt X 1 z₀ := by
        have h1 : HasDerivAt (fun z : ℂ => z - z₀) 1 z₀ := (hasDerivAt_id z₀).sub_const z₀
        have h2 : HasDerivAt (fun z : ℂ => (z - z₀) ^ 3) (3 * (z₀ - z₀) ^ 2 * 1) z₀ := by
          have hp := hasDerivAt_pow 3 ((fun z : ℂ => z - z₀) z₀)
          have := HasDerivAt.comp (h := fun z : ℂ => z - z₀) z₀ hp h1
          convert this using 1
          rfl
        have h4 := (h2.mul (hhd.differentiableAt hU').hasDerivAt)
        have := h1.add h4
        convert this using 1; simp
      have hXz : X z₀ = 0 := by simp [X]
      have hYz : Y z₀ = -1 := by norm_num [Y]
      simp only [wedge, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, Pi.zero_apply,
        hXz, hYz, dX.deriv] at h3
      norm_num at h3
  · refine ⟨(L.lattice : Set ℂ)ᶜ, ℘[L], fun z => ℘'[L] z / 2, fun _ => 1, hz₀,
      ⟨L.isClosed_lattice.isOpen_compl, L.analyticOnNhd_weierstrassP.differentiableOn,
        (L.analyticOnNhd_derivWeierstrassP.differentiableOn).div_const 2, differentiableOn_const 1,
        fun z hz => ?_⟩, ?_⟩
    · rw [L.toPoint_of_notMem _ hz]
      exact isProjCoord_some _ one_ne_zero (div_one _) (div_one _)
    · intro hw
      have h1 := congrFun hw 0
      have h2 := congrFun hw 1
      simp only [wedge, Matrix.cons_val_zero, Matrix.cons_val_one, Pi.zero_apply,
        deriv_const, PeriodPair.deriv_weierstrassP, deriv_div_const, mul_zero, one_mul, zero_sub,
        sub_zero, neg_eq_zero, div_eq_zero_iff, two_ne_zero, or_false] at h1 h2
      exact deriv_derivWeierstrassP_ne L hz₀ h2 h1

/-- **The Weierstrass map is an analytic isomorphism `ℂ/L → E_L(ℂ)`.** -/
theorem toPoint_isAnalyticIso :
    IsAnalyticIso L.weierstrassCurve L.lattice (L.toPoint L.discriminant_ne_zero) :=
  ⟨toPoint_inducesBij L, (toPoint_isImmersion L).isHolomorphicMap, toPoint_isImmersion L⟩

end Weierstrass

/-! ## §C. A holomorphic bijection `ℂ/Λ → E_{L₀}(ℂ)` with `0 ↦ O` is `z ↦ ξ_{L₀}(αz)` -/

section Liouville

/-- The affine `x`-coordinate of a point (junk value `0` at `O`). -/
def xP {W : WeierstrassCurve ℂ} : W.toAffine.Point → ℂ
  | .zero => 0
  | .some x _ _ => x

/-- The affine `y`-coordinate of a point (junk value `0` at `O`). -/
def yP {W : WeierstrassCurve ℂ} : W.toAffine.Point → ℂ
  | .zero => 0
  | .some _ y _ => y

theorem eq_some_of_ne_zero {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} (hP : P ≠ 0) :
    ∃ h : W.toAffine.Nonsingular (xP P) (yP P), P = .some _ _ h := by
  cases P with
  | zero => exact absurd rfl hP
  | some x y h => exact ⟨h, rfl⟩

theorem IsProjCoord.ne_zero_iff {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} {X Y Z : ℂ}
    (h : IsProjCoord W P X Y Z) : P ≠ 0 ↔ Z ≠ 0 := by
  rcases h with ⟨hZ, hns, rfl⟩ | ⟨-, -, hZ, rfl⟩
  · exact ⟨fun _ => hZ, fun _ => Point.some_ne_zero hns⟩
  · simp [hZ]

theorem IsProjCoord.coords {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} {X Y Z : ℂ}
    (h : IsProjCoord W P X Y Z) (hP : P ≠ 0) : xP P = X / Z ∧ yP P = Y / Z := by
  rcases h with ⟨-, -, rfl⟩ | ⟨-, -, -, rfl⟩
  · exact ⟨rfl, rfl⟩
  · exact absurd rfl hP

theorem IsProjCoord.of_zero {W : WeierstrassCurve ℂ} {X Y Z : ℂ} (h : IsProjCoord W 0 X Y Z) :
    X = 0 ∧ Y ≠ 0 ∧ Z = 0 := by
  rcases h with ⟨-, hns, he⟩ | ⟨hX, hY, hZ, -⟩
  · exact absurd he.symm (Point.some_ne_zero hns)
  · exact ⟨hX, hY, hZ⟩

/-- Homogeneous coordinates satisfy the homogeneous short Weierstrass equation. -/
theorem IsProjCoord.homog {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} {X Y Z : ℂ}
    (h : IsProjCoord W P X Y Z) (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0) (h₃ : W.a₃ = 0) :
    Y ^ 2 * Z = X ^ 3 + W.a₄ * X * Z ^ 2 + W.a₆ * Z ^ 3 := by
  rcases h with ⟨hZ, hns, -⟩ | ⟨hX, -, hZ, -⟩
  · have e := (WeierstrassCurve.Affine.equation_iff _ _).1 hns.1
    rw [h₁, h₂, h₃] at e
    have key : Y ^ 2 * Z - (X ^ 3 + W.a₄ * X * Z ^ 2 + W.a₆ * Z ^ 3) =
        Z ^ 3 * ((Y / Z) ^ 2 + 0 * (X / Z) * (Y / Z) + 0 * (Y / Z) -
          ((X / Z) ^ 3 + 0 * (X / Z) ^ 2 + W.a₄ * (X / Z) + W.a₆)) := by
      field_simp; ring
    rw [e, sub_self, mul_zero] at key
    linear_combination key
  · rw [hX, hZ]; ring

/-- Two homogeneous coordinate vectors of the same point are proportional. -/
theorem IsProjCoord.cross_eq_zero {W : WeierstrassCurve ℂ} {P : W.toAffine.Point} {X Y Z X' Y' Z' : ℂ}
    (h : IsProjCoord W P X Y Z) (h' : IsProjCoord W P X' Y' Z') :
    Y * Z' - Z * Y' = 0 ∧ Z * X' - X * Z' = 0 ∧ X * Y' - Y * X' = 0 := by
  rcases h with ⟨hZ, hns, rfl⟩ | ⟨hX, -, hZ, rfl⟩ <;>
    rcases h' with ⟨hZ', hns', he⟩ | ⟨hX', -, hZ', he⟩
  · simp only [Point.some.injEq] at he
    obtain ⟨ex, ey⟩ := he
    field_simp at ex ey
    refine ⟨by linear_combination ey, by linear_combination -ex, ?_⟩
    have : X * Y' * Z' * Z = Y * X' * Z' * Z := by linear_combination Y' * Z * ex - X' * Z * ey
    have hZZ : Z' * Z ≠ 0 := mul_ne_zero hZ' hZ
    have h2 : (X * Y' - Y * X') * (Z' * Z) = 0 := by linear_combination this
    exact (mul_eq_zero.1 h2).resolve_right hZZ
  · exact absurd he (Point.some_ne_zero hns)
  · exact absurd he.symm (Point.some_ne_zero hns')
  · rw [hX, hZ, hX', hZ']; simp

/-- Proportional homogeneous coordinate vectors give the same point. -/
theorem IsProjCoord.eq_of_cross {W : WeierstrassCurve ℂ} {P Q : W.toAffine.Point} {X Y Z X' Y' Z' : ℂ}
    (h : IsProjCoord W P X Y Z) (h' : IsProjCoord W Q X' Y' Z')
    (c₀ : Y * Z' - Z * Y' = 0) (c₁ : Z * X' - X * Z' = 0) : P = Q := by
  rcases h with ⟨hZ, hns, rfl⟩ | ⟨hX, hY, hZ, rfl⟩ <;>
    rcases h' with ⟨hZ', hns', rfl⟩ | ⟨hX', hY', hZ', rfl⟩
  · have ex : X / Z = X' / Z' := by field_simp; linear_combination -c₁
    have ey : Y / Z = Y' / Z' := by field_simp; linear_combination c₀
    simp only [Point.some.injEq]; exact ⟨ex, ey⟩
  · rw [hZ'] at c₀; simp only [mul_zero, zero_sub, neg_eq_zero, mul_eq_zero] at c₀
    exact absurd (c₀.resolve_left hZ) hY'
  · rw [hZ] at c₀; simp only [zero_mul, sub_zero, mul_eq_zero] at c₀
    exact absurd (c₀.resolve_left hY) hZ'
  · rfl

variable {W : WeierstrassCurve ℂ}

/-- The `x`-coordinate of `ξ`. -/
def xc (ξ : ℂ → W.toAffine.Point) (z : ℂ) : ℂ := xP (ξ z)

/-- The `y`-coordinate of `ξ`. -/
def yc (ξ : ℂ → W.toAffine.Point) (z : ℂ) : ℂ := yP (ξ z)

/-- Affine holomorphic coordinates near a point not sent to `O`. -/
theorem exists_affine_chart {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) {z₀ : ℂ}
    (hz : ξ z₀ ≠ 0) : ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ ∃ X Y Z : ℂ → ℂ, DifferentiableOn ℂ X V ∧
      DifferentiableOn ℂ Y V ∧ DifferentiableOn ℂ Z V ∧
      ∀ z ∈ V, Z z ≠ 0 ∧ ξ z ≠ 0 ∧ xc ξ z = X z / Z z ∧ yc ξ z = Y z / Z z := by
  obtain ⟨U, X, Y, Z, hzU, hUo, hXd, hYd, hZd, hc⟩ := hh z₀
  refine ⟨U ∩ Z ⁻¹' {0}ᶜ, hZd.continuousOn.isOpen_inter_preimage hUo isOpen_compl_singleton,
    ⟨hzU, (hc z₀ hzU).ne_zero_iff.1 hz⟩, X, Y, Z, hXd.mono Set.inter_subset_left,
    hYd.mono Set.inter_subset_left, hZd.mono Set.inter_subset_left, fun z hz => ?_⟩
  have hξz : ξ z ≠ 0 := (hc z hz.1).ne_zero_iff.2 hz.2
  exact ⟨hz.2, hξz, ((hc z hz.1).coords hξz).1, ((hc z hz.1).coords hξz).2⟩

theorem isOpen_ne_zero {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) :
    IsOpen {z | ξ z ≠ 0} := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  obtain ⟨V, hVo, hzV, X, Y, Z, -, -, -, hV⟩ := exists_affine_chart hh hz
  exact ⟨V, fun w hw => (hV w hw).2.1, hVo, hzV⟩

theorem differentiableOn_xc {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) :
    DifferentiableOn ℂ (xc ξ) {z | ξ z ≠ 0} := by
  intro z hz
  obtain ⟨V, hVo, hzV, X, Y, Z, hXd, -, hZd, hV⟩ := exists_affine_chart hh hz
  have hV' : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : DifferentiableAt ℂ (fun w => X w / Z w) z :=
    (hXd.differentiableAt hV').div (hZd.differentiableAt hV') (hV z hzV).1
  exact (hd.congr_of_eventuallyEq (Filter.eventually_of_mem hV' fun w hw => (hV w hw).2.2.1)).differentiableWithinAt

theorem differentiableOn_yc {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) :
    DifferentiableOn ℂ (yc ξ) {z | ξ z ≠ 0} := by
  intro z hz
  obtain ⟨V, hVo, hzV, X, Y, Z, -, hYd, hZd, hV⟩ := exists_affine_chart hh hz
  have hV' : V ∈ 𝓝 z := hVo.mem_nhds hzV
  have hd : DifferentiableAt ℂ (fun w => Y w / Z w) z :=
    (hYd.differentiableAt hV').div (hZd.differentiableAt hV') (hV z hzV).1
  exact (hd.congr_of_eventuallyEq (Filter.eventually_of_mem hV' fun w hw => (hV w hw).2.2.2)).differentiableWithinAt

theorem hasDerivAt_pow_comp {f : ℂ → ℂ} {f' z : ℂ} (n : ℕ) (hf : HasDerivAt f f' z) :
    HasDerivAt (fun x => f x ^ n) (n * f z ^ (n - 1) * f') z := by
  have hp := hasDerivAt_pow n (f z)
  have := HasDerivAt.comp (h := f) z hp hf
  convert this using 1
  rfl

theorem yc_sq (L₀ : PeriodPair) {ξ : ℂ → L₀.weierstrassCurve.toAffine.Point} {z : ℂ} (hz : ξ z ≠ 0) :
    yc ξ z ^ 2 = xc ξ z ^ 3 + (-L₀.g₂ / 4) * xc ξ z + (-L₀.g₃ / 4) := by
  obtain ⟨h, -⟩ := eq_some_of_ne_zero hz
  have e := (WeierstrassCurve.Affine.equation_iff _ _).1 h.1
  simp only [PeriodPair.weierstrassCurve_a₁, PeriodPair.weierstrassCurve_a₂,
    PeriodPair.weierstrassCurve_a₃, PeriodPair.weierstrassCurve_a₄, PeriodPair.weierstrassCurve_a₆,
    zero_mul, add_zero] at e
  exact e

/-- The cubic `x³ − g₂x/4 − g₃/4` has simple roots. -/
theorem cubic_deriv_ne (L₀ : PeriodPair) {e : ℂ} (he : e ^ 3 + (-L₀.g₂ / 4) * e + (-L₀.g₃ / 4) = 0) :
    3 * e ^ 2 + (-L₀.g₂ / 4) ≠ 0 := by
  intro h
  apply L₀.discriminant_ne_zero
  have hg₂ : L₀.g₂ = 12 * e ^ 2 := by linear_combination -4 * h
  have hg₃ : L₀.g₃ = -8 * e ^ 3 := by linear_combination -4 * he - e * hg₂
  show L₀.g₂ ^ 3 - 27 * L₀.g₃ ^ 2 = 0
  rw [hg₂, hg₃]; ring

/-- **Local holomorphic extensions of `ξ^*(dx/2y)/dz`.** Near every point, the function
`x'(z)/(2y(z))` (defined where `ξ(z) ≠ O` and `y(z) ≠ 0`) agrees with a holomorphic function:
`y'/(3x² − g₂/4)` near `y = 0` (the cubic has simple roots), and `−u' + uq'/(2q)` near `O`
(`u = X/Y`, `w = Z/Y`, `q = 1 − a₄uw − a₆w²`, `wq = u³`). -/
theorem exists_local_ext (L₀ : PeriodPair) {ξ : ℂ → L₀.weierstrassCurve.toAffine.Point}
    (hh : IsHolomorphicMap _ ξ) (z₀ : ℂ) :
    ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ V ∧
      ∀ z ∈ V, ξ z ≠ 0 → yc ξ z ≠ 0 → ψ z = deriv (xc ξ) z / (2 * yc ξ z) := by
  have hΩ := isOpen_ne_zero hh
  have hxd := differentiableOn_xc hh
  have hyd := differentiableOn_yc hh
  by_cases hz₀ : ξ z₀ = 0
  · obtain ⟨U, X, Y, Z, hzU, hUo, hXd, hYd, hZd, hc⟩ := hh z₀
    obtain ⟨hX0, hY0, hZ0⟩ := (hz₀ ▸ hc z₀ hzU).of_zero
    set a₄ : ℂ := -L₀.g₂ / 4
    set a₆ : ℂ := -L₀.g₃ / 4
    have hhom : ∀ z ∈ U, Y z ^ 2 * Z z = X z ^ 3 + a₄ * X z * Z z ^ 2 + a₆ * Z z ^ 3 := fun z hz => by
      have := (hc z hz).homog (by simp) (by simp) (by simp)
      simpa using this
    set u : ℂ → ℂ := fun z => X z / Y z
    set w : ℂ → ℂ := fun z => Z z / Y z
    set q : ℂ → ℂ := fun z => 1 - a₄ * u z * w z - a₆ * w z ^ 2
    set U₁ := U ∩ Y ⁻¹' {0}ᶜ
    have hU₁o : IsOpen U₁ := hYd.continuousOn.isOpen_inter_preimage hUo isOpen_compl_singleton
    have hud : DifferentiableOn ℂ u U₁ :=
      (hXd.mono Set.inter_subset_left).div (hYd.mono Set.inter_subset_left) fun z hz => hz.2
    have hwd : DifferentiableOn ℂ w U₁ :=
      (hZd.mono Set.inter_subset_left).div (hYd.mono Set.inter_subset_left) fun z hz => hz.2
    have hqd : DifferentiableOn ℂ q U₁ :=
      ((differentiableOn_const 1).sub ((hud.const_mul a₄).mul hwd)).sub ((hwd.pow 2).const_mul a₆)
    set V := U₁ ∩ q ⁻¹' {0}ᶜ
    have hVo : IsOpen V := hqd.continuousOn.isOpen_inter_preimage hU₁o isOpen_compl_singleton
    have hz₀V : z₀ ∈ V := ⟨⟨hzU, hY0⟩, by simp [q, u, w, hX0, hZ0]⟩
    have hVU₁ : V ⊆ U₁ := Set.inter_subset_left
    have hrel : ∀ z' ∈ V, w z' * q z' = u z' ^ 3 := by
      intro z' hz'
      have hY' : Y z' ≠ 0 := hz'.1.2
      have h := hhom z' hz'.1.1
      have key : w z' * q z' - u z' ^ 3 =
          (Y z' ^ 2 * Z z' - (X z' ^ 3 + a₄ * X z' * Z z' ^ 2 + a₆ * Z z' ^ 3)) / Y z' ^ 3 := by
        simp only [u, w, q]; field_simp; ring
      rw [h, sub_self, zero_div] at key
      exact sub_eq_zero.1 key
    refine ⟨V, hVo, hz₀V, fun z => -deriv u z + u z * deriv q z / (2 * q z), ?_, ?_⟩
    · have hu := hud.mono hVU₁
      have hq := hqd.mono hVU₁
      have hdu := hu.deriv hVo
      have hdq := hq.deriv hVo
      exact hdu.neg.add ((hu.mul hdq).div (hq.const_mul 2) fun z hz => mul_ne_zero two_ne_zero hz.2)
    · intro z hzV hξz _
      have hZz : Z z ≠ 0 := (hc z hzV.1.1).ne_zero_iff.1 hξz
      have hYz : Y z ≠ 0 := hzV.1.2
      have hqz : q z ≠ 0 := hzV.2
      have hwz : w z ≠ 0 := div_ne_zero hZz hYz
      have hV' : V ∈ 𝓝 z := hVo.mem_nhds hzV
      have hU₁' : U₁ ∈ 𝓝 z := hU₁o.mem_nhds hzV.1
      have hu' := (hud.differentiableAt hU₁').hasDerivAt
      have hw' := (hwd.differentiableAt hU₁').hasDerivAt
      have hq' := (hqd.differentiableAt hU₁').hasDerivAt
      have hder : deriv w z * q z + w z * deriv q z = 3 * u z ^ 2 * deriv u z := by
        have d1 := hw'.mul hq'
        have d2 := hasDerivAt_pow_comp 3 hu'
        have heq : (fun z => u z ^ 3) =ᶠ[𝓝 z] fun z => w z * q z :=
          Filter.eventually_of_mem hV' fun z' hz' => (hrel z' hz').symm
        have := (d2.congr_of_eventuallyEq heq.symm).unique d1
        rw [← this]; push_cast; ring
      have hZev : ∀ᶠ z' in 𝓝 z, Z z' ≠ 0 :=
        (hZd.differentiableAt (hUo.mem_nhds hzV.1.1)).continuousAt.eventually_ne hZz
      have hxe : xc ξ =ᶠ[𝓝 z] fun z' => u z' / w z' := by
        filter_upwards [hV', hZev] with z' hz'V hz'Z
        have hξ' : ξ z' ≠ 0 := (hc z' hz'V.1.1).ne_zero_iff.2 hz'Z
        rw [xc, ((hc z' hz'V.1.1).coords hξ').1]
        have hY' : Y z' ≠ 0 := hz'V.1.2
        simp only [u, w]; field_simp
      have hyz' : yc ξ z = 1 / w z := by
        rw [yc, ((hc z hzV.1.1).coords hξz).2]; simp only [w]; field_simp
      have hdx : deriv (xc ξ) z = (deriv u z * w z - u z * deriv w z) / w z ^ 2 := by
        rw [hxe.deriv_eq]; exact (hu'.div hw' hwz).deriv
      rw [hdx, hyz']
      have key : -deriv u z + u z * deriv q z / (2 * q z) -
          (deriv u z * w z - u z * deriv w z) / w z ^ 2 / (2 * (1 / w z)) =
          (-3 * deriv u z * (w z * q z) + u z * (deriv w z * q z + w z * deriv q z)) /
            (2 * q z * w z) := by
        field_simp; ring
      rw [hrel z hzV, hder, show -3 * deriv u z * u z ^ 3 + u z * (3 * u z ^ 2 * deriv u z) = 0 by ring,
        zero_div] at key
      exact sub_eq_zero.1 key
  · by_cases hy₀ : yc ξ z₀ = 0
    · set f' : ℂ → ℂ := fun z => 3 * xc ξ z ^ 2 + (-L₀.g₂ / 4)
      have hf'd : DifferentiableOn ℂ f' {z | ξ z ≠ 0} :=
        ((hxd.pow 2).const_mul 3).add (differentiableOn_const _)
      set V := {z | ξ z ≠ 0} ∩ f' ⁻¹' {0}ᶜ
      have hVo : IsOpen V := hf'd.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
      have hz₀V : z₀ ∈ V := by
        refine ⟨hz₀, cubic_deriv_ne L₀ ?_⟩
        have := yc_sq L₀ hz₀
        rw [hy₀] at this
        linear_combination -this
      refine ⟨V, hVo, hz₀V, fun z => deriv (yc ξ) z / f' z, ?_, ?_⟩
      · exact ((hyd.deriv hΩ).mono Set.inter_subset_left).div (hf'd.mono Set.inter_subset_left)
          fun z hz => hz.2
      · intro z hzV hξz hyz
        have hf'z : f' z ≠ 0 := hzV.2
        have hΩ' : {z | ξ z ≠ 0} ∈ 𝓝 z := hΩ.mem_nhds hξz
        have hx' := (hxd.differentiableAt hΩ').hasDerivAt
        have hy' := (hyd.differentiableAt hΩ').hasDerivAt
        have hd : 2 * yc ξ z * deriv (yc ξ) z = f' z * deriv (xc ξ) z := by
          have d1 := hasDerivAt_pow_comp 2 hy'
          have d2 := ((hasDerivAt_pow_comp 3 hx').add (hx'.const_mul (-L₀.g₂ / 4))).add_const
            (-L₀.g₃ / 4)
          have heq : (fun z => yc ξ z ^ 2) =ᶠ[𝓝 z]
              fun z => xc ξ z ^ 3 + (-L₀.g₂ / 4) * xc ξ z + (-L₀.g₃ / 4) :=
            Filter.eventually_of_mem hΩ' fun z' hz' => yc_sq L₀ hz'
          have := (d1.congr_of_eventuallyEq heq.symm).unique d2
          simp only [f']
          push_cast at this
          linear_combination this
        have key : deriv (yc ξ) z / f' z - deriv (xc ξ) z / (2 * yc ξ z) =
            (2 * yc ξ z * deriv (yc ξ) z - f' z * deriv (xc ξ) z) / (f' z * (2 * yc ξ z)) := by
          field_simp
        rw [hd, sub_self, zero_div] at key
        exact sub_eq_zero.1 key
    · set V := {z | ξ z ≠ 0} ∩ yc ξ ⁻¹' {0}ᶜ
      have hVo : IsOpen V := hyd.continuousOn.isOpen_inter_preimage hΩ isOpen_compl_singleton
      refine ⟨V, hVo, ⟨hz₀, hy₀⟩, fun z => deriv (xc ξ) z / (2 * yc ξ z), ?_, fun z _ _ _ => rfl⟩
      exact ((hxd.deriv hΩ).mono Set.inter_subset_left).div
        ((hyd.mono Set.inter_subset_left).const_mul 2) fun z hz => mul_ne_zero two_ne_zero hz.2

/-- Gluing local holomorphic extensions across a set with dense complement. -/
theorem exists_entire_of_local {G : Set ℂ} (hG : Dense G) (φ : ℂ → ℂ)
    (hloc : ∀ z₀, ∃ V : Set ℂ, IsOpen V ∧ z₀ ∈ V ∧ ∃ ψ : ℂ → ℂ, DifferentiableOn ℂ ψ V ∧
      ∀ z ∈ V, z ∈ G → ψ z = φ z) :
    ∃ Φ : ℂ → ℂ, Differentiable ℂ Φ ∧ ∀ z ∈ G, Φ z = φ z := by
  choose V hVo hzV ψ hψ heq using hloc
  have agree : ∀ z₀ z, z ∈ V z₀ → ψ z₀ z = ψ z z := by
    intro z₀ z hz
    have c1 : ContinuousAt (ψ z₀) z := (hψ z₀).continuousOn.continuousAt ((hVo z₀).mem_nhds hz)
    have c2 : ContinuousAt (ψ z) z := (hψ z).continuousOn.continuousAt ((hVo z).mem_nhds (hzV z))
    set S := V z₀ ∩ V z ∩ G
    have hS : z ∈ closure S := by
      rw [mem_closure_iff]
      intro o ho hzo
      obtain ⟨y, hy⟩ := hG.inter_open_nonempty (o ∩ (V z₀ ∩ V z)) (ho.inter ((hVo z₀).inter (hVo z)))
        ⟨z, hzo, hz, hzV z⟩
      exact ⟨y, hy.1.1, ⟨hy.1.2, hy.2⟩⟩
    have hne : (𝓝[S] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hS
    refine tendsto_nhds_unique (l := 𝓝[S] z) (c1.tendsto.mono_left nhdsWithin_le_nhds)
      ((c2.tendsto.mono_left nhdsWithin_le_nhds).congr' ?_)
    filter_upwards [self_mem_nhdsWithin] with y hy
    rw [heq z y hy.1.2 hy.2, heq z₀ y hy.1.1 hy.2]
  refine ⟨fun z => ψ z z, fun z₀ => ?_, fun z hz => heq z z (hzV z) hz⟩
  have hev : (fun z => ψ z z) =ᶠ[𝓝 z₀] ψ z₀ :=
    Filter.eventually_of_mem ((hVo z₀).mem_nhds (hzV z₀)) fun z hz => (agree z₀ z hz).symm
  exact ((hψ z₀).differentiableAt ((hVo z₀).mem_nhds (hzV z₀))).congr_of_eventuallyEq hev

/-- **Liouville for lattice-periodic entire functions.** -/
theorem eq_const_of_periodic (L : PeriodPair) {Φ : ℂ → ℂ} (hd : Differentiable ℂ Φ)
    (hper : ∀ z, ∀ l ∈ L.lattice, Φ (z + l) = Φ z) (z : ℂ) : Φ z = Φ 0 :=
  hd.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice Φ hd.continuous fun z w hw => hper z w hw).isBounded z 0


theorem affine_holo {ξ : ℂ → W.toAffine.Point} (hh : IsHolomorphicMap W ξ) (z₀ : ℂ) (hz : ξ z₀ ≠ 0) :
    ∃ U : Set ℂ, IsOpen U ∧ z₀ ∈ U ∧ ∃ X Y : ℂ → ℂ, DifferentiableOn ℂ X U ∧ DifferentiableOn ℂ Y U ∧
      ∀ z ∈ U, ∃ h : W.toAffine.Nonsingular (X z) (Y z), ξ z = .some (X z) (Y z) h :=
  ⟨{z | ξ z ≠ 0}, isOpen_ne_zero hh, hz, xc ξ, yc ξ, differentiableOn_xc hh, differentiableOn_yc hh,
    fun _ hz => eq_some_of_ne_zero hz⟩

theorem IsHolomorphicMap.comp_affine {ξ : ℂ → W.toAffine.Point} (h : IsHolomorphicMap W ξ) (α β : ℂ) :
    IsHolomorphicMap W (fun z => ξ (α * z + β)) := by
  intro z₀
  obtain ⟨U, X, Y, Z, hz, hUo, hX, hY, hZ, hc⟩ := h (α * z₀ + β)
  have hAd : Differentiable ℂ fun z : ℂ => α * z + β := (differentiable_id.const_mul α).add_const β
  refine ⟨(fun z => α * z + β) ⁻¹' U, fun z => X (α * z + β), fun z => Y (α * z + β),
    fun z => Z (α * z + β), hz, hUo.preimage hAd.continuous,
    hX.comp hAd.differentiableOn fun z hz => hz, hY.comp hAd.differentiableOn fun z hz => hz,
    hZ.comp hAd.differentiableOn fun z hz => hz, fun z hz => hc _ hz⟩

/-- A local holomorphic lift through the Weierstrass map (hcm-dict's `exists_local_lift`, which is adapted from the
vendored FLT proof `kw_surgehgf4_hH2d_…`, Apache-2.0), for a surjective holomorphic `ξ`; also records
`G z ∉ L₀` and `℘'(G z) ≠ 0` on the ball. -/
theorem exists_local_lift' (L₀ : PeriodPair)
    (ξ : ℂ → L₀.weierstrassCurve.toAffine.Point) (hsurj : Function.Surjective ξ)
    (hh : IsHolomorphicMap L₀.weierstrassCurve ξ) :
    ∃ z₁ : ℂ, ∃ r > 0, ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Metric.ball z₁ r) ∧
      (∀ z ∈ Metric.ball z₁ r, L₀.toPoint L₀.discriminant_ne_zero (G z) = ξ z) ∧
      ∀ z ∈ Metric.ball z₁ r, G z ∉ L₀.lattice ∧ ℘'[L₀] (G z) ≠ 0 := by
  set w₀ := L₀.ω₁ / 4 with hw₀def
  have hw₀Λ : w₀ ∉ L₀.lattice := ZInQ.Contrib.HCMDict.omega_div_four_notMem L₀
  have hder' : ℘'[L₀] w₀ ≠ 0 := ZInQ.Contrib.HCMDict.derivWeierstrassP_omega_div_four_ne L₀
  obtain ⟨z₀, hz₀⟩ := hsurj (L₀.toPoint L₀.discriminant_ne_zero w₀)
  have hξz₀ : ξ z₀ ≠ 0 := by
    rw [hz₀, L₀.toPoint_of_notMem _ hw₀Λ]; exact Point.some_ne_zero _
  obtain ⟨U, hUo, hz₀U, X, Y, hXd, hYd, hcoord⟩ := affine_holo hh z₀ hξz₀
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
  have hevD : ∀ᶠ z in 𝓝 z₀, ℘'[L₀] (G z) ≠ 0 := by
    have hP'cont : ContinuousAt ℘'[L₀] (G z₀) := by
      rw [hGz₀]; exact (L₀.analyticOnNhd_derivWeierstrassP w₀ hw₀Λ).continuousAt
    exact (hP'cont.comp hGcont).eventually (isOpen_ne.mem_nhds (by rw [Function.comp_apply, hGz₀]; exact hder'))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.mp
    ((((((hevΛ.and hevR).and hevψd).and hevXd).and hevU).and hevSgn).and hevD)
  refine ⟨z₀, r, hr, G, fun z hz => ?_, fun z hz => ?_, fun z hz => ⟨(hball z hz).1.1.1.1.1.1, (hball z hz).2⟩⟩
  · obtain ⟨⟨⟨⟨⟨⟨-, -⟩, hψd⟩, hXdz⟩, -⟩, -⟩, -⟩ := hball z hz
    exact (hψd.comp z hXdz).differentiableWithinAt
  · obtain ⟨⟨⟨⟨⟨⟨hGzΛ, hPGz⟩, -⟩, -⟩, hzU⟩, hsgn⟩, -⟩ := hball z hz
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



/-- **The Weierstrass-map step, proved.** A holomorphic map `ξ : ℂ → E_{L₀}(ℂ) ⊂ ℙ²(ℂ)` inducing a bijection
`ℂ/L → E_{L₀}(ℂ)` with `ξ(0) = O` is `z ↦ ξ_{L₀}(αz)` with `L₀ = αL`. Proof: `x'/(2y)` (the pull-back of the
invariant differential) extends to an entire `L`-periodic function, hence is a constant `α` (Liouville); a local
lift `g` through `ξ_{L₀}` has `g' = α`, so `ξ = ξ_{L₀}(α · + β)` near a point, then on the complement of a countable
set (identity theorem) and everywhere (homogeneous coordinates); `ξ(0) = O` gives `β ∈ L₀`. -/
theorem eq_toPoint_of_holo (L₀ L : PeriodPair) (ξ : ℂ → L₀.weierstrassCurve.toAffine.Point)
    (hb : InducesBij L₀.weierstrassCurve L.lattice ξ) (hh : IsHolomorphicMap _ ξ) (h0 : ξ 0 = 0) :
    ∃ α : ℂ, T5Glue.IsScale L₀ L α ∧ ∀ z, ξ z = L₀.toPoint L₀.discriminant_ne_zero (α * z) := by
  set D₀ := L₀.discriminant_ne_zero
  have hU := L₀.isUniformization_toPoint D₀
  have hker : ∀ z, ξ z = 0 ↔ z ∈ L.lattice := fun z =>
    ⟨fun h => by simpa using hb.2.1 z 0 (h.trans h0.symm), fun h => by simpa [h0] using hb.1 0 z h⟩
  have hLc : ∀ M : PeriodPair, (M.lattice : Set ℂ).Countable := fun M => by
    have : Countable M.lattice := Countable.of_equiv _ M.latticeEquivProd.toEquiv.symm
    exact Set.countable_coe_iff.1 this
  set G : Set ℂ := {z | ξ z ≠ 0 ∧ yc ξ z ≠ 0} with hGdef
  -- the bad set `ξ⁻¹(O) ∪ ξ⁻¹(E[2] ∖ O)` is countable
  have hBc : Gᶜ.Countable := by
    set p : Polynomial ℂ := Polynomial.X ^ 3 +
      (Polynomial.C (-L₀.g₂ / 4) * Polynomial.X + Polynomial.C (-L₀.g₃ / 4))
    have hp0 : p ≠ 0 :=
      (Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le (by norm_num))).ne_zero
    have hR := Polynomial.finite_setOfPred_isRoot hp0
    have hsub : Gᶜ ⊆ (L.lattice : Set ℂ) ∪
        ⋃ x ∈ {x | p.IsRoot x}, {z | ξ z ≠ 0 ∧ yc ξ z = 0 ∧ xc ξ z = x} := by
      intro z hz
      by_cases hξ : ξ z = 0
      · exact Or.inl ((hker z).1 hξ)
      · have hy : yc ξ z = 0 := by
          by_contra hy; exact hz ⟨hξ, hy⟩
        refine Or.inr (Set.mem_iUnion₂.2 ⟨xc ξ z, ?_, hξ, hy, rfl⟩)
        have := yc_sq L₀ hξ
        rw [hy] at this
        simp only [Set.mem_ofPred_eq, Polynomial.IsRoot, p, Polynomial.eval_add, Polynomial.eval_pow,
          Polynomial.eval_X, Polynomial.eval_mul, Polynomial.eval_C]
        linear_combination -this
    refine Set.Countable.mono hsub ((hLc L).union (hR.countable.biUnion fun x _ => ?_))
    by_cases hne : {z | ξ z ≠ 0 ∧ yc ξ z = 0 ∧ xc ξ z = x}.Nonempty
    · obtain ⟨w, hw⟩ := hne
      refine ((hLc L).image (· + w)).mono fun z (hz : z ∈ {z | ξ z ≠ 0 ∧ yc ξ z = 0 ∧ xc ξ z = x}) =>
        (⟨z - w, ?_, sub_add_cancel z w⟩ : z ∈ (· + w) '' (L.lattice : Set ℂ))
      apply hb.2.1
      obtain ⟨h1, e1⟩ := eq_some_of_ne_zero hz.1
      obtain ⟨h2, e2⟩ := eq_some_of_ne_zero hw.1
      rw [e1, e2, Point.some.injEq]
      exact ⟨hz.2.2.trans hw.2.2.symm, hz.2.1.trans hw.2.1.symm⟩
    · rw [Set.not_nonempty_iff_eq_empty.1 hne]; exact Set.countable_empty
  have hGd : Dense G := by
    have := hBc.dense_compl ℝ; rwa [compl_compl] at this
  -- `x'/(2y)` extends to an entire function `Φ`
  obtain ⟨Φ, hΦd, hΦG⟩ := exists_entire_of_local hGd (fun z => deriv (xc ξ) z / (2 * yc ξ z))
    fun z₀ => by
      obtain ⟨V, hVo, hz₀V, ψ, hψd, hψ⟩ := exists_local_ext L₀ hh z₀
      exact ⟨V, hVo, hz₀V, ψ, hψd, fun z hz hzG => hψ z hz hzG.1 hzG.2⟩
  have hxper : ∀ l ∈ L.lattice, ∀ z, xc ξ (z + l) = xc ξ z := fun l hl z => by
    simp only [xc, hb.1 z l hl]
  have hyper : ∀ l ∈ L.lattice, ∀ z, yc ξ (z + l) = yc ξ z := fun l hl z => by
    simp only [yc, hb.1 z l hl]
  have hper : ∀ z, ∀ l ∈ L.lattice, Φ (z + l) = Φ z := by
    intro z l hl
    have := Continuous.ext_on hGd (hΦd.continuous.comp (continuous_id.add continuous_const : Continuous fun x : ℂ => x + l)) hΦd.continuous
      (fun z hz => by
        have hzl : z + l ∈ G := by
          refine ⟨?_, ?_⟩
          · rw [hb.1 z l hl]; exact hz.1
          · rw [hyper l hl]; exact hz.2
        show Φ (z + l) = Φ z
        rw [hΦG _ hzl, hΦG z hz, hyper l hl]
        congr 1
        rw [← deriv_comp_add_const]
        congr 1
        funext x; exact hxper l hl x)
    exact congrFun this z
  set α := Φ 0 with hαdef
  have hΦc : ∀ z, Φ z = α := eq_const_of_periodic L hΦd hper
  -- a local lift `g` with `g' = α`
  obtain ⟨z₁, r, hr, g, hgd, hgeq, hgΛ⟩ := exists_local_lift' L₀ ξ hb.2.2 hh
  have hball : ∀ z ∈ Metric.ball z₁ r,
      ξ z ≠ 0 ∧ xc ξ z = ℘[L₀] (g z) ∧ yc ξ z = ℘'[L₀] (g z) / 2 := by
    intro z hz
    rw [xc, yc, ← hgeq z hz, L₀.toPoint_of_notMem _ (hgΛ z hz).1]
    exact ⟨Point.some_ne_zero _, rfl, rfl⟩
  have hgder : ∀ z ∈ Metric.ball z₁ r, deriv g z = α := by
    intro z hz
    have hzb : Metric.ball z₁ r ∈ 𝓝 z := Metric.isOpen_ball.mem_nhds hz
    have hgd' := (hgd.differentiableAt hzb).hasDerivAt
    have hP : HasDerivAt ℘[L₀] (℘'[L₀] (g z)) (g z) := by
      rw [← PeriodPair.deriv_weierstrassP]
      exact (L₀.analyticOnNhd_weierstrassP _ (hgΛ z hz).1).differentiableAt.hasDerivAt
    have hcomp := HasDerivAt.comp (h := g) z hP hgd'
    have hxe : xc ξ =ᶠ[𝓝 z] fun w => ℘[L₀] (g w) :=
      Filter.eventually_of_mem hzb fun w hw => (hball w hw).2.1
    have hdx : deriv (xc ξ) z = ℘'[L₀] (g z) * deriv g z := by
      rw [hxe.deriv_eq]; exact hcomp.deriv
    have hP'z := (hgΛ z hz).2
    have hzG : z ∈ G := ⟨(hball z hz).1, by rw [(hball z hz).2.2]; exact div_ne_zero hP'z two_ne_zero⟩
    have := hΦG z hzG
    rw [hΦc z, hdx, (hball z hz).2.2] at this
    rw [this]; field_simp
  set β := g z₁ - α * z₁ with hβdef
  have hglin : ∀ z ∈ Metric.ball z₁ r, g z = α * z + β := by
    intro z hz
    have hk : ∀ s ∈ Metric.ball z₁ r, HasDerivAt (fun s => g s - α * s) 0 s := by
      intro s hs
      have h1 : HasDerivAt g α s := by
        rw [← hgder s hs]
        exact (hgd.differentiableAt (Metric.isOpen_ball.mem_nhds hs)).hasDerivAt
      have h2 : HasDerivAt (fun s => α * s) α s := by simpa using (hasDerivAt_id s).const_mul α
      have := h1.sub h2
      rwa [sub_self] at this
    have := IsOpen.is_const_of_deriv_eq_zero (f := fun s => g s - α * s) Metric.isOpen_ball
      (convex_ball z₁ r).isPreconnected
      (fun s hs => (hk s hs).differentiableAt.differentiableWithinAt)
      (fun s hs => (hk s hs).deriv) hz (Metric.mem_ball_self hr)
    rw [hβdef]; linear_combination this
  have hz₁b := Metric.mem_ball_self hr (x := z₁)
  -- `α ≠ 0`
  have hα0 : α ≠ 0 := by
    intro hα
    obtain ⟨ε, hε, hsmall⟩ := ZInQ.Contrib.HCMDict.exists_lattice_small L
    set t : ℂ := ((min r ε / 2 : ℝ) : ℂ)
    have ht0 : t ≠ 0 := by
      simp only [t, ne_eq, Complex.ofReal_eq_zero]; positivity
    have htn : ‖t‖ = min r ε / 2 := by
      simp only [t, Complex.norm_real, Real.norm_eq_abs]
      exact abs_of_pos (by positivity)
    have htr : z₁ + t ∈ Metric.ball z₁ r := by
      simp only [Metric.mem_ball, dist_self_add_left, htn]
      linarith [min_le_left r ε]
    have hpt : ξ (z₁ + t) = ξ z₁ := by
      rw [← hgeq _ htr, ← hgeq _ hz₁b, hglin _ htr, hglin _ hz₁b, hα, zero_mul, zero_mul]
    have hl := hb.2.1 _ _ hpt
    rw [add_sub_cancel_left] at hl
    exact ht0 (hsmall t hl (by rw [htn]; linarith [min_le_right r ε]))
  set η : ℂ → L₀.weierstrassCurve.toAffine.Point := fun z => L₀.toPoint D₀ (α * z + β) with hηdef
  -- the complement of a countable closed set
  have hAc : Continuous fun z : ℂ => α * z + β := (continuous_const.mul continuous_id).add continuous_const
  set C : Set ℂ := (L.lattice : Set ℂ) ∪ (fun z => α * z + β) ⁻¹' (L₀.lattice : Set ℂ)
  have hCc : C.Countable := (hLc L).union (Set.Countable.mono
    (fun z (hz : z ∈ (fun z => α * z + β) ⁻¹' (L₀.lattice : Set ℂ)) =>
      (⟨α * z + β, hz, by field_simp; ring⟩ : z ∈ (fun l => (l - β) / α) '' (L₀.lattice : Set ℂ)))
    ((hLc L₀).image _))
  have hCcl : IsClosed C := L.isClosed_lattice.union (L₀.isClosed_lattice.preimage hAc)
  have hDo : IsOpen Cᶜ := hCcl.isOpen_compl
  have hDconn : IsPreconnected Cᶜ :=
    (hCc.isPathConnected_compl_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)).isConnected.isPreconnected
  have hDdense : Dense Cᶜ := hCc.dense_compl ℝ
  have hDΩ : ∀ z ∈ Cᶜ, ξ z ≠ 0 ∧ α * z + β ∉ L₀.lattice := fun z hz => by
    simp only [C, Set.mem_compl_iff, Set.mem_union, Set.mem_preimage, not_or, SetLike.mem_coe] at hz
    exact ⟨fun h => hz.1 ((hker z).1 h), hz.2⟩
  have hz₁D : z₁ ∈ Cᶜ := by
    simp only [C, Set.mem_compl_iff, Set.mem_union, Set.mem_preimage, not_or, SetLike.mem_coe]
    exact ⟨fun h => (hball z₁ hz₁b).1 ((hker z₁).2 h), by
      rw [← hglin z₁ hz₁b]; exact (hgΛ z₁ hz₁b).1⟩
  have hAa : ∀ z : ℂ, AnalyticAt ℂ (fun z : ℂ => α * z + β) z := fun z =>
    (analyticAt_const.mul analyticAt_id).add analyticAt_const
  have hxa : AnalyticOnNhd ℂ (xc ξ) Cᶜ :=
    ((differentiableOn_xc hh).mono fun z hz => (hDΩ z hz).1).analyticOnNhd hDo
  have hya : AnalyticOnNhd ℂ (yc ξ) Cᶜ :=
    ((differentiableOn_yc hh).mono fun z hz => (hDΩ z hz).1).analyticOnNhd hDo
  have hpa : AnalyticOnNhd ℂ (fun z => ℘[L₀] (α * z + β)) Cᶜ := fun z hz =>
    AnalyticAt.comp (f := fun z => α * z + β) (x := z) (L₀.analyticOnNhd_weierstrassP _ (hDΩ z hz).2) (hAa z)
  have hp'a : AnalyticOnNhd ℂ (fun z => ℘'[L₀] (α * z + β) / 2) Cᶜ := fun z hz =>
    (AnalyticAt.comp (f := fun z => α * z + β) (x := z)
      (L₀.analyticOnNhd_derivWeierstrassP _ (hDΩ z hz).2) (hAa z)).div_const (c := 2)
  have hb₁ : Metric.ball z₁ r ∈ 𝓝 z₁ := Metric.ball_mem_nhds z₁ hr
  have hxeq := hxa.eqOn_of_preconnected_of_eventuallyEq hpa hDconn hz₁D
    (Filter.eventually_of_mem hb₁ fun z hz => by rw [(hball z hz).2.1, hglin z hz])
  have hyeq := hya.eqOn_of_preconnected_of_eventuallyEq hp'a hDconn hz₁D
    (Filter.eventually_of_mem hb₁ fun z hz => by rw [(hball z hz).2.2, hglin z hz])
  have hξηD : ∀ z ∈ Cᶜ, ξ z = η z := by
    intro z hz
    obtain ⟨h, e⟩ := eq_some_of_ne_zero (hDΩ z hz).1
    rw [e, hηdef]
    simp only
    rw [L₀.toPoint_of_notMem _ (hDΩ z hz).2, Point.some.injEq]
    exact ⟨hxeq hz, hyeq hz⟩
  -- extension to all of `ℂ` through homogeneous coordinates
  have hηh : IsHolomorphicMap _ η :=
    (toPoint_isImmersion L₀).isHolomorphicMap.comp_affine α β
  have hξη : ∀ z, ξ z = η z := by
    intro z
    obtain ⟨U₁, X₁, Y₁, Z₁, hz1, hU1o, hX1, hY1, hZ1, hc1⟩ := hh z
    obtain ⟨U₂, X₂, Y₂, Z₂, hz2, hU2o, hX2, hY2, hZ2, hc2⟩ := hηh z
    have hOo : IsOpen (U₁ ∩ U₂) := hU1o.inter hU2o
    have hzcl : z ∈ closure (U₁ ∩ U₂ ∩ Cᶜ) := by
      rw [mem_closure_iff]
      intro o ho hzo
      obtain ⟨y, hy⟩ := hDdense.inter_open_nonempty (o ∩ (U₁ ∩ U₂)) (ho.inter hOo) ⟨z, hzo, hz1, hz2⟩
      exact ⟨y, hy.1.1, hy.1.2, hy.2⟩
    have zero_at : ∀ c : ℂ → ℂ, ContinuousOn c (U₁ ∩ U₂) → (∀ y ∈ U₁ ∩ U₂ ∩ Cᶜ, c y = 0) → c z = 0 := by
      intro c hc hcz
      have hcz' : ContinuousAt c z := hc.continuousAt (hOo.mem_nhds ⟨hz1, hz2⟩)
      have hne : (𝓝[U₁ ∩ U₂ ∩ Cᶜ] z).NeBot := mem_closure_iff_nhdsWithin_neBot.1 hzcl
      exact tendsto_nhds_unique (l := 𝓝[U₁ ∩ U₂ ∩ Cᶜ] z) (hcz'.tendsto.mono_left nhdsWithin_le_nhds)
        (tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun y hy => (hcz y hy).symm))
    have hcross : ∀ y ∈ U₁ ∩ U₂ ∩ Cᶜ, Y₁ y * Z₂ y - Z₁ y * Y₂ y = 0 ∧
        Z₁ y * X₂ y - X₁ y * Z₂ y = 0 ∧ X₁ y * Y₂ y - Y₁ y * X₂ y = 0 := by
      intro y hy
      have h2 := hc2 y hy.1.2
      rw [← hξηD y hy.2] at h2
      exact (hc1 y hy.1.1).cross_eq_zero h2
    have hc1' := hX1.continuousOn.mono (Set.inter_subset_left (t := U₂))
    have hc2' := hY1.continuousOn.mono (Set.inter_subset_left (t := U₂))
    have hc3' := hZ1.continuousOn.mono (Set.inter_subset_left (t := U₂))
    have hc4' := hX2.continuousOn.mono (Set.inter_subset_right (s := U₁))
    have hc5' := hY2.continuousOn.mono (Set.inter_subset_right (s := U₁))
    have hc6' := hZ2.continuousOn.mono (Set.inter_subset_right (s := U₁))
    have e0 := zero_at (fun y => Y₁ y * Z₂ y - Z₁ y * Y₂ y) ((hc2'.mul hc6').sub (hc3'.mul hc5'))
      fun y hy => (hcross y hy).1
    have e1 := zero_at (fun y => Z₁ y * X₂ y - X₁ y * Z₂ y) ((hc3'.mul hc4').sub (hc1'.mul hc6'))
      fun y hy => (hcross y hy).2.1
    exact (hc1 z hz1).eq_of_cross (hc2 z hz2) e0 e1
  -- `β ∈ L₀`
  have hβ : β ∈ L₀.lattice := by
    have := hξη 0
    rw [h0, hηdef] at this
    simp only [mul_zero, zero_add] at this
    exact hU.2.2 _ this.symm
  have hform : ∀ z, ξ z = L₀.toPoint D₀ (α * z) := fun z => by
    rw [hξη z, hηdef]
    simp only
    rw [hU.1, L₀.toPoint_of_mem _ hβ, add_zero]
  refine ⟨α, ⟨hα0, ?_⟩, hform⟩
  have hker' : ∀ z, z ∈ L.lattice ↔ α * z ∈ L₀.lattice := fun z => by
    rw [← hker, hform]
    exact ⟨hU.2.2 _, fun h => L₀.toPoint_of_mem _ h⟩
  ext x
  simp only [SetLike.mem_coe, Set.mem_smul_set, smul_eq_mul]
  constructor
  · intro hx
    refine ⟨α⁻¹ * x, (hker' _).2 ?_, ?_⟩
    · rwa [mul_inv_cancel_left₀ hα0]
    · rw [mul_inv_cancel_left₀ hα0]
  · rintro ⟨y, hy, rfl⟩
    exact (hker' y).1 hy

end Liouville

section LatticeSec

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise T5Glue

/-! ## §L. Local components at a rational prime `p` -/

/-- The places `v` of `K = ℚ(√−m)` above a rational prime `p` (the height-one primes containing `p`). -/
abbrev PlacesAbove (m : ℕ) [NeZero m] (p : ℕ) : Type :=
  {v : HeightOneSpectrum (𝓞 (QNeg m)) // (p : 𝓞 (QNeg m)) ∈ v.asIdeal}

/-- `K_p = K ⊗_ℚ ℚ_p`, in its standard model `∏_{v ∣ p} K_v`. -/
abbrev Kp (m : ℕ) [NeZero m] (p : ℕ) : Type :=
  (v : PlacesAbove m p) → v.1.adicCompletion (QNeg m)

variable {m : ℕ} [NeZero m]

/-- The `p`-component `x ↦ x_p` of a finite adele, `𝔸_{K,f} → K_p`. -/
def projP (p : ℕ) (x : AfK m) : Kp m p := fun v => x v.1

/-- The diagonal embedding `K → K_p`. -/
def diagP (p : ℕ) (k : QNeg m) : Kp m p := projP p (algebraMap (QNeg m) (AfK m) k)

/-- `𝔞_p = 𝔞 ⊗ ℤ_p ⊂ K_p`: the closure of a lattice `𝔞 ⊂ K` in `K_p` (for a finitely generated `ℤ`-module
`𝔞` this is the `ℤ_p`-module it generates, since `ℤ` is dense in `ℤ_p`). -/
def locLat (p : ℕ) (𝔞 : Set (QNeg m)) : Set (Kp m p) := closure (diagP p '' 𝔞)

/-- The `p`-component `s_p ∈ K_p^×` of an idele `s` of `K`. -/
def ideleComp (p : ℕ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : Kp m p := projP p (finPart s)

theorem continuous_projP (p : ℕ) : Continuous (projP (m := m) p) :=
  continuous_pi fun v => RestrictedProduct.continuous_eval v.1

theorem projP_mul (p : ℕ) (x y : AfK m) : projP p (x * y) = projP p x * projP p y := rfl

theorem projP_sub (p : ℕ) (x y : AfK m) : projP p (x - y) = projP p x - projP p y := rfl

theorem projP_one (p : ℕ) : projP p (1 : AfK m) = 1 := rfl

theorem finPart_mul_inv (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) : finPart s * finPart s⁻¹ = 1 := by
  rw [mul_comm]; exact finPart_inv_mul s

theorem ideleComp_mul_inv (p : ℕ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    ideleComp p s * ideleComp p s⁻¹ = 1 := by
  simp only [ideleComp, ← projP_mul, finPart_mul_inv, projP_one]

theorem ideleComp_inv_mul (p : ℕ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    ideleComp p s⁻¹ * ideleComp p s = 1 := by
  rw [mul_comm]; exact ideleComp_mul_inv p s

/-! ## §M. A lattice contains `N·𝓞_K` -/

theorem mem_of_kappa (L : PeriodPair) {𝔞 : Set (QNeg m)} (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞)
    (x : QNeg m) : x ∈ 𝔞 ↔ kappa m x ∈ L.lattice := by
  rw [← SetLike.mem_coe, h𝔞]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e⟩ => kappa_injective e ▸ hy⟩

theorem kappa_zsmul (n : ℤ) (x : QNeg m) : kappa m (n • x) = n • kappa m x := by
  rw [← kappaLin_apply, ← kappaLin_apply, map_zsmul]

/-- Every element of `K` has a nonzero integer multiple in a lattice `𝔞`. -/
theorem exists_nat_mul_mem (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (x : QNeg m) :
    ∃ n : ℕ, 0 < n ∧ ((n : ℤ) • x) ∈ 𝔞 := by
  have hm := mem_of_kappa L h𝔞
  obtain ⟨a₁, -, ha₁⟩ : L.ω₁ ∈ kappa m '' 𝔞 := h𝔞 ▸ L.ω₁_mem_lattice
  obtain ⟨a₂, -, ha₂⟩ : L.ω₂ ∈ kappa m '' 𝔞 := h𝔞 ▸ L.ω₂_mem_lattice
  have hind := LinearIndependent.pair_iff.1 L.indep
  have hk : ∀ c₁ c₂ : ℚ, kappa m ((c₁ : QNeg m) * a₁ + (c₂ : QNeg m) * a₂) =
      (c₁ : ℝ) • L.ω₁ + (c₂ : ℝ) • L.ω₂ := by
    intro c₁ c₂
    rw [← ha₁, ← ha₂, ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply]
    simp only [map_add, map_mul, map_ratCast, Complex.real_smul]
    push_cast; ring
  set p₁ := a₁.re; set q₁ := a₁.im; set p₂ := a₂.re; set q₂ := a₂.im
  have hdet : p₁ * q₂ - p₂ * q₁ ≠ 0 := by
    intro hd
    have e1 : (q₂ : QNeg m) * a₁ + ((-q₁ : ℚ) : QNeg m) * a₂ = ((p₁ * q₂ - p₂ * q₁ : ℚ) : QNeg m) := by
      ext <;> simp [p₁, q₁, p₂, q₂] <;> ring
    have h1 := hk q₂ (-q₁)
    rw [e1, hd] at h1
    simp only [Rat.cast_zero, show kappa m 0 = 0 by simp [kappa]] at h1
    obtain ⟨hq₂, hq₁⟩ := hind _ _ h1.symm
    have hq₂' : q₂ = 0 := by exact_mod_cast hq₂
    have hq₁' : q₁ = 0 := by have := hq₁; push_cast at this; exact_mod_cast neg_eq_zero.1 this
    have e2 : (p₂ : QNeg m) * a₁ + ((-p₁ : ℚ) : QNeg m) * a₂ = ((0 : ℚ) : QNeg m) := by
      ext <;> simp [p₁, q₁, p₂, q₂, hq₁', hq₂'] <;> ring
    have h2 := hk p₂ (-p₁)
    rw [e2] at h2
    simp only [Rat.cast_zero, show kappa m 0 = 0 by simp [kappa]] at h2
    obtain ⟨hp₂, hp₁⟩ := hind _ _ h2.symm
    have hp₁' : p₁ = 0 := by have := hp₁; push_cast at this; exact_mod_cast neg_eq_zero.1 this
    have ha₁0 : a₁ = 0 := by
      ext
      · exact hp₁'
      · exact hq₁'
    have := hind 1 0 (by rw [← ha₁, ha₁0]; simp [kappa])
    exact one_ne_zero this.1
  set r : ℚ := (x.re * q₂ - x.im * p₂) / (p₁ * q₂ - p₂ * q₁)
  set t : ℚ := (p₁ * x.im - q₁ * x.re) / (p₁ * q₂ - p₂ * q₁)
  have hdet' : a₂.im * a₁.re - a₂.re * a₁.im ≠ 0 := by
    intro h; apply hdet; simp only [p₁, q₁, p₂, q₂]; linear_combination h
  have hx : (r : QNeg m) * a₁ + (t : QNeg m) * a₂ = x := by
    ext
    · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_ratCast,
        QuadraticAlgebra.im_ratCast, r, t, p₁, q₁, p₂, q₂, Rat.cast_id] at hdet ⊢
      field_simp; ring
    · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_ratCast,
        QuadraticAlgebra.im_ratCast, r, t, p₁, q₁, p₂, q₂, Rat.cast_id] at hdet ⊢
      field_simp; ring
  refine ⟨r.den * t.den, Nat.mul_pos r.den_pos t.den_pos, ?_⟩
  rw [hm, ← hx, kappa_zsmul, hk]
  have er : ((r.den * t.den : ℕ) : ℤ) • ((r : ℝ) • L.ω₁) = ((r.num * t.den : ℤ) : ℂ) * L.ω₁ := by
    rw [zsmul_eq_mul, Complex.real_smul, ← mul_assoc]
    congr 1
    have : (r : ℝ) = r.num / r.den := by exact_mod_cast (Rat.num_div_den r).symm
    rw [this]; push_cast; field_simp
  have et : ((r.den * t.den : ℕ) : ℤ) • ((t : ℝ) • L.ω₂) = ((t.num * r.den : ℤ) : ℂ) * L.ω₂ := by
    rw [zsmul_eq_mul, Complex.real_smul, ← mul_assoc]
    congr 1
    have : (t : ℝ) = t.num / t.den := by exact_mod_cast (Rat.num_div_den t).symm
    rw [this]; push_cast; field_simp
  rw [smul_add, er, et]
  exact PeriodPair.mem_lattice.2 ⟨_, _, rfl⟩

/-- A lattice `𝔞 ⊂ K` (with `κ𝔞` a period lattice) contains `N·𝓞_K` for some `N > 0`. -/
theorem exists_nat_mul_integers_mem (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) :
    ∃ N : ℕ, 0 < N ∧ ∀ y : 𝓞 (QNeg m), (N : QNeg m) * y ∈ 𝔞 := by
  have hm := mem_of_kappa L h𝔞
  obtain ⟨n₁, hn₁, h₁⟩ := exists_nat_mul_mem L h𝔞 1
  obtain ⟨n₂, hn₂, h₂⟩ := exists_nat_mul_mem L h𝔞 QuadraticAlgebra.omega
  refine ⟨2 * n₁ * n₂, by positivity, fun y => ?_⟩
  obtain ⟨a, t, -, ha, ht, -⟩ := two_coords hsq y
  have hy : (2 : QNeg m) * (y : QNeg m) = (a : QNeg m) + (t : QNeg m) * QuadraticAlgebra.omega := by
    ext
    · simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, ha]
    · simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat, ht]
  have e : ((2 * n₁ * n₂ : ℕ) : QNeg m) * (y : QNeg m) =
      (a * n₂ : ℤ) • ((n₁ : ℤ) • (1 : QNeg m)) + (t * n₁ : ℤ) • ((n₂ : ℤ) • QuadraticAlgebra.omega) := by
    have : ((2 * n₁ * n₂ : ℕ) : QNeg m) * (y : QNeg m) = (n₁ * n₂ : QNeg m) * (2 * (y : QNeg m)) := by
      push_cast; ring
    rw [this, hy]
    simp only [zsmul_eq_mul]; push_cast; ring
  rw [e, hm, kappa_add, kappa_zsmul (a * n₂), kappa_zsmul (t * n₁)]
  exact add_mem (zsmul_mem ((hm _).1 h₁) _) (zsmul_mem ((hm _).1 h₂) _)

/-- `𝔞 = κ⁻¹(L)` as a `ℤ`-submodule. -/
theorem eq_kappaComap (L : PeriodPair) {𝔞 : Set (QNeg m)} (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) :
    𝔞 = ((kappaComap (m := m) L.lattice : Submodule ℤ (QNeg m)) : Set (QNeg m)) := by
  rw [coe_kappaComap]; ext x; exact mem_of_kappa L h𝔞 x

/-- **`𝔞̂` is open** in `𝔸_{K,f}` for a lattice `𝔞` (it contains `N·𝒪̂_K`). -/
theorem isOpen_latHat (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) : IsOpen (latHat m 𝔞) := by
  obtain ⟨N, hN, hN𝔞⟩ := exists_nat_mul_integers_mem hsq L h𝔞
  have e := eq_kappaComap L h𝔞
  set M := kappaComap (m := m) L.lattice
  rw [e] at hN𝔞 ⊢
  rw [latHat_eq_closure]
  set H := (M.toAddSubgroup.map (algebraMap (QNeg m) (AfK m)).toAddMonoidHom).topologicalClosure
  refine AddSubgroup.isOpen_of_mem_nhds H (g := 0) ?_
  have hN0 : (N : QNeg m) ≠ 0 := by exact_mod_cast hN.ne'
  set W : Set (AfK m) := (fun z => algebraMap (QNeg m) (AfK m) ((N : QNeg m)⁻¹) * z) ⁻¹'
    (FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m) : Set (AfK m))
  have hWo : IsOpen W := (FiniteAdeleRing.isOpen_integralAdeles (𝓞 (QNeg m)) (QNeg m)).preimage
    (continuous_const.mul continuous_id)
  have h0W : (0 : AfK m) ∈ W := by
    show algebraMap (QNeg m) (AfK m) ((N : QNeg m)⁻¹) * 0 ∈
      (FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m) : Set (AfK m))
    rw [mul_zero]; exact Subalgebra.zero_mem _
  refine Filter.mem_of_superset (hWo.mem_nhds h0W) fun z hz => ?_
  have hcl := FiniteAdeleRing.closure_range_algebraMap (𝓞 (QNeg m)) (QNeg m)
  have hz' := (Set.ext_iff.1 hcl (algebraMap (QNeg m) (AfK m) ((N : QNeg m)⁻¹) * z)).2 hz
  have hcont : Continuous fun w : AfK m => algebraMap (QNeg m) (AfK m) (N : QNeg m) * w :=
    continuous_const.mul continuous_id
  have h1 := image_closure_subset_closure_image hcont ⟨_, hz', rfl⟩
  have hzeq : algebraMap (QNeg m) (AfK m) (N : QNeg m) *
      (algebraMap (QNeg m) (AfK m) ((N : QNeg m)⁻¹) * z) = z := by
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hN0, map_one, one_mul]
  beta_reduce at h1
  rw [hzeq] at h1
  rw [AddSubgroup.topologicalClosure_coe]
  refine closure_mono ?_ h1
  rintro _ ⟨_, ⟨r, rfl⟩, rfl⟩
  refine ⟨(N : QNeg m) * (r : QNeg m), hN𝔞 r, ?_⟩
  show algebraMap (QNeg m) (AfK m) ((N : QNeg m) * (r : QNeg m)) = _
  rw [map_mul]; rfl

/-! ## §N. `(s⁻¹𝔞)_p = s_p⁻¹ 𝔞_p` -/

/-- **The localization form of `s⁻¹𝔞`**, preimage version: for every lattice `𝔞 ⊂ K`, idele `s` and `p`,
`(K ∩ s_f⁻¹𝔞̂)_p = {y ∈ K_p : s_p y ∈ 𝔞_p}`. -/
theorem locLat_sInvLat_eq_preimage (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (p : ℕ) :
    locLat p (sInvLat m s 𝔞) = {y | ideleComp p s * y ∈ locLat p 𝔞} := by
  set U : Set (AfK m) := {x | finPart s * x ∈ latHat m 𝔞} with hUdef
  have hUo : IsOpen U := (isOpen_latHat hsq L h𝔞).preimage (continuous_const.mul continuous_id)
  have hproj : ∀ x ∈ latHat m 𝔞, projP p x ∈ locLat p 𝔞 := by
    intro x hx
    have h := image_closure_subset_closure_image (continuous_projP (m := m) p) ⟨x, hx, rfl⟩
    rw [Set.image_image] at h
    exact h
  apply Set.Subset.antisymm
  · have hcl : IsClosed {y : Kp m p | ideleComp p s * y ∈ locLat p 𝔞} :=
      isClosed_closure.preimage (continuous_const.mul continuous_id)
    refine closure_minimal ?_ hcl
    rintro _ ⟨k, hk, rfl⟩
    show ideleComp p s * diagP p k ∈ locLat p 𝔞
    have := hproj _ hk
    rw [projP_mul] at this
    exact this
  · intro y hy
    rw [locLat, mem_closure_iff]
    intro W hWo hyW
    set c := ideleComp p s⁻¹
    have hW' : IsOpen {z : Kp m p | c * z ∈ W} := hWo.preimage (continuous_const.mul continuous_id)
    have hsy : c * (ideleComp p s * y) ∈ W := by rw [← mul_assoc, ideleComp_inv_mul, one_mul]; exact hyW
    obtain ⟨_, hz, ⟨a₀, ha₀, rfl⟩⟩ := mem_closure_iff.1 hy _ hW' hsy
    have hx₀U : finPart s⁻¹ * algebraMap (QNeg m) (AfK m) a₀ ∈ U := by
      show finPart s * (finPart s⁻¹ * algebraMap (QNeg m) (AfK m) a₀) ∈ latHat m 𝔞
      rw [← mul_assoc, finPart_mul_inv, one_mul]
      exact mem_latHat_of_mem ha₀
    have hx₀W : finPart s⁻¹ * algebraMap (QNeg m) (AfK m) a₀ ∈ projP p ⁻¹' W := by
      show projP p (finPart s⁻¹ * algebraMap (QNeg m) (AfK m) a₀) ∈ W
      rw [projP_mul]; exact hz
    obtain ⟨k, hk⟩ := (FiniteAdeleRing.denseRange_algebraMap (𝓞 (QNeg m)) (QNeg m)).exists_mem_open
      (((continuous_projP p).isOpen_preimage W hWo).inter hUo) ⟨_, hx₀W, hx₀U⟩
    exact ⟨diagP p k, hk.1, k, hk.2, rfl⟩

/-- **`(s⁻¹𝔞)_p = s_p⁻¹ 𝔞_p`** (Shimura's localization form of `s⁻¹𝔞`), for every lattice `𝔞 ⊂ K` (of any order),
every idele `s` and every `p`, where `s⁻¹𝔞 = sInvLat m s 𝔞 = K ∩ s_f⁻¹𝔞̂`. -/
theorem locLat_sInvLat (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) (p : ℕ) :
    locLat p (sInvLat m s 𝔞) = (fun x => ideleComp p s⁻¹ * x) '' locLat p 𝔞 := by
  rw [locLat_sInvLat_eq_preimage hsq L h𝔞 s p]
  ext y
  constructor
  · intro hy
    refine ⟨_, hy, ?_⟩
    show ideleComp p s⁻¹ * (ideleComp p s * y) = y
    rw [← mul_assoc, ideleComp_inv_mul, one_mul]
  · rintro ⟨x, hx, rfl⟩
    show ideleComp p s * (ideleComp p s⁻¹ * x) ∈ locLat p 𝔞
    rwa [← mul_assoc, ideleComp_mul_inv, one_mul]

/-- The two readings of "`v` represents `s⁻¹u`": `s_f v − u ∈ 𝔞̂` gives `v − s_p⁻¹u ∈ (s⁻¹𝔞)_p` for every `p`. -/
theorem rep_local_of_global (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) {u v : QNeg m}
    (h : finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u ∈ latHat m 𝔞) (p : ℕ) :
    diagP p v - ideleComp p s⁻¹ * diagP p u ∈ locLat p (sInvLat m s 𝔞) := by
  rw [locLat_sInvLat_eq_preimage hsq L h𝔞 s p]
  show ideleComp p s * (diagP p v - ideleComp p s⁻¹ * diagP p u) ∈ locLat p 𝔞
  have e : ideleComp p s * (diagP p v - ideleComp p s⁻¹ * diagP p u) =
      projP p (finPart s * algebraMap (QNeg m) (AfK m) v - algebraMap (QNeg m) (AfK m) u) := by
    rw [projP_sub, projP_mul, mul_sub, ← mul_assoc, ideleComp_mul_inv, one_mul]; rfl
  rw [e]
  have h' := image_closure_subset_closure_image (continuous_projP (m := m) p) ⟨_, h, rfl⟩
  rw [Set.image_image] at h'
  exact h'


/-! ## §O. `s⁻¹𝔞 = K ∩ s_f⁻¹𝔞̂` is a lattice -/

/-- `N·𝒪̂_K ⊆ 𝔞̂` when `N·𝒪_K ⊆ 𝔞`. -/
theorem natMul_integral_mem_latHat {𝔞 : Set (QNeg m)} {N : ℕ}
    (hN𝔞 : ∀ y : 𝓞 (QNeg m), (N : QNeg m) * y ∈ 𝔞) {z : AfK m}
    (hz : z ∈ FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m)) :
    algebraMap (QNeg m) (AfK m) (N : QNeg m) * z ∈ latHat m 𝔞 := by
  have hcl := FiniteAdeleRing.closure_range_algebraMap (𝓞 (QNeg m)) (QNeg m)
  have hz' : z ∈ closure (Set.range (algebraMap (𝓞 (QNeg m)) (AfK m))) := (Set.ext_iff.1 hcl z).2 hz
  refine map_mem_closure (continuous_const.mul continuous_id) hz' ?_
  rintro _ ⟨r, rfl⟩
  refine ⟨(N : QNeg m) * (r : QNeg m), hN𝔞 r, ?_⟩
  show algebraMap (QNeg m) (AfK m) ((N : QNeg m) * (r : QNeg m)) = _
  rw [map_mul]; rfl

theorem algebraMap_integers_eq (y : 𝓞 (QNeg m)) :
    algebraMap (𝓞 (QNeg m)) (AfK m) y = algebraMap (QNeg m) (AfK m) (y : QNeg m) := rfl

theorem linIndep_mul_I_sqrt {w : ℂ} (hw : w ≠ 0) :
    LinearIndependent ℝ ![w, w * (I * (Real.sqrt m : ℂ))] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hsqrt : (0 : ℝ) < Real.sqrt m := Real.sqrt_pos.2 (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne m))
  have h1 : w * ((a : ℂ) + (b : ℂ) * (I * (Real.sqrt m : ℂ))) = 0 := by
    rw [Complex.real_smul, Complex.real_smul] at hab; linear_combination hab
  have h2 := (mul_eq_zero.1 h1).resolve_left hw
  have hre := congrArg Complex.re h2
  have him := congrArg Complex.im h2
  simp at hre him
  refine ⟨hre, ?_⟩
  rcases him with h | h
  · exact h
  · exact absurd h (NeZero.ne m)

/-- **`s⁻¹𝔞` is a lattice**: for a lattice `𝔞 ⊂ K` and an idele `s`, `κ(K ∩ s_f⁻¹𝔞̂)` is the lattice of a period
pair (it lies between `c₀𝒪_K` and `c₁⁻¹𝒪_K`). -/
theorem exists_periodPair_sInvLat (hsq : Squarefree m) (L : PeriodPair) {𝔞 : Set (QNeg m)}
    (h𝔞 : (L.lattice : Set ℂ) = kappa m '' 𝔞) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)) :
    ∃ L' : PeriodPair, (L'.lattice : Set ℂ) = kappa m '' sInvLat m s 𝔞 := by
  set alg := algebraMap (QNeg m) (AfK m) with halg
  have hM := eq_kappaComap L h𝔞
  set M := kappaComap (m := m) L.lattice
  have hadd : ∀ x y, x ∈ sInvLat m s 𝔞 → y ∈ sInvLat m s 𝔞 → x + y ∈ sInvLat m s 𝔞 := by
    intro x y hx hy
    show finPart s * alg (x + y) ∈ latHat m 𝔞
    rw [map_add, mul_add]
    rw [hM] at hx hy ⊢
    exact latHat_add_mem M hx hy
  have hzero : (0 : QNeg m) ∈ sInvLat m s 𝔞 := by
    show finPart s * alg 0 ∈ latHat m 𝔞
    rw [map_zero, mul_zero, ← map_zero alg]
    exact mem_latHat_of_mem (by rw [hM]; exact zero_mem M)
  have hzsmul : ∀ (n : ℤ) x, x ∈ sInvLat m s 𝔞 → n • x ∈ sInvLat m s 𝔞 := by
    intro n x hx
    show finPart s * alg (n • x) ∈ latHat m 𝔞
    rw [map_zsmul, mul_smul_comm]
    have hx' : finPart s * alg x ∈ latHat m 𝔞 := hx
    rw [hM] at hx' ⊢
    rw [latHat_eq_closure] at hx' ⊢
    exact zsmul_mem hx' n
  let b : Submodule ℤ (QNeg m) :=
    { carrier := sInvLat m s 𝔞
      add_mem' := fun hx hy => hadd _ _ hx hy
      zero_mem' := hzero
      smul_mem' := fun n x hx => hzsmul n x hx }
  -- lower bound `N c 𝒪 ⊆ s⁻¹𝔞`
  obtain ⟨N, hN, hN𝔞⟩ := exists_nat_mul_integers_mem hsq L h𝔞
  obtain ⟨c, hc0, hc⟩ := FiniteAdeleRing.mul_nonZeroDivisor_mem_integralAdeles (finPart s)
  have hcK : (c : QNeg m) ≠ 0 := by
    intro h; exact nonZeroDivisors.ne_zero hc0 (by exact_mod_cast h)
  have hlow : ∀ y : 𝓞 (QNeg m), (N : QNeg m) * c * y ∈ sInvLat m s 𝔞 := by
    intro y
    show finPart s * alg ((N : QNeg m) * c * y) ∈ latHat m 𝔞
    have e : finPart s * alg ((N : QNeg m) * c * y) = alg (N : QNeg m) *
        ((finPart s * algebraMap (𝓞 (QNeg m)) (AfK m) c) * algebraMap (𝓞 (QNeg m)) (AfK m) y) := by
      rw [algebraMap_integers_eq, algebraMap_integers_eq, map_mul, map_mul]; ring
    rw [e]
    exact natMul_integral_mem_latHat hN𝔞 (Subalgebra.mul_mem _ hc (Subalgebra.algebraMap_mem _ y))
  -- upper bound `c' d (s⁻¹𝔞) ⊆ 𝒪`
  obtain ⟨a₁, -, ha₁⟩ : L.ω₁ ∈ kappa m '' 𝔞 := h𝔞 ▸ L.ω₁_mem_lattice
  obtain ⟨a₂, -, ha₂⟩ : L.ω₂ ∈ kappa m '' 𝔞 := h𝔞 ▸ L.ω₂_mem_lattice
  obtain ⟨⟨r₁, d₁⟩, hd₁⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 (QNeg m))) a₁
  obtain ⟨⟨r₂, d₂⟩, hd₂⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 (QNeg m))) a₂
  simp only at hd₁ hd₂
  set d : 𝓞 (QNeg m) := (d₁ : 𝓞 (QNeg m)) * d₂
  have hdK : (d : QNeg m) ≠ 0 := by
    have h1 := nonZeroDivisors.ne_zero d₁.2
    have h2 := nonZeroDivisors.ne_zero d₂.2
    intro h; exact mul_ne_zero h1 h2 (by exact_mod_cast h)
  have hd𝔞 : ∀ x ∈ 𝔞, (d : QNeg m) * x ∈ (algebraMap (𝓞 (QNeg m)) (QNeg m)).range := by
    intro x hx
    obtain ⟨p, q, hpq⟩ := PeriodPair.mem_lattice.1 ((mem_of_kappa L h𝔞 x).1 hx)
    have hx' : x = (p : QNeg m) * a₁ + (q : QNeg m) * a₂ := by
      apply kappa_injective
      rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ha₁, ha₂, hpq]
    refine ⟨p * (d₂ : 𝓞 (QNeg m)) * r₁ + q * (d₁ : 𝓞 (QNeg m)) * r₂, ?_⟩
    rw [hx']
    simp only [map_add, map_mul, map_intCast, ← hd₁, ← hd₂, d]
    push_cast; ring
  have hhat : ∀ z ∈ latHat m 𝔞,
      alg (d : QNeg m) * z ∈ FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m) := by
    intro z hz
    have hcl : IsClosed {z : AfK m | alg (d : QNeg m) * z ∈
        FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m)} :=
      (FiniteAdeleRing.isClosed_integralAdeles _ _).preimage (continuous_const.mul continuous_id)
    refine closure_minimal ?_ hcl hz
    rintro _ ⟨x, hx, rfl⟩
    simp only [Set.mem_setOf_eq]
    rw [← map_mul]
    exact (FiniteAdeleRing.algebraMap_mem_integralAdeles_iff _).2 (hd𝔞 x hx)
  obtain ⟨c', hc'0, hc'⟩ := FiniteAdeleRing.mul_nonZeroDivisor_mem_integralAdeles (finPart s⁻¹)
  have hc'K : (c' : QNeg m) ≠ 0 := by
    intro h; exact nonZeroDivisors.ne_zero hc'0 (by exact_mod_cast h)
  have hup : ∀ x ∈ sInvLat m s 𝔞,
      (c' : QNeg m) * d * x ∈ (algebraMap (𝓞 (QNeg m)) (QNeg m)).range := by
    intro x hx
    rw [← FiniteAdeleRing.algebraMap_mem_integralAdeles_iff (R := 𝓞 (QNeg m))]
    have e : alg ((c' : QNeg m) * d * x) =
        (finPart s⁻¹ * algebraMap (𝓞 (QNeg m)) (AfK m) c') * (alg (d : QNeg m) * (finPart s * alg x)) := by
      rw [algebraMap_integers_eq, map_mul, map_mul]
      have h1 := finPart_inv_mul s
      linear_combination (-(alg (c' : QNeg m) * alg (d : QNeg m) * alg x)) * h1
    rw [e]
    exact Subalgebra.mul_mem _ hc' (hhat _ hx)
  -- the period pair
  set c₀ : QNeg m := (N : QNeg m) * c
  set c₁ : QNeg m := (c' : QNeg m) * d
  have hc₀ : c₀ ≠ 0 := mul_ne_zero (by exact_mod_cast hN.ne') hcK
  have hc₁ : c₁ ≠ 0 := mul_ne_zero hc'K hdK
  set Lb : Submodule ℤ ℂ := b.map (kappaLin m)
  have hLb : (Lb : Set ℂ) = kappa m '' sInvLat m s 𝔞 := by
    ext z; simp only [Lb, Submodule.map_coe, kappaLin_apply]; rfl
  have hkc₁ : kappa m c₁ ≠ 0 := fun h => hc₁ (kappa_injective (h.trans (by simp [kappa])))
  set w : ℂ := (kappa m c₁)⁻¹ with hwdef
  have hw0 : w ≠ 0 := inv_ne_zero hkc₁
  have hind0 : LinearIndependent ℝ ![w / 2, w / 2 * (I * (Real.sqrt m : ℂ))] :=
    linIndep_mul_I_sqrt (div_ne_zero hw0 two_ne_zero)
  let P₀ : PeriodPair := ⟨w / 2, w / 2 * (I * (Real.sqrt m : ℂ)), hind0⟩
  have hsub : (Lb : Set ℂ) ⊆ P₀.lattice := by
    rw [hLb]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨y, hy⟩ := hup x hx
    obtain ⟨a, t, -, ha, ht, -⟩ := two_coords hsq y
    rw [SetLike.mem_coe, PeriodPair.mem_lattice]
    refine ⟨a, t, ?_⟩
    have hx' : x = c₁⁻¹ * (y : QNeg m) := by
      have : (y : QNeg m) = c₁ * x := hy
      rw [this, ← mul_assoc, inv_mul_cancel₀ hc₁, one_mul]
    have hky : kappa m (y : QNeg m) = (a : ℂ) / 2 + (t : ℂ) / 2 * (I * (Real.sqrt m : ℂ)) := by
      simp only [kappa]
      have ha' : ((y : QNeg m).re : ℂ) = (a : ℂ) / 2 := by
        have : ((y : QNeg m).re : ℚ) = a / 2 := by rw [← ha]; ring
        rw [this]; push_cast; ring
      have ht' : ((y : QNeg m).im : ℂ) = (t : ℂ) / 2 := by
        have : ((y : QNeg m).im : ℚ) = t / 2 := by rw [← ht]; ring
        rw [this]; push_cast; ring
      rw [ha', ht']
    have hkx : kappa m x = w * kappa m (y : QNeg m) := by
      rw [hwdef, hx', ← kappaAlg_apply, ← kappaAlg_apply, ← kappaAlg_apply, map_mul, map_inv₀]
    show (a : ℂ) * (w / 2) + (t : ℂ) * (w / 2 * (I * (Real.sqrt m : ℂ))) = kappa m x
    rw [hkx, hky]; ring
  have hdisc : DiscreteTopology Lb := DiscreteTopology.of_subset (inferInstance : DiscreteTopology P₀.lattice) hsub
  have hv1 : kappa m c₀ ∈ (Lb : Set ℂ) := by
    rw [hLb]; exact ⟨c₀, by simpa [c₀] using hlow 1, rfl⟩
  have hv2 : kappa m c₀ * (I * (Real.sqrt m : ℂ)) ∈ (Lb : Set ℂ) := by
    rw [hLb]
    refine ⟨(N : QNeg m) * c * (sqrtNeg m : QNeg m), hlow (sqrtNeg m), ?_⟩
    rw [coe_sqrtNeg, ← kappaAlg_apply, map_mul, kappaAlg_apply, kappaAlg_apply, kappa_omega]
  have hkc₀ : kappa m c₀ ≠ 0 := fun h => hc₀ (kappa_injective (h.trans (by simp [kappa])))
  have hspan : Submodule.span ℝ (Lb : Set ℂ) = ⊤ := by
    have hli := linIndep_mul_I_sqrt (m := m) hkc₀
    have htop : Submodule.span ℝ (Set.range ![kappa m c₀, kappa m c₀ * (I * (Real.sqrt m : ℂ))]) = ⊤ :=
      hli.span_eq_top_of_card_eq_finrank' (by simp)
    rw [eq_top_iff, ← htop]
    apply Submodule.span_mono
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact hv1
    · exact hv2
  have : IsZLattice ℝ Lb := ⟨hspan⟩
  have hrank : Module.finrank ℤ Lb = 2 := by
    rw [ZLattice.rank ℝ Lb, Complex.finrank_real_complex]
  let B := Module.finBasisOfFinrankEq ℤ Lb hrank
  have hBind : LinearIndependent ℝ ![((B 0 : Lb) : ℂ), ((B 1 : Lb) : ℂ)] := by
    have := (B.ofZLatticeBasis ℝ Lb).linearIndependent
    convert this using 1
    funext i; fin_cases i <;> simp
  refine ⟨⟨(B 0 : ℂ), (B 1 : ℂ), hBind⟩, ?_⟩
  rw [← hLb]
  have hspanZ := B.ofZLatticeBasis_span ℝ Lb
  have hr : Set.range (B.ofZLatticeBasis ℝ Lb) = {((B 0 : Lb) : ℂ), ((B 1 : Lb) : ℂ)} := by
    ext z; simp [Fin.exists_fin_two, eq_comm]
  rw [hr] at hspanZ
  show ((Submodule.span ℤ {((B 0 : Lb) : ℂ), ((B 1 : Lb) : ℂ)} : Submodule ℤ ℂ) : Set ℂ) = Lb
  rw [hspanZ]

/-! ## §Q. The local–global principle for lattices: `𝔟 = {x ∈ K : x ∈ 𝔟_p for every prime p}` -/

/-- Every element of `K` has a positive integer multiple in `𝒪_K`. -/
theorem exists_nat_mul_mem_integers (x : QNeg m) :
    ∃ D : ℕ, 0 < D ∧ (D : QNeg m) * x ∈ (algebraMap (𝓞 (QNeg m)) (QNeg m)).range := by
  refine ⟨x.re.den * x.im.den, Nat.mul_pos x.re.den_pos x.im.den_pos, ?_⟩
  refine ⟨((x.re.num * x.im.den : ℤ) : 𝓞 (QNeg m)) + ((x.im.num * x.re.den : ℤ) : 𝓞 (QNeg m)) * sqrtNeg m, ?_⟩
  rw [map_add, map_mul, map_intCast, map_intCast]
  have hs : algebraMap (𝓞 (QNeg m)) (QNeg m) (sqrtNeg m) = QuadraticAlgebra.omega := coe_sqrtNeg
  rw [hs]
  have e1 := Rat.mul_den_eq_num x.re
  have e2 := Rat.mul_den_eq_num x.im
  ext
  · simp only [QuadraticAlgebra.re_add, QuadraticAlgebra.re_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega,
      QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]
    push_cast
    linear_combination -(x.im.den : ℚ) * e1
  · simp only [QuadraticAlgebra.im_add, QuadraticAlgebra.im_mul, QuadraticAlgebra.re_intCast,
      QuadraticAlgebra.im_intCast, QuadraticAlgebra.re_omega, QuadraticAlgebra.im_omega,
      QuadraticAlgebra.re_natCast, QuadraticAlgebra.im_natCast]
    push_cast
    linear_combination -(x.re.den : ℚ) * e2

/-- A lattice is the `ℤ`-span of `κ⁻¹ω₁, κ⁻¹ω₂`, and `K ∩ 𝔟̂ = 𝔟` (from the tree's `latHat_inter_of_sandwich`). -/
theorem mem_of_mem_latHat (hsq : Squarefree m) (L : PeriodPair) {𝔟 : Set (QNeg m)}
    (h𝔟 : (L.lattice : Set ℂ) = kappa m '' 𝔟) {x : QNeg m}
    (hx : algebraMap (QNeg m) (AfK m) x ∈ latHat m 𝔟) : x ∈ 𝔟 := by
  obtain ⟨a₁, -, ha₁⟩ : L.ω₁ ∈ kappa m '' 𝔟 := h𝔟 ▸ L.ω₁_mem_lattice
  obtain ⟨a₂, -, ha₂⟩ : L.ω₂ ∈ kappa m '' 𝔟 := h𝔟 ▸ L.ω₂_mem_lattice
  have hspan : 𝔟 = (Submodule.span ℤ {a₁, a₂} : Set (QNeg m)) := by
    ext y
    rw [mem_of_kappa L h𝔟, PeriodPair.mem_lattice, SetLike.mem_coe, Submodule.mem_span_pair]
    constructor
    · rintro ⟨p, q, hpq⟩
      refine ⟨p, q, kappa_injective ?_⟩
      rw [kappa_add, kappa_zsmul, kappa_zsmul, ha₁, ha₂, ← hpq, zsmul_eq_mul, zsmul_eq_mul]
    · rintro ⟨p, q, hpq⟩
      refine ⟨p, q, ?_⟩
      rw [← hpq, kappa_add, kappa_zsmul, kappa_zsmul, ha₁, ha₂, zsmul_eq_mul, zsmul_eq_mul]
  obtain ⟨n, hn, hn𝔟⟩ := exists_nat_mul_integers_mem hsq L h𝔟
  obtain ⟨D₁, hD₁, hd₁⟩ := exists_nat_mul_mem_integers a₁
  obtain ⟨D₂, hD₂, hd₂⟩ := exists_nat_mul_mem_integers a₂
  have hda₁ : ((D₁ * D₂ : ℕ) : QNeg m) * a₁ ∈ Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m)) := by
    obtain ⟨r, hr⟩ := hd₁
    exact ⟨(D₂ : 𝓞 (QNeg m)) * r, by rw [map_mul, hr, map_natCast]; push_cast; ring⟩
  have hda₂ : ((D₁ * D₂ : ℕ) : QNeg m) * a₂ ∈ Set.range (algebraMap (𝓞 (QNeg m)) (QNeg m)) := by
    obtain ⟨r, hr⟩ := hd₂
    exact ⟨(D₁ : 𝓞 (QNeg m)) * r, by rw [map_mul, hr, map_natCast]; push_cast; ring⟩
  have key := latHat_inter_of_sandwich a₁ a₂ n (D₁ * D₂) hn (Nat.mul_pos hD₁ hD₂)
    (fun y => by have := hn𝔟 y; rw [hspan] at this; exact this) hda₁ hda₂
  rw [hspan] at hx ⊢
  have : x ∈ {x : QNeg m | algebraMap (QNeg m) (AfK m) x ∈
      latHat m (Submodule.span ℤ {a₁, a₂} : Set (QNeg m))} := hx
  rw [key] at this
  exact this

/-- Only finitely many places lie above a prime. -/
theorem finite_placesAbove {p : ℕ} (hp : p.Prime) : Finite (PlacesAbove m p) := by
  have hp0 : (p : 𝓞 (QNeg m)) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hI : Ideal.span {(p : 𝓞 (QNeg m))} ≠ 0 := by
    rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hp0
  have hf := Ideal.finite_factors hI
  have : {v : HeightOneSpectrum (𝓞 (QNeg m)) | (p : 𝓞 (QNeg m)) ∈ v.asIdeal} =
      {v : HeightOneSpectrum (𝓞 (QNeg m)) | v.asIdeal ∣ Ideal.span {(p : 𝓞 (QNeg m))}} := by
    ext v; simp only [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
  rw [← this] at hf
  exact hf.to_subtype

theorem valuation_intCast_le_one (v : HeightOneSpectrum (𝓞 (QNeg m))) (k : ℤ) :
    v.valuation (QNeg m) (k : QNeg m) ≤ 1 := by
  have := v.valuation_le_one (K := QNeg m) (k : 𝓞 (QNeg m))
  simpa using this

theorem valuation_natCast_eq_one {v : HeightOneSpectrum (𝓞 (QNeg m))} {p : ℕ}
    (hv : (p : 𝓞 (QNeg m)) ∉ v.asIdeal) : v.valuation (QNeg m) (p : QNeg m) = 1 := by
  rw [show (p : QNeg m) = algebraMap (𝓞 (QNeg m)) (QNeg m) (p : 𝓞 (QNeg m)) by simp,
    HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_eq_one_iff.2 hv

/-- **One prime at a time.** If `p y ∈ 𝔟` and `y ∈ 𝔟_p`, then `y ∈ 𝔟`. -/
theorem mem_of_prime_mul_mem (hsq : Squarefree m) (L : PeriodPair) {𝔟 : Set (QNeg m)}
    (h𝔟 : (L.lattice : Set ℂ) = kappa m '' 𝔟) {p : ℕ} (hp : p.Prime) {y : QNeg m}
    (hpy : (p : QNeg m) * y ∈ 𝔟) (hy : diagP p y ∈ locLat p 𝔟) : y ∈ 𝔟 := by
  have hm := mem_of_kappa L h𝔟
  have hM := eq_kappaComap L h𝔟
  set M := kappaComap (m := m) L.lattice
  set alg := algebraMap (QNeg m) (AfK m) with halg
  have := finite_placesAbove (m := m) hp
  obtain ⟨n, hn, hn𝔟⟩ := exists_nat_mul_integers_mem hsq L h𝔟
  have hn0 : (n : QNeg m) ≠ 0 := by exact_mod_cast hn.ne'
  -- `D 𝔟 ⊆ 𝒪`
  obtain ⟨a₁, -, ha₁⟩ : L.ω₁ ∈ kappa m '' 𝔟 := h𝔟 ▸ L.ω₁_mem_lattice
  obtain ⟨a₂, -, ha₂⟩ : L.ω₂ ∈ kappa m '' 𝔟 := h𝔟 ▸ L.ω₂_mem_lattice
  obtain ⟨D₁, hD₁, r₁, hr₁⟩ := exists_nat_mul_mem_integers a₁
  obtain ⟨D₂, hD₂, r₂, hr₂⟩ := exists_nat_mul_mem_integers a₂
  set D : ℕ := D₁ * D₂
  have hD : 0 < D := Nat.mul_pos hD₁ hD₂
  have hD𝔟 : ∀ b ∈ 𝔟, ∀ v : HeightOneSpectrum (𝓞 (QNeg m)),
      v.valuation (QNeg m) ((D : QNeg m) * b) ≤ 1 := by
    intro b hb v
    obtain ⟨p', q', hpq⟩ := PeriodPair.mem_lattice.1 ((hm b).1 hb)
    have hb' : b = (p' : QNeg m) * a₁ + (q' : QNeg m) * a₂ := by
      apply kappa_injective
      rw [kappa_add, kappa_intCast_mul, kappa_intCast_mul, ha₁, ha₂, hpq]
    have e : (D : QNeg m) * b = algebraMap (𝓞 (QNeg m)) (QNeg m)
        (p' * (D₂ : 𝓞 (QNeg m)) * r₁ + q' * (D₁ : 𝓞 (QNeg m)) * r₂) := by
      rw [hb']
      simp only [map_add, map_mul, map_intCast, map_natCast, hr₁, hr₂, D]
      push_cast; ring
    rw [e]; exact v.valuation_le_one _
  -- step (i): `b ∈ 𝔟` with `n⁻¹(b − y)` integral at the places above `p`
  set W : Set (Kp m p) := ⋂ v : PlacesAbove m p,
    (fun z : Kp m p => (alg ((n : QNeg m)⁻¹)) v.1 * (z v - diagP p y v)) ⁻¹'
      {w : v.1.adicCompletion (QNeg m) | Valued.v w ≤ 1}
  have hWo : IsOpen W := isOpen_iInter_of_finite fun v => by
    refine IsOpen.preimage (continuous_const.mul ((continuous_apply v).sub continuous_const)) ?_
    exact Valued.isOpen_integer (v.1.adicCompletion (QNeg m))
  have hyW : diagP p y ∈ W := by
    simp only [W, Set.mem_iInter, Set.mem_preimage, sub_self, mul_zero, Set.mem_ofPred_eq]
    intro v; simp
  obtain ⟨_, hbW, b, hb, rfl⟩ := mem_closure_iff.1 hy W hWo hyW
  have hbv : ∀ v : PlacesAbove m p, v.1.valuation (QNeg m) ((n : QNeg m)⁻¹ * (b - y)) ≤ 1 := by
    intro v
    have h1 := Set.mem_iInter.1 hbW v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq] at h1
    rw [← val_algebraMap_apply]
    convert h1 using 2
    rw [map_mul, map_sub]; rfl
  -- step (ii): one Bézout step removes the other primes
  have hp0 : (p : QNeg m) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hnD0 : n * D ≠ 0 := Nat.mul_ne_zero hn.ne' hD.ne'
  set j := (n * D).factorization p
  set M' := ordCompl[p] (n * D)
  have hnD : p ^ j * M' = n * D := Nat.ordProj_mul_ordCompl_eq_self (n * D) p
  have hpM : ¬ p ∣ M' := Nat.not_dvd_ordCompl hp hnD0
  obtain ⟨t, s', hts⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
  set c : QNeg m := (p : QNeg m) * y - (p : QNeg m) * b
  have hpb : (p : QNeg m) * b ∈ 𝔟 := by
    rw [hM] at hb ⊢
    have := zsmul_mem hb (p : ℤ)
    rwa [zsmul_eq_mul, Int.cast_natCast] at this
  have hc : c ∈ 𝔟 := by
    rw [hM] at hpy hpb ⊢; exact sub_mem hpy hpb
  set z : QNeg m := y - b - (t : QNeg m) * c
  have hts' : (t : QNeg m) * p + (s' : QNeg m) * M' = 1 := by exact_mod_cast hts
  have hz : z = (s' : QNeg m) * M' * (y - b) := by
    simp only [z, c]; linear_combination (-(y - b)) * hts'
  have hzint : ∀ v : HeightOneSpectrum (𝓞 (QNeg m)),
      v.valuation (QNeg m) ((n : QNeg m)⁻¹ * z) ≤ 1 := by
    intro v
    by_cases hv : (p : 𝓞 (QNeg m)) ∈ v.asIdeal
    · have e : (n : QNeg m)⁻¹ * z = ((-(1 - t * p) : ℤ) : QNeg m) * ((n : QNeg m)⁻¹ * (b - y)) := by
        simp only [z, c]; push_cast; ring
      rw [e, Valuation.map_mul]
      exact mul_le_one' (valuation_intCast_le_one v _) (hbv ⟨v, hv⟩)
    · have hnD' : (p : QNeg m) ^ j * M' = (n : QNeg m) * D := by exact_mod_cast hnD
      have e : (n : QNeg m)⁻¹ * z = (s' : QNeg m) * ((D : QNeg m) * c) * ((p : QNeg m) ^ (j + 1))⁻¹ := by
        rw [hz]; simp only [c]
        field_simp
        linear_combination (s' : QNeg m) * (y - b) * (p : QNeg m) * hnD'
      rw [e, Valuation.map_mul, Valuation.map_mul, map_inv₀, map_pow, valuation_natCast_eq_one hv,
        one_pow, inv_one, mul_one]
      exact mul_le_one' (valuation_intCast_le_one v s') (hD𝔟 c hc v)
  have hzhat : alg z ∈ latHat m 𝔟 := by
    have hint : alg ((n : QNeg m)⁻¹ * z) ∈ FiniteAdeleRing.integralAdeles (𝓞 (QNeg m)) (QNeg m) := by
      rw [mem_intAdeles_iff]; intro v; rw [val_algebraMap_apply]; exact hzint v
    have := natMul_integral_mem_latHat hn𝔟 hint
    rwa [← map_mul, ← mul_assoc, mul_inv_cancel₀ hn0, one_mul] at this
  have hyz : y = z + b + (t : QNeg m) * c := by simp only [z]; ring
  apply mem_of_mem_latHat hsq L h𝔟
  rw [hyz, map_add, map_add]
  have htc : (t : QNeg m) * c ∈ 𝔟 := by
    rw [hM] at hc ⊢
    have := zsmul_mem hc t
    rwa [zsmul_eq_mul] at this
  rw [hM] at hb htc hzhat ⊢
  exact latHat_add_mem M (latHat_add_mem M hzhat (mem_latHat_of_mem hb)) (mem_latHat_of_mem htc)

/-- `𝔟_p` is closed under integer multiples. -/
theorem zsmul_mem_locLat (L : PeriodPair) {𝔟 : Set (QNeg m)} (h𝔟 : (L.lattice : Set ℂ) = kappa m '' 𝔟)
    (p : ℕ) (k : ℤ) {z : Kp m p} (hz : z ∈ locLat p 𝔟) : k • z ∈ locLat p 𝔟 := by
  have hM := eq_kappaComap L h𝔟
  refine map_mem_closure (continuous_const_smul k) hz ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨k • x, ?_, ?_⟩
  · rw [hM] at hx ⊢; exact zsmul_mem hx k
  · show projP p (algebraMap (QNeg m) (AfK m) (k • x)) = k • projP p (algebraMap (QNeg m) (AfK m) x)
    rw [map_zsmul]; rfl

/-- `𝔟_p` is an additive subgroup: closed under subtraction. -/
theorem sub_mem_locLat (L : PeriodPair) {𝔟 : Set (QNeg m)} (h𝔟 : (L.lattice : Set ℂ) = kappa m '' 𝔟)
    (p : ℕ) {z w : Kp m p} (hz : z ∈ locLat p 𝔟) (hw : w ∈ locLat p 𝔟) : z - w ∈ locLat p 𝔟 := by
  have hM := eq_kappaComap L h𝔟
  refine map_mem_closure₂ continuous_sub hz hw ?_
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  refine ⟨x - y, ?_, ?_⟩
  · rw [hM] at hx hy ⊢; exact sub_mem hx hy
  · show projP p (algebraMap (QNeg m) (AfK m) (x - y)) = _
    rw [map_sub]; rfl

/-- **The local–global principle for lattices of `K`**: `x ∈ K` lies in the lattice `𝔟` as soon as `x ∈ 𝔟_p`
for every prime `p`. -/
theorem mem_of_forall_locLat (hsq : Squarefree m) (L : PeriodPair) {𝔟 : Set (QNeg m)}
    (h𝔟 : (L.lattice : Set ℂ) = kappa m '' 𝔟) {x : QNeg m}
    (hx : ∀ p : ℕ, p.Prime → diagP p x ∈ locLat p 𝔟) : x ∈ 𝔟 := by
  classical
  have hex : ∃ r : ℕ, 0 < r ∧ ((r : ℤ) • x) ∈ 𝔟 := exists_nat_mul_mem L h𝔟 x
  set r := Nat.find hex with hr
  obtain ⟨hr0, hrx⟩ := Nat.find_spec hex
  by_cases h1 : r = 1
  · rw [← hr, h1] at hrx; simpa using hrx
  · exfalso
    have hr1 : 1 < r := by omega
    set p := r.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    obtain ⟨r', hr'⟩ := Nat.minFac_dvd r
    have hr'0 : 0 < r' := by
      rcases Nat.eq_zero_or_pos r' with h | h
      · rw [h, mul_zero] at hr'; omega
      · exact h
    have hr'lt : r' < r := by
      rw [hr']; exact lt_mul_left hr'0 hp.one_lt
    have hy : ((r' : ℤ) • x) ∈ 𝔟 := by
      apply mem_of_prime_mul_mem hsq L h𝔟 hp
      · have : (p : QNeg m) * ((r' : ℤ) • x) = (r : ℤ) • x := by
          rw [hr', zsmul_eq_mul, zsmul_eq_mul]; push_cast; ring
        rw [this]; exact hrx
      · have := zsmul_mem_locLat L h𝔟 p (r' : ℤ) (hx p hp)
        convert this using 1
        show projP p (algebraMap (QNeg m) (AfK m) ((r' : ℤ) • x)) = _
        rw [map_zsmul]; rfl
    exact Nat.find_min hex hr'lt ⟨hr'0, hy⟩

/-- **Lattices are determined by their `p`-components** (so `ShimuraThm54Local`'s `𝔟` is Shimura's `s⁻¹𝔞`). -/
theorem lattice_eq_of_locLat_eq (hsq : Squarefree m) {L L' : PeriodPair} {𝔟 𝔟' : Set (QNeg m)}
    (h𝔟 : (L.lattice : Set ℂ) = kappa m '' 𝔟) (h𝔟' : (L'.lattice : Set ℂ) = kappa m '' 𝔟')
    (h : ∀ p : ℕ, p.Prime → locLat p 𝔟 = locLat p 𝔟') : 𝔟 = 𝔟' := by
  ext x
  constructor
  · intro hx
    exact mem_of_forall_locLat hsq L' h𝔟' fun p hp => h p hp ▸ subset_closure ⟨x, hx, rfl⟩
  · intro hx
    exact mem_of_forall_locLat hsq L h𝔟 fun p hp => (h p hp).symm ▸ subset_closure ⟨x, hx, rfl⟩

/-- **`s⁻¹u` is well defined**: two `v`'s satisfying the local congruences differ by an element of `𝔟`
(so `K/𝔟 → ⊕_p K_p/𝔟_p` is injective). -/
theorem rep_sub_mem (hsq : Squarefree m) {L : PeriodPair} {𝔟 : Set (QNeg m)}
    (h𝔟 : (L.lattice : Set ℂ) = kappa m '' 𝔟) (c : (p : ℕ) → Kp m p) {u v v' : QNeg m}
    (hv : ∀ p : ℕ, p.Prime → diagP p v - c p * diagP p u ∈ locLat p 𝔟)
    (hv' : ∀ p : ℕ, p.Prime → diagP p v' - c p * diagP p u ∈ locLat p 𝔟) : v - v' ∈ 𝔟 := by
  apply mem_of_forall_locLat hsq L h𝔟
  intro p hp
  have := sub_mem_locLat L h𝔟 p (hv p hp) (hv' p hp)
  convert this using 1
  show projP p (algebraMap (QNeg m) (AfK m) (v - v')) = _
  rw [map_sub, projP_sub]
  simp only [diagP]
  ring

end LatticeSec

/-! ## §P. Shimura 1971 Thm 5.4 with the print's hypotheses and the print's `s⁻¹𝔞`, and `ShimuraMainCM` -/

section Printed

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise T5Glue

/-- **LEAF SHIMURA-5.4-LOCAL (the main theorem of complex multiplication, Shimura 1971 Thm 5.4, with the print's
hypotheses and the print's `s⁻¹𝔞` and `s⁻¹u`).** Let `K = ℚ(√−m) ⊂ ℂ` (through `κ`, `√−m ↦ i√m`), `e : Kˢ → ℚ̄`
normalized (`ιC ∘ e = κ` on `K`), `σ ∈ Aut(ℂ)` and `s ∈ 𝔸_K^×` with `σ = [s, K]` on `K^ab` (`ArtinCond`). Let `𝔞`
be a lattice in `K` (`κ(𝔞)` is the lattice of a period pair) and `𝔟 = s⁻¹𝔞`, the lattice of `K` whose
`p`-components are `𝔟_p = s_p⁻¹𝔞_p` for every prime `p` (`K_p = K ⊗ ℚ_p = ∏_{v∣p} K_v`, `𝔞_p = 𝔞 ⊗ ℤ_p` the closure
of `𝔞` in `K_p`, `s_p` the `p`-component of `s`; `locLat`, `ideleComp`). Let `E` be an elliptic curve over `ℂ`
in short Weierstrass form (`E(ℂ) = E.toAffine.Point`) and `ξ : ℂ/𝔞 → E(ℂ)` an analytic isomorphism
(`IsAnalyticIso`: a bijection `ℂ/κ(𝔞) → E(ℂ)`, holomorphic into `E(ℂ) ⊂ ℙ²(ℂ)` with nowhere vanishing differential;
and a group homomorphism). Then there is an analytic map `ξ' : ℂ/𝔟 → E^σ(ℂ)` (`E^σ = E.map σ`) inducing a bijection
`ℂ/κ(𝔟) → E^σ(ℂ)` and holomorphic into `ℙ²(ℂ)`, with `ξ(u)^σ = ξ'(s⁻¹u)` for all `u ∈ K/𝔞`; here `v ∈ K`
represents `s⁻¹u ∈ K/𝔟 = ⊕_p K_p/𝔟_p` when `v ≡ s_p⁻¹u (mod 𝔟_p)` for every prime `p`, and `P ↦ P^σ` is `conjPt σ`.

Source: G. Shimura, *Introduction to the arithmetic theory of automorphic functions* (1971), Thm. 5.4 (the
definitions of `s𝔞` and `su` through `p`-components in the same section); S. Lang, *Elliptic functions*, Ch. 10,
Thm. 3 (numbers UNVERIFIED, from memory; not read here). This is the print restricted, each change a special case
or a weakening of the conclusion: `E` ranges over short Weierstrass models; `ξ` is in addition a group homomorphism
(so the hypothesis implies the print's in either reading of "analytic isomorphism"); the uniqueness of `ξ'`, the
group-law and the holomorphy of its inverse are dropped from the conclusion. The setting (`ArtinCond`, the
normalization of `e`) is that of `T5Glue.ShimuraMainCM` and `HCMDict.ShimuraThm54`. -/
def ShimuraThm54Local : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (𝔟 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔟) →
    (∀ p : ℕ, p.Prime → locLat p 𝔟 = (fun x => ideleComp p s⁻¹ * x) '' locLat p 𝔞) →
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic], E.a₁ = 0 → E.a₂ = 0 → E.a₃ = 0 →
  ∀ ξ : ℂ → E.toAffine.Point, IsAnalyticIso E (kappa m '' 𝔞) ξ → (∀ z w, ξ (z + w) = ξ z + ξ w) →
    ∃ ξ' : ℂ → (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      InducesBij (E.map (σ : ℂ →+* ℂ)) (kappa m '' 𝔟) ξ' ∧ IsHolomorphicMap (E.map (σ : ℂ →+* ℂ)) ξ' ∧
      ∀ u v : QNeg m, (∀ p : ℕ, p.Prime → diagP p v - ideleComp p s⁻¹ * diagP p u ∈ locLat p 𝔟) →
        ZInQ.Contrib.HCMDict.conjPt (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)

/-- A holomorphic bijection `ℂ/L → E(ℂ)` with `0 ↦ O`, `E` a short model, satisfies hcm-dict's `IsAnalyticUnif`. -/
theorem isAnalyticUnif_of_holo (W : WeierstrassCurve ℂ) [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) (L : PeriodPair) (ξ : ℂ → W.toAffine.Point) (hb : InducesBij W L.lattice ξ)
    (hh : IsHolomorphicMap W ξ) (h0 : ξ 0 = 0) : ZInQ.Contrib.HCMDict.IsAnalyticUnif W L.lattice ξ := by
  obtain ⟨L₀, rfl⟩ := ZInQ.Contrib.HCMDict.exists_lattice_eq W h₁ h₂ h₃
  obtain ⟨α, hsc, hα⟩ := eq_toPoint_of_holo L₀ L ξ hb hh h0
  have : ξ = fun z => L₀.toPoint L₀.discriminant_ne_zero (α * z) := funext hα
  rw [this]
  exact ZInQ.Contrib.HCMDict.isAnalyticUnif_comp_mul L₀ L α hsc

/-- **`ShimuraMainCM` from Shimura's Thm 5.4 with the print's hypotheses and `s⁻¹𝔞`.** -/
theorem shimuraMainCM_of_local (h : ShimuraThm54Local) : ShimuraMainCM := by
  intro m _ hm e he σ s hs 𝔞 P P' hP hP'
  have : P.weierstrassCurve.IsElliptic :=
    ⟨isUnit_iff_ne_zero.mpr P.discriminant_ne_zero.weierstrassCurve_Δ_ne_zero⟩
  have hξ := toPoint_isAnalyticIso P
  rw [hP] at hξ
  have hadd := (P.isUniformization_toPoint P.discriminant_ne_zero).1
  obtain ⟨ξ', hb', hh', hcomm⟩ := h m hm e he σ s hs 𝔞 ⟨P, hP⟩ (sInvLat m s 𝔞) ⟨P', hP'⟩
    (fun p _ => locLat_sInvLat hm P hP s p) P.weierstrassCurve (by simp) (by simp) (by simp) _ hξ hadd
  have hk0 : kappa m 0 = 0 := by simp [kappa]
  have h0 : ξ' 0 = 0 := by
    have hrep : finPart s * algebraMap (QNeg m) (AfK m) 0 - algebraMap (QNeg m) (AfK m) 0 ∈ latHat m 𝔞 := by
      rw [map_zero, mul_zero, sub_zero, ← map_zero (algebraMap (QNeg m) (AfK m))]
      exact mem_latHat_of_mem ((mem_of_kappa P hP 0).2 (by rw [hk0]; exact zero_mem _))
    have := hcomm 0 0 fun p _ => rep_local_of_global hm P hP s hrep p
    rw [hk0, P.toPoint_zero] at this
    rw [← this]; rfl
  rw [← hP'] at hb'
  have hξ' := isAnalyticUnif_of_holo _ (by simp) (by simp) (by simp) P' ξ' hb' hh' h0
  obtain ⟨μ, hμ, ha4, ha6, hcoord⟩ :=
    ZInQ.Contrib.HCMDict.eq_scaled_of_isAnalyticUnif (P.weierstrassCurve.map (σ : ℂ →+* ℂ)) (by simp)
      (by simp) (by simp) P' ξ' hξ'
  simp only [WeierstrassCurve.map_a₄, WeierstrassCurve.map_a₆, PeriodPair.weierstrassCurve_a₄,
    PeriodPair.weierstrassCurve_a₆, map_div₀, map_neg, map_ofNat] at ha4 ha6
  refine ⟨μ, ⟨hμ, ?_, ?_⟩, fun u v hu huv => ?_⟩
  · linear_combination (-4 : ℂ) * ha4
  · linear_combination (-4 : ℂ) * ha6
  · have hc := hcomm u v fun p _ => rep_local_of_global hm P hP s huv p
    rw [P.toPoint_of_notMem _ hu] at hc
    have hv : kappa m v ∉ P'.lattice := by
      intro hv
      rw [← SetLike.mem_coe, ← hξ'.2.2.1] at hv
      rw [hv] at hc
      exact Point.some_ne_zero _ hc
    obtain ⟨h', e'⟩ := hcoord _ hv
    rw [e'] at hc
    simp only [ZInQ.Contrib.HCMDict.conjPt, Point.some.injEq, RingEquiv.coe_toRingHom, map_div₀,
      map_ofNat] at hc
    refine ⟨hc.1, ?_⟩
    linear_combination 2 * hc.2

/-- Composition with `z ↦ αz` (`α ≠ 0`) preserves nonvanishing differentials. -/
theorem IsImmersion.comp_mul {W : WeierstrassCurve ℂ} {ξ : ℂ → W.toAffine.Point} (h : IsImmersion W ξ)
    {α : ℂ} (hα : α ≠ 0) : IsImmersion W (fun z => ξ (α * z)) := by
  intro z₀
  obtain ⟨U, X, Y, Z, hz, ⟨hUo, hX, hY, hZ, hc⟩, hw⟩ := h (α * z₀)
  have hAd : Differentiable ℂ fun z : ℂ => α * z := differentiable_id.const_mul α
  refine ⟨(fun z => α * z) ⁻¹' U, fun z => X (α * z), fun z => Y (α * z), fun z => Z (α * z), hz,
    ⟨hUo.preimage hAd.continuous, hX.comp hAd.differentiableOn fun z hz => hz,
      hY.comp hAd.differentiableOn fun z hz => hz, hZ.comp hAd.differentiableOn fun z hz => hz,
      fun z hz => hc _ hz⟩, ?_⟩
  have hU : U ∈ 𝓝 (α * z₀) := hUo.mem_nhds hz
  have dcomp : ∀ F : ℂ → ℂ, DifferentiableOn ℂ F U →
      deriv (fun z => F (α * z)) z₀ = deriv F (α * z₀) * α := by
    intro F hF
    have h1 : HasDerivAt (fun z : ℂ => α * z) α z₀ := by simpa using (hasDerivAt_id z₀).const_mul α
    exact (HasDerivAt.comp (h := fun z : ℂ => α * z) z₀ (hF.differentiableAt hU).hasDerivAt h1).deriv
  intro h0
  apply hw
  have e0 := congrFun h0 0
  have e1 := congrFun h0 1
  have e2 := congrFun h0 2
  simp only [wedge, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons, Pi.zero_apply, dcomp X hX, dcomp Y hY, dcomp Z hZ] at e0 e1 e2
  have k : ∀ t : ℂ, α * t = 0 → t = 0 := fun t ht => (mul_eq_zero.1 ht).resolve_left hα
  have k0 : Y (α * z₀) * deriv Z (α * z₀) - Z (α * z₀) * deriv Y (α * z₀) = 0 :=
    k _ (by linear_combination e0)
  have k1 : Z (α * z₀) * deriv X (α * z₀) - X (α * z₀) * deriv Z (α * z₀) = 0 :=
    k _ (by linear_combination e1)
  have k2 : X (α * z₀) * deriv Y (α * z₀) - Y (α * z₀) * deriv X (α * z₀) = 0 :=
    k _ (by linear_combination e2)
  funext i
  fin_cases i <;> simp [wedge, k0, k1, k2]

/-- hcm-dict's `IsAnalyticUnif` on a short model implies `IsAnalyticIso` (through the dictionary). -/
theorem isAnalyticIso_of_unif (W : WeierstrassCurve ℂ) [W.IsElliptic] (h₁ : W.a₁ = 0) (h₂ : W.a₂ = 0)
    (h₃ : W.a₃ = 0) (L : PeriodPair) (ξ : ℂ → W.toAffine.Point)
    (hξ : ZInQ.Contrib.HCMDict.IsAnalyticUnif W L.lattice ξ) : IsAnalyticIso W L.lattice ξ := by
  have hb : InducesBij W L.lattice ξ := by
    let f : ℂ →+ W.toAffine.Point := AddMonoidHom.mk' ξ hξ.1
    refine ⟨fun z l hl => ?_, fun z w h => ?_, hξ.2.1⟩
    · rw [hξ.1, (hξ.2.2.1 l).2 hl, add_zero]
    · rw [← hξ.2.2.1]
      have : f (z - w) = f z - f w := map_sub f z w
      simp only [f, AddMonoidHom.mk'_apply] at this
      rw [this, h, sub_self]
  obtain ⟨L₀, rfl⟩ := ZInQ.Contrib.HCMDict.exists_lattice_eq W h₁ h₂ h₃
  obtain ⟨α, hsc, hα⟩ := ZInQ.Contrib.HCMDict.exists_isScale_eq L₀ L ξ hξ
  have e : ξ = fun z => L₀.toPoint L₀.discriminant_ne_zero (α * z) := funext hα
  have hI := (toPoint_isImmersion L₀).comp_mul hsc.1
  rw [← e] at hI
  exact ⟨hb, hI.isHolomorphicMap, hI⟩

/-- **The old leaf from the new one**: hcm-dict's `HCMDict.ShimuraThm54` follows from `ShimuraThm54Local`. -/
theorem shimuraThm54_of_local (h : ShimuraThm54Local) : ZInQ.Contrib.HCMDict.ShimuraThm54 := by
  intro m _ hm e he σ s hs 𝔞 h𝔞 E _ h₁ h₂ h₃ ξ hξ
  obtain ⟨L, hL⟩ := h𝔞
  obtain ⟨L', hL'⟩ := exists_periodPair_sInvLat hm L hL s
  have hξL : ZInQ.Contrib.HCMDict.IsAnalyticUnif E L.lattice ξ := by rw [hL]; exact hξ
  have hI := isAnalyticIso_of_unif E h₁ h₂ h₃ L ξ hξL
  rw [hL] at hI
  obtain ⟨ξ', hb', hh', hcomm⟩ := h m hm e he σ s hs 𝔞 ⟨L, hL⟩ (sInvLat m s 𝔞) ⟨L', hL'⟩
    (fun p _ => locLat_sInvLat hm L hL s p) E h₁ h₂ h₃ ξ hI hξ.1
  have hk0 : kappa m 0 = 0 := by simp [kappa]
  have h0 : ξ' 0 = 0 := by
    have hrep : finPart s * algebraMap (QNeg m) (AfK m) 0 - algebraMap (QNeg m) (AfK m) 0 ∈ latHat m 𝔞 := by
      rw [map_zero, mul_zero, sub_zero, ← map_zero (algebraMap (QNeg m) (AfK m))]
      exact mem_latHat_of_mem ((mem_of_kappa L hL 0).2 (by rw [hk0]; exact zero_mem _))
    have := hcomm 0 0 fun p _ => rep_local_of_global hm L hL s hrep p
    have hξ0 : ξ 0 = 0 := (hξ.2.2.1 0).2 ⟨0, (mem_of_kappa L hL 0).2 (by rw [hk0]; exact zero_mem _), hk0⟩
    rw [hk0, hξ0] at this
    rw [← this]; rfl
  refine ⟨ξ', ?_, fun u v huv => hcomm u v fun p _ => rep_local_of_global hm L hL s huv p⟩
  rw [← hL'] at hb' ⊢
  exact isAnalyticUnif_of_holo _ (by simp [h₁]) (by simp [h₂]) (by simp [h₃]) L' ξ' hb' hh' h0

end Printed

end ZInQ.Contrib.HCMLattice

/-! ## The combined leaf: Shimura's analytic isomorphisms (`IsAnalyticIso`, biholomorphisms for the complex
structure of `E(ℂ)`) and Shimura's `s⁻¹𝔞`, `s⁻¹u` through `p`-components -/

namespace ZInQ.Contrib.HCMWeierstrass

open WeierstrassCurve.Affine (Point)
open ZInQ.Contrib.HCMDict (IsAnalyticUnif conjPt ShimuraThm54)
open ZInQ.Contrib.HCMLattice (locLat ideleComp diagP)

section Printed

open ZInQ.Contrib.TYZDecomp.CurveA ZInQ.Contrib.TYZGenus.CM ZInQ.Contrib.TYZGenus.RingClass
  ZInQ.RouteK.Rank5b NumberField TauCeti.GlobalNumberFields TauCeti.ClassFieldTheory Complex
  ZInQ.Contrib.TYZGenus.Shimura IsDedekindDomain Pointwise T5Glue

/-- **LEAF SHIMURA-5.4-LOCAL-BIHOLO (Shimura 1971 Thm 5.4 with the print's analytic isomorphisms and the print's
`s⁻¹𝔞`, `s⁻¹u`).** `ξ : ℂ/𝔞 → E(ℂ)` an analytic isomorphism (`IsAnalyticIso`: a biholomorphism for the complex
structure of `E(ℂ)` given by the charts `x`, `y`, `t = -x/y`) with `ξ(0) = O`, and `𝔟 = s⁻¹𝔞` the lattice of `K` with
`𝔟_p = s_p⁻¹𝔞_p` for every prime `p` (hcm-lattice's `locLat`, `ideleComp`). Then there is an analytic isomorphism
`ξ' : ℂ/𝔟 → E^σ(ℂ)` with `ξ(u)^σ = ξ'(s⁻¹u)`, where `v` represents `s⁻¹u` when `v ≡ s_p⁻¹u (mod 𝔟_p)` for every `p`.
Source: Shimura 1971 Thm 5.4 and §5.2 (numbers UNVERIFIED). Differences, each weaker or equal in either reading of
"analytic isomorphism": `ξ(0) = O` asked; no group law asked of `ξ'`; uniqueness dropped; short models only. -/
def ShimuraThm54LocalBiholo : Prop :=
  ∀ (m : ℕ) [NeZero m], Squarefree m →
  ∀ (e : SeparableClosure (QNeg m) →ₐ[ℚ] Qbar),
    ιC (e (algebraMap (QNeg m) (SeparableClosure (QNeg m)) QuadraticAlgebra.omega)) =
      I * (Real.sqrt m : ℂ) →
  ∀ (σ : ℂ ≃+* ℂ) (s : IdeleGroup (𝓞 (QNeg m)) (QNeg m)), ArtinCond m e σ s →
  ∀ (𝔞 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔞) →
  ∀ (𝔟 : Set (QNeg m)), (∃ L : PeriodPair, (L.lattice : Set ℂ) = kappa m '' 𝔟) →
    (∀ p : ℕ, p.Prime → locLat p 𝔟 = (fun x => ideleComp p s⁻¹ * x) '' locLat p 𝔞) →
  ∀ (E : WeierstrassCurve ℂ) [E.IsElliptic] [E.IsShortNF],
  ∀ ξ : ℂ → E.toAffine.Point, IsAnalyticIso E (kappa m '' 𝔞) ξ → ξ 0 = 0 →
    ∃ ξ' : ℂ → (E.map (σ : ℂ →+* ℂ)).toAffine.Point,
      IsAnalyticIso (E.map (σ : ℂ →+* ℂ)) (kappa m '' 𝔟) ξ' ∧
      ∀ u v : QNeg m, (∀ p : ℕ, p.Prime → diagP p v - ideleComp p s⁻¹ * diagP p u ∈ locLat p 𝔟) →
        conjPt (σ : ℂ →+* ℂ) (ξ (kappa m u)) = ξ' (kappa m v)

theorem shimuraThm54_of_localBiholo (h : ShimuraThm54LocalBiholo) : ShimuraThm54 := by
  intro m _ hm e he σ s hs 𝔞 h𝔞 E _ h₁ h₂ h₃ ξ hξ
  haveI : E.IsShortNF := ⟨h₁, h₂, h₃⟩
  obtain ⟨L, hL⟩ := h𝔞
  obtain ⟨L', hL'⟩ := ZInQ.Contrib.HCMLattice.exists_periodPair_sInvLat hm L hL s
  rw [isAnalyticUnif_iff_isAnalyticIso_zero] at hξ
  obtain ⟨ξ', hI', hcomm⟩ := h m hm e he σ s hs 𝔞 ⟨L, hL⟩ (sInvLat m s 𝔞) ⟨L', hL'⟩
    (fun p _ => ZInQ.Contrib.HCMLattice.locLat_sInvLat hm L hL s p) E ξ hξ.1 hξ.2
  have hk0 : kappa m 0 = 0 := by simp [kappa]
  have h0 : ξ' 0 = 0 := by
    have hrep : finPart s * algebraMap (QNeg m) (AfK m) 0 - algebraMap (QNeg m) (AfK m) 0 ∈ latHat m 𝔞 := by
      rw [map_zero, mul_zero, sub_zero, ← map_zero (algebraMap (QNeg m) (AfK m))]
      exact ZInQ.Contrib.HCMLattice.mem_latHat_of_mem
        ((ZInQ.Contrib.HCMLattice.mem_of_kappa L hL 0).2 (by rw [hk0]; exact zero_mem _))
    have := hcomm 0 0 fun p _ => ZInQ.Contrib.HCMLattice.rep_local_of_global hm L hL s hrep p
    rw [hk0, hξ.2] at this
    rw [← this]; rfl
  refine ⟨ξ', isAnalyticUnif_iff_isAnalyticIso_zero.2 ⟨hI', h0⟩, fun u v huv =>
    hcomm u v fun p _ => ZInQ.Contrib.HCMLattice.rep_local_of_global hm L hL s huv p⟩

/-- With `ξ(0) = O`, hcm-lattice's `IsAnalyticIso` (holomorphic into `ℙ²`, immersion, bijective on `ℂ/L`) is
equivalent to `HCMWeierstrass.IsAnalyticIso`. -/
theorem hcmLattice_isAnalyticIso_iff (W : WeierstrassCurve ℂ) [W.IsElliptic] [W.IsShortNF] (L : PeriodPair)
    (ξ : ℂ → W.toAffine.Point) (h0 : ξ 0 = 0) :
    ZInQ.Contrib.HCMLattice.IsAnalyticIso W L.lattice ξ ↔ IsAnalyticIso W L.lattice ξ := by
  have h₁ := WeierstrassCurve.IsShortNF.a₁ (W := W)
  have h₂ := WeierstrassCurve.IsShortNF.a₂ (W := W)
  have h₃ := WeierstrassCurve.IsShortNF.a₃ (W := W)
  constructor
  · intro h
    exact isAnalyticIso_of_isAnalyticUnif
      (ZInQ.Contrib.HCMLattice.isAnalyticUnif_of_holo W h₁ h₂ h₃ L ξ h.1 h.2.1 h0)
  · intro h
    exact ZInQ.Contrib.HCMLattice.isAnalyticIso_of_unif W h₁ h₂ h₃ L ξ
      (isAnalyticUnif_iff_isAnalyticIso_zero.2 ⟨h, h0⟩)

end Printed

end ZInQ.Contrib.HCMWeierstrass

#print axioms ZInQ.Contrib.HCMWeierstrass.shimuraThm54_of_localBiholo
#print axioms ZInQ.Contrib.HCMWeierstrass.hcmLattice_isAnalyticIso_iff
