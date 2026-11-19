import ZInQKernel.Contrib.RC53Assist.NewformPeriods.Reduction
import Mathlib.Analysis.Complex.RemovableSingularity
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# `ParametrizationPeriodsGlue` (G1) is a theorem

This file proves the named step `ParametrizationPeriodsGlue` (`G1`) of the reduction of
`NewformPeriodsRational`: for `g ∈ S₂(Γ₀(M))`, an elliptic curve `A/ℚ`, a nonconstant point
`(x, y)` of `A` over `ℚ(j, j_M) ⊆ ℚ((q))` (`IsModularPointQ`), and `c ≠ 0` with
`θx = c · ĝ · (2y + a₁x + a₃)` (`PullbackIsMultiple`), every period lattice `Lat` of `A`
(`IsLatticeOf`: `g₂ = c₄/12`, `g₃ = c₆/216`) satisfies `IsParamScale M g Lat c`, i.e.
`c (F_g(γτ) − F_g(τ)) ∈ Lat` for all `γ ∈ Γ₀(M)` and `τ ∈ ℍ`.

## Main results (all PROVED, standard axioms only)

* `parametrizationPeriodsGlue_holds : ParametrizationPeriodsGlue`.
* `newformPeriodsRational_of_prints_G0_G2`: `NewformPeriodsRational` from the two printed leaves
  (Shimura 1973, Theorem 1; Faltings 1983, Korollar 2) and the two remaining named steps
  `NewformOfModularCurveGlue` (G0) and `IsogenyLatticeGlue` (G2).
* `isParamScale_of_local_curve_point` (the analytic core): if `X` is meromorphic and
  `Γ₀(M)`-invariant on the upper half plane, and near one point `τ₀` the pair `(X, Y)` lies on
  `Y² = X³ − (g₂/4) X − g₃/4` with `X' = 2πi c g · 2Y`, `Y(τ₀) ≠ 0`, `g(τ₀) ≠ 0`, then
  `IsParamScale M g Lat c`.
* `modularFunctionQExpansion`: every element of `ℚ(j, j_M)` is the Laurent `q`-expansion of a
  `Γ₀(M)`-invariant meromorphic function on the upper half plane.

## Proof

1. *Weierstrass `℘`* (Mathlib's `PeriodPair.weierstrassP`): `℘` takes every value off the
   lattice (Liouville's theorem for `1/(℘ − w)`), and a local period of `℘` is a lattice vector
   (identity theorem for the meromorphic function `℘(z + ω) − ℘(z)`, and the pole of `℘` at `0`).
2. *Local lift*: with `℘(z₀) = X(τ₀)`, `℘'(z₀) = 2Y(τ₀)` and a local inverse of `℘` (inverse
   function theorem), `u = c F_g + (z₀ − c F_g(τ₀))` satisfies `℘ ∘ u = X` near `τ₀`, because
   both `u` and the local lift `℘⁻¹ ∘ X` have derivative `2πi c g` (`F_g' = 2πi g`).
3. *Analytic continuation*: `℘ ∘ u = X` on a punctured neighbourhood of every point of the
   connected upper half plane; for `γ ∈ Γ₀(M)` the period `ω = c (F_g(γτ) − F_g(τ))` does not
   depend on `τ`, and invariance of `X` gives `℘(u + ω) = ℘(u)` near `τ₀`, hence `ω ∈ Lat`.
4. *`q`-expansions* (`HasQExpansionAbove`): convergent Laurent expansions in `e^{2πiτ}` are
   compatible with sums, products (Cauchy product), reciprocals (the reciprocal of a power series
   with nonzero constant term is analytic at `0`), termwise differentiation (`θ` corresponds to
   `(2πi)⁻¹ d/dτ`) and are unique; they turn the formal identities of `IsModularPointQ` and
   `PullbackIsMultiple` into identities of functions near `∞`, and give a point `τ₀` near `∞`
   where the pull-back does not vanish (`x` is not constant).
5. *`ℚ(j, j_M)`*: `j` from Mathlib's `E₄`, `E₆` (coefficients through `B₄`, `B₆`), `j(Mτ)` through
   `M · γτ = γ'(Mτ)`, and closure under the field operations (`IntermediateField.adjoin_induction`).
6. *Coordinates*: `X + b₂/12` and `(2Y + a₁X + a₃)/2` satisfy `Y² = X³ − (c₄/48) X − c₆/864`,
   which is the curve of `Lat` when `g₂ = c₄/12`, `g₃ = c₆/216`.

No uniformization theorem `ℂ/Λ ≅ E(ℂ)` and no covering-space lifting is needed: step 1 replaces
surjectivity and injectivity of the uniformization by two properties of `℘` alone.

Classification: PROVED.
-/

noncomputable section

open Filter Topology Bornology Set Complex UpperHalfPlane CongruenceSubgroup
open scoped MatrixGroups

namespace ZInQ.Contrib.RC53Assist.NewformPeriodsG1

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Contrib.RC53Assist.NewformPeriods

/-! ### Three facts about the Weierstrass `℘` function -/

section Weierstrass

variable (L : PeriodPair)


/-- `ℂ \ Λ` is a punctured neighbourhood of every point. -/
theorem compl_lattice_mem_nhdsNE (z : ℂ) : (L.lattice : Set ℂ)ᶜ ∈ 𝓝[≠] z := by
  have h := L.compl_lattice_sdiff_singleton_mem_nhds z
  filter_upwards [nhdsWithin_le_nhds h, self_mem_nhdsWithin] with w hw hwz
  intro hwL
  exact hw ⟨hwL, hwz⟩

/-- `℘` tends to infinity at every lattice point. -/
theorem tendsto_weierstrassP_cobounded {l : ℂ} (hl : l ∈ L.lattice) :
    Tendsto L.weierstrassP (𝓝[≠] l) (cobounded ℂ) := by
  refine tendsto_cobounded_of_meromorphicOrderAt_neg ?_
  rw [L.order_weierstrassP l hl]
  decide

/-- **`℘` takes every value off the lattice.** -/
theorem exists_notMem_weierstrassP_eq (w : ℂ) : ∃ z, z ∉ L.lattice ∧ L.weierstrassP z = w := by
  by_contra! hno
  classical
  let G : ℂ → ℂ := fun z => if z ∈ L.lattice then 0 else (L.weierstrassP z - w)⁻¹
  have hGc : ∀ z ∉ L.lattice, G z = (L.weierstrassP z - w)⁻¹ := fun z hz =>
    ite_eq_right_iff.mpr (fun h => absurd h hz)
  have hGm : ∀ z ∈ L.lattice, G z = 0 := fun z hz => ite_eq_left_iff.mpr (fun h => absurd hz h)
  have hne : ∀ z ∉ L.lattice, L.weierstrassP z - w ≠ 0 := fun z hz => sub_ne_zero.mpr (hno z hz)
  have hGper : ∀ z l, l ∈ L.lattice → G (z + l) = G z := by
    intro z l hl
    by_cases hz : z ∈ L.lattice
    · rw [hGm z hz, hGm (z + l) (add_mem hz hl)]
    · have hzl : z + l ∉ L.lattice := fun h => hz (by simpa using sub_mem h hl)
      rw [hGc z hz, hGc (z + l) hzl, L.weierstrassP_add_coe z ⟨l, hl⟩]
  have hGdc : DifferentiableOn ℂ G (L.lattice : Set ℂ)ᶜ := by
    refine DifferentiableOn.congr ?_ (fun z hz => hGc z hz)
    exact fun z hz => ((L.analyticOnNhd_weierstrassP z hz).sub
      analyticAt_const).differentiableAt.inv (hne z hz) |>.differentiableWithinAt
  have hGd : Differentiable ℂ G := by
    intro z
    by_cases hz : z ∈ L.lattice
    · set s := ((L.lattice : Set ℂ) \ {z})ᶜ with hs_def
      have hs : s ∈ 𝓝 z := L.compl_lattice_sdiff_singleton_mem_nhds z
      have hsd : s \ {z} = (L.lattice : Set ℂ)ᶜ := by
        ext v
        simp only [hs_def, Set.mem_sdiff, mem_compl_iff, mem_singleton_iff, SetLike.mem_coe]
        constructor
        · rintro ⟨hv, hvz⟩ hvL
          exact hv ⟨hvL, hvz⟩
        · exact fun hvL => ⟨fun h => hvL h.1, fun h => hvL (h ▸ hz)⟩
      have hGcont : ContinuousAt G z := by
        rw [← continuousWithinAt_compl_self, ContinuousWithinAt, hGm z hz]
        refine Tendsto.congr' (eventually_of_mem (compl_lattice_mem_nhdsNE L z)
          (fun v hv => (hGc v hv).symm)) ?_
        have h1 := tendsto_weierstrassP_cobounded L hz
        have h2 : Tendsto (fun v => L.weierstrassP v - w) (𝓝[≠] z) (cobounded ℂ) := by
          rw [← tendsto_norm_atTop_iff_cobounded] at h1 ⊢
          exact tendsto_atTop_mono (fun v => norm_sub_norm_le (L.weierstrassP v) w)
            (tendsto_atTop_add_const_right _ (-‖w‖) h1)
        exact tendsto_inv₀_cobounded.comp h2
      exact ((Complex.differentiableOn_compl_singleton_and_continuousAt_iff hs).mp
        ⟨hsd ▸ hGdc, hGcont⟩).differentiableAt hs
    · exact (hGdc z hz).differentiableAt (L.isClosed_lattice.isOpen_compl.mem_nhds hz)
  have hb : IsBounded (Set.range G) :=
    (IsZLattice.isCompact_range_of_periodic L.lattice G hGd.continuous hGper).isBounded
  have hconst := hGd.apply_eq_apply_of_bounded hb (L.ω₁ / 2) 0
  rw [hGm 0 (zero_mem _), hGc _ L.ω₁_div_two_notMem_lattice] at hconst
  exact inv_ne_zero (hne _ L.ω₁_div_two_notMem_lattice) hconst

/-- **A local period of `℘` is a lattice vector.** If `℘(z + ω) = ℘(z)` for all `z ≠ z₀` near
`z₀`, then `ω ∈ Λ`. -/
theorem mem_lattice_of_eventually_weierstrassP_add {ω z₀ : ℂ}
    (h : ∀ᶠ z in 𝓝[≠] z₀, L.weierstrassP (z + ω) = L.weierstrassP z) : ω ∈ L.lattice := by
  set D : ℂ → ℂ := fun z => L.weierstrassP (z + ω) - L.weierstrassP z with hD
  have hDm : MeromorphicOn D Set.univ := by
    intro z _
    have h1 : MeromorphicAt (fun z => L.weierstrassP (z + ω)) z :=
      (L.meromorphic_weierstrassP (z + ω)).comp_analyticAt (g := fun z => z + ω) (by fun_prop)
    exact h1.sub (L.meromorphic_weierstrassP z)
  have htop : meromorphicOrderAt D z₀ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [h] with z hz
    simp [hD, hz]
  have htop' : meromorphicOrderAt D (-ω) = ⊤ :=
    hDm.meromorphicOrderAt_eq_top_of_isPreconnected isPreconnected_univ (Set.mem_univ _)
      (Set.mem_univ _) htop
  rw [meromorphicOrderAt_eq_top_iff] at htop'
  by_contra hω
  have hω' : -ω ∉ L.lattice := fun h' => hω (by simpa using neg_mem h')
  have hcont : Tendsto L.weierstrassP (𝓝[≠] (-ω)) (𝓝 (L.weierstrassP (-ω))) :=
    ((L.analyticOnNhd_weierstrassP (-ω) hω').continuousAt.tendsto).mono_left nhdsWithin_le_nhds
  have hshift : Tendsto (fun z => z + ω) (𝓝[≠] (-ω)) (𝓝[≠] 0) := by
    have h1 : Tendsto (fun z => z + ω) (𝓝 (-ω)) (𝓝 0) := by
      have h2 : Continuous fun z : ℂ => z + ω := by fun_prop
      have := h2.tendsto (-ω)
      rwa [neg_add_cancel] at this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (h1.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hz ⊢
    intro h0
    exact hz (by linear_combination h0)
  have hinf : Tendsto (fun z => L.weierstrassP (z + ω)) (𝓝[≠] (-ω)) (cobounded ℂ) :=
    (tendsto_weierstrassP_cobounded L (zero_mem _)).comp hshift
  have hinf' : Tendsto L.weierstrassP (𝓝[≠] (-ω)) (cobounded ℂ) := by
    refine hinf.congr' ?_
    filter_upwards [htop'] with z hz
    simpa [hD, sub_eq_zero] using hz
  exact hinf'.not_tendsto (Metric.disjoint_nhds_cobounded _).symm hcont

end Weierstrass

/-! ### The Eichler potential and Möbius maps on `ℂ` -/

/-- The derivative of the Eichler potential, as a function on `ℂ` through `ofComplex`. -/
theorem hasDerivAt_eichlerPotential_ofComplex {N : ℕ}
    (f : CuspForm (Gamma0 N : Subgroup (GL (Fin 2) ℝ)) 2) {τ : ℂ} (hτ : 0 < τ.im) :
    HasDerivAt (eichlerPotential f ∘ ofComplex) (2 * Real.pi * Complex.I * f (ofComplex τ)) τ := by
  have hd : DifferentiableOn ℂ (eichlerPotential f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (mdifferentiable_eichlerPotential f)
  have hda : DifferentiableAt ℂ (eichlerPotential f ∘ ofComplex) τ :=
    (hd τ hτ).differentiableAt (isOpen_upperHalfPlaneSet.mem_nhds hτ)
  have hD := congrFun (normalizedDeriv_eichlerPotential f) ⟨τ, hτ⟩
  simp only [Derivative.normalizedDerivOfComplex] at hD
  have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hderiv : deriv (eichlerPotential f ∘ ofComplex) τ =
      2 * Real.pi * Complex.I * f (ofComplex τ) := by
    rw [ofComplex_apply_of_im_pos hτ, ← hD]
    field_simp
  rw [← hderiv]
  exact hda.hasDerivAt

/-- A Möbius transformation of `SL(2, ℤ)`, read on `ℂ` through `ofComplex`, maps punctured
neighbourhoods of a point of the upper half plane into punctured neighbourhoods. -/
theorem tendsto_smul_ofComplex_nhdsNE (γ : SL(2, ℤ)) {τ₀ : ℂ} (hτ₀ : 0 < τ₀.im) :
    Tendsto (fun σ : ℂ => ((γ • ofComplex σ : ℍ) : ℂ)) (𝓝[≠] τ₀)
      (𝓝[≠] ((γ • ofComplex τ₀ : ℍ) : ℂ)) := by
  set a : ℂ := ((γ 0 0 : ℤ) : ℂ)
  set b : ℂ := ((γ 0 1 : ℤ) : ℂ)
  set c : ℂ := ((γ 1 0 : ℤ) : ℂ)
  set d : ℂ := ((γ 1 1 : ℤ) : ℂ)
  have hform : ∀ σ : ℂ, 0 < σ.im → ((γ • ofComplex σ : ℍ) : ℂ) = (a * σ + b) / (c * σ + d) := by
    intro σ hσ
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, ofComplex_apply_of_im_pos hσ]
    simp [a, b, c, d]
  have hden : c * τ₀ + d ≠ 0 := by
    have h := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) ⟨τ₀, hτ₀⟩
    intro h0
    apply h
    rw [UpperHalfPlane.denom]
    convert h0 using 2 <;> simp [c, d]
  have hdet : a * d - b * c = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rw [Matrix.det_fin_two] at h
    have h' : ((γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 : ℤ) : ℂ) = 1 := by rw [h]; simp
    push_cast at h'
    simp only [a, b, c, d]
    linear_combination h'
  have hr : HasDerivAt (fun σ : ℂ => (a * σ + b) / (c * σ + d))
      ((a * (c * τ₀ + d) - (a * τ₀ + b) * c) / (c * τ₀ + d) ^ 2) τ₀ := by
    have h1 : HasDerivAt (fun σ : ℂ => a * σ + b) a τ₀ := by
      simpa using ((hasDerivAt_id τ₀).const_mul a).add_const b
    have h2 : HasDerivAt (fun σ : ℂ => c * σ + d) c τ₀ := by
      simpa using ((hasDerivAt_id τ₀).const_mul c).add_const d
    exact h1.div h2 hden
  have hev : (fun σ : ℂ => ((γ • ofComplex σ : ℍ) : ℂ)) =ᶠ[𝓝 τ₀]
      (fun σ : ℂ => (a * σ + b) / (c * σ + d)) := by
    filter_upwards [isOpen_upperHalfPlaneSet.mem_nhds hτ₀] with σ hσ
    exact hform σ hσ
  have hm := hr.congr_of_eventuallyEq hev
  have hne : (a * (c * τ₀ + d) - (a * τ₀ + b) * c) / (c * τ₀ + d) ^ 2 ≠ 0 := by
    have : a * (c * τ₀ + d) - (a * τ₀ + b) * c = 1 := by linear_combination hdet
    rw [this]
    exact div_ne_zero one_ne_zero (pow_ne_zero 2 hden)
  exact hm.tendsto_nhdsNE hne

/-! ### The local lift -/

/-- **Local lift through `℘`.** Near `τ₀`, let `(X, Y)` be a point of `Y² = X³ − (g₂/4)X − g₃/4`
with `X' = h · 2Y` and `Y(τ₀) ≠ 0`, and let `z₀ ∉ L` with `℘(z₀) = X(τ₀)` and `℘'(z₀) = 2Y(τ₀)`.
If `u' = h` near `τ₀` and `u(τ₀) = z₀`, then `℘ ∘ u = X` near `τ₀`. -/
theorem eventually_weierstrassP_comp_eq {L : PeriodPair} {X Y h u : ℂ → ℂ} {τ₀ z₀ : ℂ}
    (hderiv : ∀ᶠ τ in 𝓝 τ₀, HasDerivAt X (h τ * (2 * Y τ)) τ)
    (hcurve : ∀ᶠ τ in 𝓝 τ₀, Y τ ^ 2 = X τ ^ 3 - L.g₂ / 4 * X τ - L.g₃ / 4)
    (hYc : ContinuousAt Y τ₀) (hY0 : Y τ₀ ≠ 0)
    (hz₀ : z₀ ∉ L.lattice) (hPz : L.weierstrassP z₀ = X τ₀)
    (hP'z : L.derivWeierstrassP z₀ = 2 * Y τ₀)
    (hu : ∀ᶠ τ in 𝓝 τ₀, HasDerivAt u (h τ) τ) (hu0 : u τ₀ = z₀) :
    ∀ᶠ τ in 𝓝 τ₀, L.weierstrassP (u τ) = X τ := by
  have hderivP : ∀ z ∉ L.lattice, HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
    intro z hz
    have := (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt
    rwa [L.deriv_weierstrassP] at this
  have hP : HasStrictDerivAt L.weierstrassP (L.derivWeierstrassP z₀) z₀ := by
    have := (L.analyticOnNhd_weierstrassP z₀ hz₀).hasStrictDerivAt
    rwa [L.deriv_weierstrassP] at this
  have hne : L.derivWeierstrassP z₀ ≠ 0 := by
    rw [hP'z]
    exact mul_ne_zero two_ne_zero hY0
  set φ := (hP.hasStrictFDerivAt_equiv hne).toOpenPartialHomeomorph L.weierstrassP with hφ
  have hcoe : (φ : ℂ → ℂ) = L.weierstrassP :=
    HasStrictFDerivAt.toOpenPartialHomeomorph_coe _
  have hsrc : z₀ ∈ φ.source := HasStrictFDerivAt.mem_toOpenPartialHomeomorph_source _
  have htgt : X τ₀ ∈ φ.target := by
    have := HasStrictFDerivAt.image_mem_toOpenPartialHomeomorph_target
      (hP.hasStrictFDerivAt_equiv hne)
    rwa [hPz] at this
  have hsymm0 : φ.symm (X τ₀) = z₀ := by
    rw [← hPz, ← hcoe]
    exact φ.left_inv hsrc
  have hXc : ContinuousAt X τ₀ := hderiv.self_of_nhds.continuousAt
  set v : ℂ → ℂ := fun τ => φ.symm (X τ) with hv
  have hvc : ContinuousAt v τ₀ := (φ.continuousAt_symm htgt).comp hXc
  have hv0 : v τ₀ = z₀ := hsymm0
  have hP'c : ContinuousAt L.derivWeierstrassP z₀ :=
    (L.analyticOnNhd_derivWeierstrassP z₀ hz₀).continuousAt
  have hP'v : ContinuousAt (fun τ => L.derivWeierstrassP (v τ)) τ₀ := by
    have hP'c' : ContinuousAt L.derivWeierstrassP (v τ₀) := by rw [hv0]; exact hP'c
    exact hP'c'.comp hvc
  have e1 : ∀ᶠ τ in 𝓝 τ₀, X τ ∈ φ.target := hXc.preimage_mem_nhds (φ.open_target.mem_nhds htgt)
  have e2 : ∀ᶠ τ in 𝓝 τ₀, v τ ∉ L.lattice := by
    have : (L.lattice : Set ℂ)ᶜ ∈ 𝓝 (v τ₀) := by
      rw [hv0]
      exact L.isClosed_lattice.isOpen_compl.mem_nhds hz₀
    exact hvc.preimage_mem_nhds this
  have e3 : ∀ᶠ τ in 𝓝 τ₀, L.derivWeierstrassP (v τ) + 2 * Y τ ≠ 0 := by
    have hc : ContinuousAt (fun τ => L.derivWeierstrassP (v τ) + 2 * Y τ) τ₀ :=
      hP'v.add (continuousAt_const.mul hYc)
    have hval : L.derivWeierstrassP (v τ₀) + 2 * Y τ₀ ≠ 0 := by
      rw [hv0, hP'z]
      intro h0
      apply hY0
      linear_combination h0 / 4
    exact hc.eventually_ne hval
  have e4 : ∀ᶠ τ in 𝓝 τ₀, Y τ ≠ 0 := hYc.eventually_ne hY0
  have hvd : ∀ᶠ τ in 𝓝 τ₀, HasDerivAt v (h τ) τ := by
    filter_upwards [e1, e2, e3, e4, hderiv, hcurve] with τ h1 h2 h3 h4 h5 h6
    have hright : L.weierstrassP (v τ) = X τ := by
      have := φ.right_inv h1
      rwa [hcoe] at this
    have hsign : L.derivWeierstrassP (v τ) = 2 * Y τ := by
      have hsq := L.derivWeierstrassP_sq (v τ) h2
      rw [hright] at hsq
      have hprod : (L.derivWeierstrassP (v τ) - 2 * Y τ) *
          (L.derivWeierstrassP (v τ) + 2 * Y τ) = 0 := by
        linear_combination hsq - 4 * h6
      rcases mul_eq_zero.mp hprod with h7 | h7
      · linear_combination h7
      · exact absurd h7 h3
    have hne' : L.derivWeierstrassP (v τ) ≠ 0 := by
      rw [hsign]
      exact mul_ne_zero two_ne_zero h4
    have hsymm : HasDerivAt φ.symm (L.derivWeierstrassP (v τ))⁻¹ (X τ) := by
      refine φ.hasDerivAt_symm h1 hne' ?_
      rw [hcoe]
      exact hderivP _ h2
    have hcomp := hsymm.comp τ h5
    have hval : (L.derivWeierstrassP (v τ))⁻¹ * (h τ * (2 * Y τ)) = h τ := by
      rw [hsign]
      field_simp
    rw [hval] at hcomp
    exact hcomp
  obtain ⟨ε, hε, hball⟩ := Metric.eventually_nhds_iff_ball.mp (hvd.and hu)
  have hconst : ∀ y ∈ Metric.ball τ₀ ε, (v - u) y = (v - u) τ₀ := by
    intro y hy
    refine Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball τ₀ ε).isPreconnected
      ?_ ?_ hy (Metric.mem_ball_self hε)
    · intro w hw
      exact ((hball w hw).1.sub (hball w hw).2).differentiableAt.differentiableWithinAt
    · intro w hw
      have := ((hball w hw).1.sub (hball w hw).2).deriv
      simpa using this
  filter_upwards [Metric.ball_mem_nhds τ₀ hε, e1] with y hy hy1
  have h1 := hconst y hy
  simp only [Pi.sub_apply, hv0, hu0, sub_self, sub_eq_zero] at h1
  rw [← h1]
  have := φ.right_inv hy1
  rwa [hcoe] at this

/-! ### The analytic core -/

/-- A point of the curve of `L` with prescribed `x`-coordinate and `y`-coordinate of the right
sign: `℘(z₀) = X`, `℘'(z₀) = 2Y` for some `z₀ ∉ L`, whenever `Y² = X³ − (g₂/4) X − g₃/4`. -/
theorem exists_weierstrassP_point (L : PeriodPair) {x y : ℂ}
    (hxy : y ^ 2 = x ^ 3 - L.g₂ / 4 * x - L.g₃ / 4) :
    ∃ z₀, z₀ ∉ L.lattice ∧ L.weierstrassP z₀ = x ∧ L.derivWeierstrassP z₀ = 2 * y := by
  obtain ⟨z₁, hz₁, hPz₁⟩ := exists_notMem_weierstrassP_eq L x
  have hsq := L.derivWeierstrassP_sq z₁ hz₁
  rw [hPz₁] at hsq
  have hprod : (L.derivWeierstrassP z₁ - 2 * y) * (L.derivWeierstrassP z₁ + 2 * y) = 0 := by
    linear_combination hsq - 4 * hxy
  rcases mul_eq_zero.mp hprod with h | h
  · exact ⟨z₁, hz₁, hPz₁, by linear_combination h⟩
  · refine ⟨-z₁, fun h' => hz₁ (by simpa using neg_mem h'), ?_, ?_⟩
    · rw [L.weierstrassP_neg, hPz₁]
    · rw [L.derivWeierstrassP_neg]
      linear_combination -h

/-- **Analytic core of `G1`** (PROVED). Let `g ∈ S₂(Γ₀(M))`, `L` a lattice, `c ≠ 0`, and
`X, Y : ℂ → ℂ` with: `X` meromorphic and `Γ₀(M)`-invariant on the upper half plane; near some
`τ₀` with `Im τ₀ > 0`, `Y² = X³ − (g₂/4) X − g₃/4` and `X' = 2πi c g · 2Y`; `Y` continuous at
`τ₀`, `Y(τ₀) ≠ 0` and `g(τ₀) ≠ 0`. Then `IsParamScale M g L c`. -/
theorem isParamScale_of_local_curve_point {M : ℕ}
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) (L : PeriodPair) {c : ℂ} (hc : c ≠ 0)
    {X Y : ℂ → ℂ} (hXm : MeromorphicOn X {z : ℂ | 0 < z.im})
    (hXinv : ∀ γ ∈ Gamma0 M, ∀ τ : ℍ, X ((γ • τ : ℍ) : ℂ) = X τ)
    {τ₀ : ℂ} (hτ₀ : 0 < τ₀.im)
    (hderiv : ∀ᶠ τ in 𝓝 τ₀,
      HasDerivAt X (2 * Real.pi * Complex.I * c * g (ofComplex τ) * (2 * Y τ)) τ)
    (hcurve : ∀ᶠ τ in 𝓝 τ₀, Y τ ^ 2 = X τ ^ 3 - L.g₂ / 4 * X τ - L.g₃ / 4)
    (hYc : ContinuousAt Y τ₀) (hY0 : Y τ₀ ≠ 0) (hg0 : g (ofComplex τ₀) ≠ 0) :
    IsParamScale M g L c := by
  set U : Set ℂ := {z : ℂ | 0 < z.im} with hU
  have hUo : IsOpen U := isOpen_upperHalfPlaneSet
  have hUc : IsPreconnected U := (convex_halfSpace_im_gt 0).isPreconnected
  set F : ℂ → ℂ := eichlerPotential g ∘ ofComplex with hF
  set h : ℂ → ℂ := fun τ => 2 * Real.pi * Complex.I * c * g (ofComplex τ) with hh
  obtain ⟨z₀, hz₀, hPz₀, hP'z₀⟩ := exists_weierstrassP_point L hcurve.self_of_nhds
  set u : ℂ → ℂ := fun τ => c * F τ + (z₀ - c * F τ₀) with hu
  have hud : ∀ τ ∈ U, HasDerivAt u (h τ) τ := by
    intro τ hτ
    have := ((hasDerivAt_eichlerPotential_ofComplex g hτ).const_mul c).add_const (z₀ - c * F τ₀)
    convert this using 1
    simp only [hh]
    ring
  have hu0 : u τ₀ = z₀ := by simp [hu]
  have hloc : ∀ᶠ τ in 𝓝 τ₀, L.weierstrassP (u τ) = X τ :=
    eventually_weierstrassP_comp_eq (h := h) hderiv hcurve hYc hY0 hz₀ hPz₀ hP'z₀
      (by filter_upwards [hUo.mem_nhds hτ₀] with τ hτ using hud τ hτ) hu0
  -- the identity extends to a punctured neighbourhood of every point of the upper half plane
  have hum : ∀ τ ∈ U, MeromorphicAt (fun σ => L.weierstrassP (u σ)) τ := by
    intro τ hτ
    have hdu : DifferentiableOn ℂ u U :=
      fun σ hσ => (hud σ hσ).differentiableAt.differentiableWithinAt
    exact (L.meromorphic_weierstrassP (u τ)).comp_analyticAt (hdu.analyticAt (hUo.mem_nhds hτ))
  set D₁ : ℂ → ℂ := fun σ => L.weierstrassP (u σ) - X σ with hD₁
  have hD₁m : MeromorphicOn D₁ U := fun τ hτ => (hum τ hτ).sub (hXm τ hτ)
  have hD₁top : meromorphicOrderAt D₁ τ₀ = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [nhdsWithin_le_nhds hloc] with σ hσ
    simp [hD₁, hσ]
  have hglob : ∀ τ ∈ U, ∀ᶠ σ in 𝓝[≠] τ, L.weierstrassP (u σ) = X σ := by
    intro τ hτ
    have := hD₁m.meromorphicOrderAt_eq_top_of_isPreconnected hUc hτ₀ hτ hD₁top
    rw [meromorphicOrderAt_eq_top_iff] at this
    filter_upwards [this] with σ hσ
    simpa [hD₁, sub_eq_zero] using hσ
  refine ⟨hc, fun γ hγ τ => ?_⟩
  set τ₀' : ℍ := ⟨τ₀, hτ₀⟩ with hτ₀'
  set ω : ℂ := c * (eichlerPotential g (γ • τ₀') - eichlerPotential g τ₀') with hω
  have hper : c * (eichlerPotential g (γ • τ) - eichlerPotential g τ) = ω := by
    rw [hω, eichlerPotential_period_indep g hγ τ τ₀']
  rw [hper]
  set m : ℂ → ℂ := fun σ => ((γ • ofComplex σ : ℍ) : ℂ) with hm
  have hmt : Tendsto m (𝓝[≠] τ₀) (𝓝[≠] (m τ₀)) := tendsto_smul_ofComplex_nhdsNE γ hτ₀
  have hmU : m τ₀ ∈ U := (γ • ofComplex τ₀).im_pos
  have hshift : ∀ σ ∈ U, u (m σ) = u σ + ω := by
    intro σ hσ
    have h1 := eichlerPotential_period_indep g hγ (ofComplex σ) τ₀'
    simp only [hu, hF, hm, Function.comp_apply, ofComplex_apply, hω]
    linear_combination c * h1
  have hev : ∀ᶠ σ in 𝓝[≠] τ₀, L.weierstrassP (u σ + ω) = L.weierstrassP (u σ) := by
    have e1 : ∀ᶠ σ in 𝓝[≠] τ₀, L.weierstrassP (u (m σ)) = X (m σ) := hmt.eventually (hglob _ hmU)
    have e2 : ∀ᶠ σ in 𝓝[≠] τ₀, σ ∈ U := nhdsWithin_le_nhds (hUo.mem_nhds hτ₀)
    have e3 : ∀ᶠ σ in 𝓝[≠] τ₀, L.weierstrassP (u σ) = X σ := nhdsWithin_le_nhds hloc
    filter_upwards [e1, e2, e3] with σ h1 h2 h3
    rw [← hshift σ h2, h1, h3]
    have h4 := hXinv γ hγ (ofComplex σ)
    simp only [hm]
    rw [h4, ofComplex_apply_of_im_pos h2]
  have hh0 : h τ₀ ≠ 0 := by
    simp only [hh]
    exact mul_ne_zero (mul_ne_zero (by simp [Real.pi_ne_zero]) hc) hg0
  have hut : Tendsto u (𝓝[≠] τ₀) (𝓝[≠] z₀) := by
    have := (hud τ₀ hτ₀).tendsto_nhdsNE hh0
    rwa [hu0] at this
  set D₂ : ℂ → ℂ := fun z => L.weierstrassP (z + ω) - L.weierstrassP z with hD₂
  have hD₂m : MeromorphicAt D₂ z₀ := by
    have h1 : MeromorphicAt (fun z => L.weierstrassP (z + ω)) z₀ :=
      (L.meromorphic_weierstrassP (z₀ + ω)).comp_analyticAt (g := fun z => z + ω) (by fun_prop)
    exact h1.sub (L.meromorphic_weierstrassP z₀)
  rcases hD₂m.eventually_eq_zero_or_eventually_ne_zero with h0 | h0
  · apply mem_lattice_of_eventually_weierstrassP_add L (z₀ := z₀)
    filter_upwards [h0] with z hz
    simpa [hD₂, sub_eq_zero] using hz
  · exfalso
    obtain ⟨σ, hσ1, hσ2⟩ := ((hut.eventually h0).and hev).exists
    exact hσ1 (by simp [hD₂, hσ2])

/-! ### Convergent Laurent `q`-expansions -/

section QExpansion

/-- `H` is given by the Laurent `q`-expansion `h` above height `R`:
`H(τ) = Σ_{n ∈ ℤ} hₙ e^{2πinτ}` for `Im τ > R`. -/
def HasQExpansionAbove (h : LaurentSeries ℂ) (H : ℂ → ℂ) (R : ℝ) : Prop :=
  ∀ τ : ℂ, R < τ.im →
    HasSum (fun n : ℤ => h.coeff n * Complex.exp (2 * Real.pi * Complex.I * n * τ)) (H τ)

theorem HasQExpansionAbove.mono {h : LaurentSeries ℂ} {H : ℂ → ℂ} {R R' : ℝ}
    (e : HasQExpansionAbove h H R) (hR : R ≤ R') : HasQExpansionAbove h H R' :=
  fun τ hτ => e τ (lt_of_le_of_lt hR hτ)

/-- Laurent series have support bounded below. -/
theorem exists_coeff_eq_zero_of_lt (h : LaurentSeries ℂ) :
    ∃ m : ℕ, ∀ n : ℤ, n < -(m : ℤ) → h.coeff n = 0 := by
  refine ⟨(-h.order).toNat, fun n hn => HahnSeries.coeff_eq_zero_of_lt_order ?_⟩
  have := Int.self_le_toNat (-h.order)
  omega

/-- Reindexing a sum over `ℤ` with support in `[-m, ∞)` as a sum over `ℕ`. -/
theorem hasSum_int_iff_nat {f : ℤ → ℂ} {m : ℕ} (hf : ∀ n : ℤ, n < -(m : ℤ) → f n = 0) {s : ℂ} :
    HasSum f s ↔ HasSum (fun k : ℕ => f ((k : ℤ) - m)) s := by
  have hinj : Function.Injective (fun k : ℕ => (k : ℤ) - m) := fun a b hab => by
    simpa using hab
  rw [← hinj.hasSum_iff]
  · rfl
  · intro x hx
    apply hf
    by_contra hc
    exact hx ⟨(x + m).toNat, by simp only; omega⟩

/-- A Laurent series with support in `[-m, ∞)` is `q^{-m}` times a power series. -/
theorem eq_single_mul_ofPowerSeries (h : LaurentSeries ℂ) {m : ℕ}
    (hm : ∀ n : ℤ, n < -(m : ℤ) → h.coeff n = 0) :
    h = HahnSeries.single (-(m : ℤ)) (1 : ℂ) *
      HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk fun k => h.coeff ((k : ℤ) - m)) := by
  ext n
  have hn : n = (n + m) + (-(m : ℤ)) := by ring
  rw [hn, HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe]
  split_ifs with h0
  · exact hm _ (by omega)
  · rw [PowerSeries.coeff_mk]
    congr 1
    omega

/-- Coefficients of a product of Laurent series with supports in `[-m₁, ∞)` and `[-m₂, ∞)`. -/
theorem coeff_mul_shift (h₁ h₂ : LaurentSeries ℂ) {m₁ m₂ : ℕ}
    (hm₁ : ∀ n : ℤ, n < -(m₁ : ℤ) → h₁.coeff n = 0)
    (hm₂ : ∀ n : ℤ, n < -(m₂ : ℤ) → h₂.coeff n = 0) :
    (∀ n : ℤ, n < -((m₁ + m₂ : ℕ) : ℤ) → (h₁ * h₂).coeff n = 0) ∧
    ∀ k : ℕ, (h₁ * h₂).coeff ((k : ℤ) - (m₁ + m₂ : ℕ)) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k,
        h₁.coeff ((p.1 : ℤ) - m₁) * h₂.coeff ((p.2 : ℤ) - m₂) := by
  set P₁ := PowerSeries.mk fun k : ℕ => h₁.coeff ((k : ℤ) - m₁)
  set P₂ := PowerSeries.mk fun k : ℕ => h₂.coeff ((k : ℤ) - m₂)
  have hprod : h₁ * h₂ = HahnSeries.single (-((m₁ + m₂ : ℕ) : ℤ)) (1 : ℂ) *
      HahnSeries.ofPowerSeries ℤ ℂ (P₁ * P₂) := by
    conv_lhs => rw [eq_single_mul_ofPowerSeries h₁ hm₁, eq_single_mul_ofPowerSeries h₂ hm₂]
    rw [map_mul]
    have hs : HahnSeries.single (-((m₁ + m₂ : ℕ) : ℤ)) (1 : ℂ) =
        HahnSeries.single (-(m₁ : ℤ)) (1 : ℂ) * HahnSeries.single (-(m₂ : ℤ)) (1 : ℂ) := by
      rw [HahnSeries.single_mul_single, one_mul]
      congr 2
      omega
    rw [hs]
    ring
  refine ⟨fun n hn => ?_, fun k => ?_⟩
  · have e : n = (n + (m₁ + m₂ : ℕ)) + (-((m₁ + m₂ : ℕ) : ℤ)) := by ring
    rw [hprod, e, HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe]
    split_ifs with h0
    · rfl
    · omega
  · have e : (k : ℤ) - (m₁ + m₂ : ℕ) = (k : ℤ) + (-((m₁ + m₂ : ℕ) : ℤ)) := by ring
    rw [hprod, e, HahnSeries.coeff_single_mul_add, one_mul,
      HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_mul]
    simp [P₁, P₂]

theorem HasQExpansionAbove.add {h₁ h₂ : LaurentSeries ℂ} {H₁ H₂ : ℂ → ℂ} {R₁ R₂ : ℝ}
    (e₁ : HasQExpansionAbove h₁ H₁ R₁) (e₂ : HasQExpansionAbove h₂ H₂ R₂) :
    HasQExpansionAbove (h₁ + h₂) (fun τ => H₁ τ + H₂ τ) (max R₁ R₂) := by
  intro τ hτ
  have := (e₁ τ (lt_of_le_of_lt (le_max_left _ _) hτ)).add
    (e₂ τ (lt_of_le_of_lt (le_max_right _ _) hτ))
  convert this using 1
  funext n
  simp only [HahnSeries.coeff_add]
  ring

/-- The constant Laurent series `a` expands the constant function `a`. -/
theorem hasQExpansionAbove_C (a : ℂ) (R : ℝ) :
    HasQExpansionAbove (HahnSeries.C a) (fun _ => a) R := by
  intro τ _
  have : (fun n : ℤ => (HahnSeries.C a : LaurentSeries ℂ).coeff n *
      Complex.exp (2 * Real.pi * Complex.I * n * τ)) = fun n => if n = 0 then a else 0 := by
    funext n
    by_cases hn : n = 0
    · subst hn
      simp [HahnSeries.C_apply]
    · simp [HahnSeries.C_apply, hn, HahnSeries.coeff_single_of_ne hn]
  rw [this]
  exact hasSum_ite_eq 0 a

/-- **Cauchy product of convergent Laurent `q`-expansions.** -/
theorem HasQExpansionAbove.mul {h₁ h₂ : LaurentSeries ℂ} {H₁ H₂ : ℂ → ℂ} {R₁ R₂ : ℝ}
    (e₁ : HasQExpansionAbove h₁ H₁ R₁) (e₂ : HasQExpansionAbove h₂ H₂ R₂) :
    HasQExpansionAbove (h₁ * h₂) (fun τ => H₁ τ * H₂ τ) (max R₁ R₂) := by
  intro τ hτ
  obtain ⟨m₁, hm₁⟩ := exists_coeff_eq_zero_of_lt h₁
  obtain ⟨m₂, hm₂⟩ := exists_coeff_eq_zero_of_lt h₂
  obtain ⟨hm, hcoef⟩ := coeff_mul_shift h₁ h₂ hm₁ hm₂
  set E : ℤ → ℂ := fun n => Complex.exp (2 * Real.pi * Complex.I * n * τ) with hE
  have s₁ := e₁ τ (lt_of_le_of_lt (le_max_left _ _) hτ)
  have s₂ := e₂ τ (lt_of_le_of_lt (le_max_right _ _) hτ)
  rw [hasSum_int_iff_nat (m := m₁) (fun n hn => by simp [hm₁ n hn])] at s₁
  rw [hasSum_int_iff_nat (m := m₂) (fun n hn => by simp [hm₂ n hn])] at s₂
  rw [hasSum_int_iff_nat (m := m₁ + m₂) (fun n hn => by simp [hm n hn])]
  set f₁ : ℕ → ℂ := fun k => h₁.coeff ((k : ℤ) - m₁) * E ((k : ℤ) - m₁) with hf₁
  set f₂ : ℕ → ℂ := fun k => h₂.coeff ((k : ℤ) - m₂) * E ((k : ℤ) - m₂) with hf₂
  have n₁ : Summable fun k => ‖f₁ k‖ := s₁.summable.norm
  have n₂ : Summable fun k => ‖f₂ k‖ := s₂.summable.norm
  have hconv : ∀ k : ℕ, ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, f₁ p.1 * f₂ p.2 =
      (h₁ * h₂).coeff ((k : ℤ) - (m₁ + m₂ : ℕ)) * E ((k : ℤ) - (m₁ + m₂ : ℕ)) := by
    intro k
    rw [hcoef k, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun p hp => ?_)
    have hpk : p.1 + p.2 = k := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hexp : E ((p.1 : ℤ) - m₁) * E ((p.2 : ℤ) - m₂) = E ((k : ℤ) - (m₁ + m₂ : ℕ)) := by
      simp only [hE, ← Complex.exp_add]
      congr 1
      rw [← hpk]
      push_cast
      ring
    simp only [hf₁, hf₂]
    rw [← hexp]
    ring
  have hmain : HasSum (fun k : ℕ => ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, f₁ p.1 * f₂ p.2)
      (H₁ τ * H₂ τ) := by
    rw [← s₁.tsum_eq, ← s₂.tsum_eq, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm n₁ n₂]
    exact (summable_norm_sum_mul_antidiagonal_of_summable_norm n₁ n₂).of_norm.hasSum
  convert hmain using 1
  funext k
  rw [hconv k]

theorem norm_exp_two_pi_I_mul (n : ℤ) (σ : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * n * σ)‖ = Real.exp (-2 * Real.pi * n * σ.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

theorem exp_two_pi_I_mul_I (n : ℤ) (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * n * (t * Complex.I)) =
      ((Real.exp (-2 * Real.pi * n * t) : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]
  congr 1
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Termwise differentiation of a convergent Laurent `q`-expansion**: `H` is differentiable
above height `R` and `(2πi)⁻¹ H'` has the expansion `Σ n hₙ e^{2πinτ}`. -/
theorem HasQExpansionAbove.hasDerivAt {h : LaurentSeries ℂ} {H : ℂ → ℂ} {R : ℝ}
    (e : HasQExpansionAbove h H R) {τ : ℂ} (hτ : R < τ.im) :
    HasSum (fun n : ℤ => ((n : ℂ) * h.coeff n) * Complex.exp (2 * Real.pi * Complex.I * n * τ))
      (deriv H τ / (2 * Real.pi * Complex.I)) ∧ HasDerivAt H (deriv H τ) τ := by
  set ε : ℝ := (R + τ.im) / 2 with hε
  set ε' : ℝ := τ.im + 1 with hε'
  set U : Set ℂ := {σ | ε < σ.im ∧ σ.im < ε'} with hUdef
  have hU : IsOpen U :=
    (isOpen_lt continuous_const Complex.continuous_im).inter
      (isOpen_lt Complex.continuous_im continuous_const)
  have hτU : τ ∈ U := ⟨by rw [hε]; linarith, by rw [hε']; linarith⟩
  set F : ℤ → ℂ → ℂ := fun n σ => h.coeff n * Complex.exp (2 * Real.pi * Complex.I * n * σ)
    with hF
  have hnorm : ∀ n : ℤ, ∀ σ : ℂ, ‖F n σ‖ = ‖h.coeff n‖ * Real.exp (-2 * Real.pi * n * σ.im) := by
    intro n σ
    rw [hF, norm_mul, norm_exp_two_pi_I_mul]
  set u : ℤ → ℝ := fun n => ‖F n (ε * Complex.I)‖ + ‖F n (ε' * Complex.I)‖ with hu
  have hus : Summable u := by
    have h1 := (e (ε * Complex.I) (by simp; rw [hε]; linarith)).summable.norm
    have h2 := (e (ε' * Complex.I) (by simp; rw [hε']; linarith)).summable.norm
    exact h1.add h2
  have hle : ∀ (n : ℤ) (σ : ℂ), σ ∈ U → ‖F n σ‖ ≤ u n := by
    intro n σ hσ
    obtain ⟨h1, h2⟩ := hσ
    simp only [hu, hnorm, Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im,
      Complex.I_re, mul_one, mul_zero, add_zero]
    have hpi := Real.pi_pos
    have hn0 : 0 ≤ ‖h.coeff n‖ := norm_nonneg _
    rcases le_or_gt 0 n with hn | hn
    · have hn' : (0 : ℝ) ≤ n := by exact_mod_cast hn
      have : Real.exp (-2 * Real.pi * n * σ.im) ≤ Real.exp (-2 * Real.pi * n * ε) :=
        Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (mul_nonneg hpi.le hn') (sub_pos.mpr h1).le])
      nlinarith [Real.exp_pos (-2 * Real.pi * n * ε'), Real.exp_pos (-2 * Real.pi * n * ε)]
    · have hn' : (n : ℝ) < 0 := by exact_mod_cast hn
      have : Real.exp (-2 * Real.pi * n * σ.im) ≤ Real.exp (-2 * Real.pi * n * ε') :=
        Real.exp_le_exp.mpr (by
          nlinarith [mul_nonneg (mul_nonneg hpi.le (neg_nonneg.mpr hn'.le)) (sub_pos.mpr h2).le])
      nlinarith [Real.exp_pos (-2 * Real.pi * n * ε'), Real.exp_pos (-2 * Real.pi * n * ε)]
  have hFd : ∀ n : ℤ, HasDerivAt (F n) (h.coeff n * (Complex.exp
      (2 * Real.pi * Complex.I * n * τ) * (2 * Real.pi * Complex.I * n))) τ := by
    intro n
    have := (((hasDerivAt_id τ).const_mul (2 * Real.pi * Complex.I * n)).cexp).const_mul
      (h.coeff n)
    simpa [hF] using this
  have hdiff : ∀ n : ℤ, DifferentiableOn ℂ (F n) U := by
    intro n
    have : Differentiable ℂ (F n) := by
      intro σ
      simp only [hF]
      fun_prop
    exact this.differentiableOn
  set T : ℂ → ℂ := fun σ => ∑' n : ℤ, F n σ with hT
  have hTd : DifferentiableOn ℂ T U := differentiableOn_tsum_of_summable_norm hus hdiff hU hle
  have hTD := hasSum_deriv_of_summable_norm hus hdiff hU hle hτU
  have hHT : H =ᶠ[𝓝 τ] T := by
    filter_upwards [hU.mem_nhds hτU] with σ hσ
    exact ((e σ (by have := hσ.1; rw [hε] at this; linarith)).tsum_eq).symm
  have hderiv : deriv H τ = deriv T τ := hHT.deriv_eq
  refine ⟨?_, ?_⟩
  · rw [hderiv]
    have := hTD.div_const (2 * Real.pi * Complex.I)
    convert this using 1
    funext n
    rw [(hFd n).deriv]
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp
  · rw [hderiv]
    exact ((hTd.differentiableAt (hU.mem_nhds hτU)).hasDerivAt).congr_of_eventuallyEq hHT

/-- **Uniqueness of convergent Laurent `q`-expansions**: a Laurent series summing to `0` above
some height is `0`. -/
theorem HasQExpansionAbove.eq_zero {h : LaurentSeries ℂ} {H : ℂ → ℂ} {R : ℝ}
    (e : HasQExpansionAbove h H R) (hH : ∀ τ : ℂ, R < τ.im → H τ = 0) : h = 0 := by
  by_contra hne
  set n₀ : ℤ := h.order with hn₀
  have ha : h.coeff n₀ ≠ 0 := fun h0 => hne (HahnSeries.coeff_order_eq_zero.mp h0)
  set t₁ : ℝ := max R 0 + 1 with ht₁
  have hRt : ∀ t : ℝ, t₁ ≤ t → R < t := fun t ht => by
    have := le_max_left R 0
    linarith
  set f : ℝ → ℤ → ℂ := fun t n => h.coeff n * ((Real.exp (-2 * Real.pi * (n - n₀) * t) : ℝ) : ℂ)
    with hf
  set g : ℤ → ℂ := fun n => if n = n₀ then h.coeff n₀ else 0 with hg
  have hlow : ∀ n : ℤ, n < n₀ → h.coeff n = 0 := fun n hn =>
    HahnSeries.coeff_eq_zero_of_lt_order hn
  have hsplit : ∀ (n : ℤ) (t : ℝ), Real.exp (-2 * Real.pi * (n - n₀) * t) =
      Real.exp (-2 * Real.pi * n * t) * Real.exp (2 * Real.pi * n₀ * t) := by
    intro n t
    rw [← Real.exp_add]
    congr 1
    ring
  have hzero : ∀ t : ℝ, t₁ ≤ t → ∑' n, f t n = 0 := by
    intro t ht
    have hs := e (t * Complex.I) (by simpa using hRt t ht)
    rw [hH _ (by simpa using hRt t ht)] at hs
    have hs' := hs.mul_right (((Real.exp (2 * Real.pi * n₀ * t) : ℝ) : ℂ))
    rw [zero_mul] at hs'
    refine (HasSum.tsum_eq ?_)
    convert hs' using 1
    funext n
    simp only [hf, exp_two_pi_I_mul_I, hsplit]
    push_cast
    ring
  have hbound_s : Summable fun n : ℤ => ‖h.coeff n‖ * Real.exp (-2 * Real.pi * (n - n₀) * t₁) := by
    have hs := (e (t₁ * Complex.I) (by simpa using hRt t₁ le_rfl)).summable.norm
    have hs' := hs.mul_right (Real.exp (2 * Real.pi * n₀ * t₁))
    convert hs' using 1
    funext n
    rw [norm_mul, exp_two_pi_I_mul_I, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le,
      hsplit]
    ring
  have hab : ∀ n : ℤ, Tendsto (fun t => f t n) atTop (𝓝 (g n)) := by
    intro n
    rcases lt_trichotomy n n₀ with hn | hn | hn
    · have : (fun t => f t n) = fun _ => 0 := by
        funext t
        simp [hf, hlow n hn]
      rw [this]
      simp only [hg, hn.ne, ↓reduceIte]
      exact tendsto_const_nhds
    · subst hn
      have : (fun t => f t n₀) = fun _ => h.coeff n₀ := by
        funext t
        simp [hf]
      rw [this]
      simp only [hg, ↓reduceIte]
      exact tendsto_const_nhds
    · have hpos : (0 : ℝ) < (n : ℝ) - n₀ := by
        have : (n₀ : ℝ) < n := by exact_mod_cast hn
        linarith
      have h1 : Tendsto (fun t : ℝ => -2 * Real.pi * ((n : ℝ) - n₀) * t) atTop atBot := by
        apply tendsto_id.const_mul_atTop_of_neg
        nlinarith [Real.pi_pos]
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp (Real.tendsto_exp_atBot.comp h1)
      have h3 := h2.const_mul (h.coeff n)
      simp only [hg, hn.ne', ↓reduceIte]
      rw [← mul_zero (h.coeff n)]
      simpa [hf, Function.comp_def] using h3
  have hbound : ∀ᶠ t in atTop, ∀ n : ℤ,
      ‖f t n‖ ≤ ‖h.coeff n‖ * Real.exp (-2 * Real.pi * (n - n₀) * t₁) := by
    filter_upwards [eventually_ge_atTop t₁] with t ht n
    rw [hf, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]
    rcases lt_or_ge n n₀ with hn | hn
    · rw [hlow n hn, norm_zero, zero_mul, zero_mul]
    · have hn' : (0 : ℝ) ≤ (n : ℝ) - n₀ := by
        have : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
        linarith
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      apply Real.exp_le_exp.mpr
      have := Real.pi_pos
      nlinarith [mul_nonneg (mul_nonneg this.le hn') (sub_nonneg.mpr ht)]
  have hlim := tendsto_tsum_of_dominated_convergence hbound_s hab hbound
  have hg_sum : ∑' n, g n = h.coeff n₀ := by
    rw [hg]
    exact tsum_ite_eq n₀ _
  rw [hg_sum] at hlim
  have h0 : Tendsto (fun t => ∑' n, f t n) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop t₁] with t ht
    exact (hzero t ht).symm
  exact ha (tendsto_nhds_unique hlim h0)

theorem HasQExpansionAbove.add' {h₁ h₂ : LaurentSeries ℂ} {H₁ H₂ : ℂ → ℂ} {R : ℝ}
    (e₁ : HasQExpansionAbove h₁ H₁ R) (e₂ : HasQExpansionAbove h₂ H₂ R) :
    HasQExpansionAbove (h₁ + h₂) (fun τ => H₁ τ + H₂ τ) R := by
  simpa using e₁.add e₂

theorem HasQExpansionAbove.mul' {h₁ h₂ : LaurentSeries ℂ} {H₁ H₂ : ℂ → ℂ} {R : ℝ}
    (e₁ : HasQExpansionAbove h₁ H₁ R) (e₂ : HasQExpansionAbove h₂ H₂ R) :
    HasQExpansionAbove (h₁ * h₂) (fun τ => H₁ τ * H₂ τ) R := by
  simpa using e₁.mul e₂

theorem HasQExpansionAbove.const_mul {h : LaurentSeries ℂ} {H : ℂ → ℂ} {R : ℝ} (a : ℂ)
    (e : HasQExpansionAbove h H R) :
    HasQExpansionAbove (HahnSeries.C a * h) (fun τ => a * H τ) R :=
  (hasQExpansionAbove_C a R).mul' e

theorem HasQExpansionAbove.sub' {h₁ h₂ : LaurentSeries ℂ} {H₁ H₂ : ℂ → ℂ} {R : ℝ}
    (e₁ : HasQExpansionAbove h₁ H₁ R) (e₂ : HasQExpansionAbove h₂ H₂ R) :
    HasQExpansionAbove (h₁ - h₂) (fun τ => H₁ τ - H₂ τ) R := by
  intro τ hτ
  have := (e₁ τ hτ).sub (e₂ τ hτ)
  convert this using 1
  funext n
  simp only [HahnSeries.coeff_sub]
  ring

/-- The zero series expands only the zero function. -/
theorem HasQExpansionAbove.eq_zero_of_zero {H : ℂ → ℂ} {R : ℝ}
    (e : HasQExpansionAbove 0 H R) {τ : ℂ} (hτ : R < τ.im) : H τ = 0 := by
  have := e τ hτ
  simp only [HahnSeries.coeff_zero, zero_mul] at this
  exact this.unique hasSum_zero

/-- Two functions with the same expansion agree. -/
theorem HasQExpansionAbove.unique {h : LaurentSeries ℂ} {H₁ H₂ : ℂ → ℂ} {R₁ R₂ : ℝ}
    (e₁ : HasQExpansionAbove h H₁ R₁) (e₂ : HasQExpansionAbove h H₂ R₂) {τ : ℂ}
    (h₁ : R₁ < τ.im) (h₂ : R₂ < τ.im) : H₁ τ = H₂ τ :=
  (e₁ τ h₁).unique (e₂ τ h₂)

/-- Reindexing a sum over `ℤ` with support in `[a, ∞)` as a sum over `ℕ`. -/
theorem hasSum_int_iff_nat_add {f : ℤ → ℂ} {a : ℤ} (hf : ∀ n : ℤ, n < a → f n = 0) {s : ℂ} :
    HasSum f s ↔ HasSum (fun k : ℕ => f (a + k)) s := by
  have hinj : Function.Injective (fun k : ℕ => a + (k : ℤ)) := fun x y hxy => by
    simpa using hxy
  rw [← hinj.hasSum_iff]
  · rfl
  · intro n hn
    apply hf
    by_contra hc
    exact hn ⟨(n - a).toNat, by simp only; omega⟩

theorem exp_two_pi_I_add (a : ℤ) (k : ℕ) (τ : ℂ) :
    Complex.exp (2 * Real.pi * Complex.I * ((a + k : ℤ) : ℂ) * τ) =
      Complex.exp (2 * Real.pi * Complex.I * a * τ) *
        Complex.exp (2 * Real.pi * Complex.I * τ) ^ k := by
  rw [← Complex.exp_nat_mul, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem norm_exp_two_pi_I (τ : ℂ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * τ)‖ = Real.exp (-2 * Real.pi * τ.im) := by
  rw [Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- **Reciprocals of convergent Laurent `q`-expansions**: if `H` has the expansion `h`, then
`H⁻¹` has the expansion `h⁻¹` above some height. -/
theorem HasQExpansionAbove.inv {h : LaurentSeries ℂ} {H : ℂ → ℂ} {R : ℝ}
    (e : HasQExpansionAbove h H R) : ∃ R' : ℝ, HasQExpansionAbove h⁻¹ (fun τ => (H τ)⁻¹) R' := by
  rcases eq_or_ne h 0 with rfl | hne
  · refine ⟨R, fun τ hτ => ?_⟩
    have h0 : H τ = 0 := e.eq_zero_of_zero hτ
    simp only [inv_zero, HahnSeries.coeff_zero, zero_mul, h0]
    exact hasSum_zero
  set n₀ : ℤ := h.order with hn₀
  have hlow : ∀ n : ℤ, n < n₀ → h.coeff n = 0 := fun n hn =>
    HahnSeries.coeff_eq_zero_of_lt_order hn
  set b : ℕ → ℂ := fun k => h.coeff (n₀ + k) with hb
  have hb0 : b 0 ≠ 0 := by
    simp only [hb, Nat.cast_zero, add_zero]
    exact fun h0 => hne (HahnSeries.coeff_order_eq_zero.mp h0)
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ b with hp
  set R₁ : ℝ := R + 1 with hR₁
  set r₀ : NNReal := Real.toNNReal (Real.exp (-2 * Real.pi * R₁)) with hr₀
  have hr : ((r₀ : NNReal) : ℝ) = Real.exp (-2 * Real.pi * R₁) :=
    Real.coe_toNNReal _ (Real.exp_pos _).le
  have hsumm : Summable fun k : ℕ => ‖p k‖ * (r₀ : ℝ) ^ k := by
    have hs := (e (R₁ * Complex.I) (by simp [hR₁])).summable.norm
    have hinj : Function.Injective (fun k : ℕ => n₀ + (k : ℤ)) := fun x y hxy => by
      simpa using hxy
    have hs' := (hs.comp_injective hinj).mul_right (Real.exp (2 * Real.pi * n₀ * R₁))
    convert hs' using 1
    funext k
    have him : ((R₁ : ℂ) * Complex.I).im = R₁ := by simp
    simp only [Function.comp_apply, hp, FormalMultilinearSeries.ofScalars_norm, hb, norm_mul,
      norm_exp_two_pi_I_mul, hr, him]
    rw [← Real.exp_nat_mul, mul_assoc (‖h.coeff (n₀ + ↑k)‖), ← Real.exp_add]
    congr 2
    push_cast
    ring

  have hrad : ((r₀ : NNReal) : ENNReal) ≤ p.radius := p.le_radius_of_summable_norm hsumm
  have hrad0 : 0 < p.radius :=
    lt_of_lt_of_le (ENNReal.coe_pos.mpr (Real.toNNReal_pos.mpr (Real.exp_pos _))) hrad
  have hF := p.hasFPowerSeriesOnBall hrad0
  have hF0 : p.sum 0 = b 0 := by
    have := hF.hasSum (y := 0) (by simp [hrad0])
    simp only [zero_add] at this
    refine this.unique ?_
    have h1 : (fun n : ℕ => p n fun _ => (0 : ℂ)) = fun n => if n = 0 then b 0 else 0 := by
      funext n
      rw [hp, FormalMultilinearSeries.ofScalars_apply_eq]
      rcases n with _ | n
      · simp
      · simp
    rw [h1]
    exact hasSum_ite_eq 0 (b 0)
  have hFa : AnalyticAt ℂ p.sum 0 := hF.analyticAt
  have hinvA : AnalyticAt ℂ (fun w => (p.sum w)⁻¹) 0 := hFa.inv (by rw [hF0]; exact hb0)
  obtain ⟨p', hp'⟩ := hinvA
  set c : ℕ → ℂ := fun k => p'.coeff k with hc
  have ev1 : ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun k : ℕ => b k * w ^ k) (p.sum w) := by
    filter_upwards [hF.hasFPowerSeriesAt.eventually_hasSum] with w hw
    simp only [zero_add] at hw
    convert hw using 1
    funext k
    rw [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have ev2 : ∀ᶠ w in 𝓝 (0 : ℂ), HasSum (fun k : ℕ => c k * w ^ k) ((p.sum w)⁻¹) := by
    filter_upwards [hp'.eventually_hasSum] with w hw
    simp only [zero_add] at hw
    convert hw using 1
    funext k
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, smul_eq_mul, hc, mul_comm]
  have ev3 : ∀ᶠ w in 𝓝 (0 : ℂ), p.sum w ≠ 0 :=
    hFa.continuousAt.eventually_ne (by rw [hF0]; exact hb0)
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp ((ev1.and ev2).and ev3)
  set R₂ : ℝ := max R₁ (-Real.log δ / (2 * Real.pi)) with hR₂
  have hq : ∀ τ : ℂ, R₂ < τ.im → dist (Complex.exp (2 * Real.pi * Complex.I * τ)) 0 < δ := by
    intro τ hτ
    rw [dist_zero_right, norm_exp_two_pi_I]
    have h1 : -Real.log δ / (2 * Real.pi) < τ.im := lt_of_le_of_lt (le_max_right _ _) hτ
    have hpi := Real.pi_pos
    have h2 : -2 * Real.pi * τ.im < Real.log δ := by
      rw [div_lt_iff₀ (by positivity)] at h1
      linarith
    calc Real.exp (-2 * Real.pi * τ.im) < Real.exp (Real.log δ) := Real.exp_lt_exp.mpr h2
      _ = δ := Real.exp_log hδ
  set B : LaurentSeries ℂ := HahnSeries.single (-n₀) (1 : ℂ) *
    HahnSeries.ofPowerSeries ℤ ℂ (PowerSeries.mk c) with hB
  have hBlow : ∀ n : ℤ, n < -n₀ → B.coeff n = 0 := by
    intro n hn
    have e1 : n = (n + n₀) + (-n₀) := by ring
    rw [hB, e1, HahnSeries.coeff_single_mul_add, one_mul, PowerSeries.coeff_coe]
    simp [show n + n₀ < 0 by omega]
  have hBk : ∀ k : ℕ, B.coeff (-n₀ + k) = c k := by
    intro k
    have e1 : -n₀ + (k : ℤ) = (k : ℤ) + (-n₀) := by ring
    rw [hB, e1, HahnSeries.coeff_single_mul_add, one_mul, HahnSeries.ofPowerSeries_apply_coeff,
      PowerSeries.coeff_mk]
  have hHτ : ∀ τ : ℂ, R₂ < τ.im → H τ = Complex.exp (2 * Real.pi * Complex.I * n₀ * τ) *
      p.sum (Complex.exp (2 * Real.pi * Complex.I * τ)) := by
    intro τ hτ
    have hRτ : R < τ.im := by
      have := le_max_left R₁ (-Real.log δ / (2 * Real.pi))
      linarith
    have hs := e τ hRτ
    rw [hasSum_int_iff_nat_add (a := n₀) (fun n hn => by simp [hlow n hn])] at hs
    have hw := (((hball (hq τ hτ)).1).1).mul_left (Complex.exp (2 * Real.pi * Complex.I * n₀ * τ))
    refine hs.unique ?_
    convert hw using 1
    funext k
    rw [exp_two_pi_I_add]
    simp only [hb]
    ring
  have eB : HasQExpansionAbove B (fun τ => (H τ)⁻¹) R₂ := by
    intro τ hτ
    rw [hasSum_int_iff_nat_add (a := -n₀) (fun n hn => by simp [hBlow n hn])]
    have hw := (((hball (hq τ hτ)).1).2).mul_left
      (Complex.exp (2 * Real.pi * Complex.I * (-n₀ : ℤ) * τ))
    show HasSum _ (H τ)⁻¹
    rw [hHτ τ hτ, mul_inv]
    have hexp : (Complex.exp (2 * Real.pi * Complex.I * n₀ * τ))⁻¹ =
        Complex.exp (2 * Real.pi * Complex.I * (-n₀ : ℤ) * τ) := by
      rw [← Complex.exp_neg]
      congr 1
      push_cast
      ring
    rw [hexp]
    convert hw using 1
    funext k
    rw [hBk, exp_two_pi_I_add]
    ring
  -- `h * B = 1`
  have hHne : ∀ τ : ℂ, R₂ < τ.im → H τ ≠ 0 := by
    intro τ hτ
    rw [hHτ τ hτ]
    exact mul_ne_zero (Complex.exp_ne_zero _) (hball (hq τ hτ)).2
  have hR₂ : R ≤ R₂ := by
    have := le_max_left R₁ (-Real.log δ / (2 * Real.pi))
    linarith
  have ehB := (e.mono hR₂).mul' eB
  have e1 := hasQExpansionAbove_C (1 : ℂ) R₂
  rw [HahnSeries.C_one] at e1
  have hdiff := ehB.sub' e1
  have hzero : h * B - 1 = 0 := hdiff.eq_zero (fun τ hτ => by
    rw [mul_inv_cancel₀ (hHne τ hτ), sub_self])
  have hinv : h⁻¹ = B := inv_eq_of_mul_eq_one_right (sub_eq_zero.mp hzero)
  exact ⟨R₂, hinv ▸ eB⟩

end QExpansion

/-! ### The translation of the formal data -/

section Translation

theorem toComplexLaurent_add (x y : LaurentSeries ℚ) :
    toComplexLaurent (x + y) = toComplexLaurent x + toComplexLaurent y := by
  ext n
  simp

theorem toComplexLaurent_sub (x y : LaurentSeries ℚ) :
    toComplexLaurent (x - y) = toComplexLaurent x - toComplexLaurent y := by
  ext n
  simp

theorem toComplexLaurent_cQ (a : ℚ) : toComplexLaurent (cQ a) = HahnSeries.C (a : ℂ) := by
  rw [cQ, LaurentSeries.algebraMap_apply, toComplexLaurent, HahnSeries.map_C]
  rfl

/-- The `q`-expansion of a weight-two cusp form on `Γ₀(M)`, as a Laurent expansion on `ℂ`. -/
theorem hasQExpansionAbove_cuspForm {M : ℕ}
    (g : CuspForm (Gamma0 M : Subgroup (GL (Fin 2) ℝ)) 2) :
    HasQExpansionAbove (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 g))
      (fun τ => g (ofComplex τ)) 0 := by
  intro τ hτ
  have hg1 := one_mem_strictPeriods_Gamma0 M
  have : Fact (IsCusp OnePoint.infty (Gamma0 M : Subgroup (GL (Fin 2) ℝ))) :=
    ⟨Subgroup.isCusp_of_mem_strictPeriods one_pos hg1⟩
  have hs := ModularForm.hasSum_qExpansion g one_pos hg1 (ofComplex τ)
  rw [hasSum_int_iff_nat (m := 0) (fun n hn => by
    rw [PowerSeries.coeff_coe]
    simp [show n < 0 by omega])]
  convert hs using 1
  funext k
  rw [Nat.cast_zero, sub_zero, HahnSeries.ofPowerSeries_apply_coeff,
    ofComplex_apply_of_im_pos hτ]
  congr 1
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  simp only [Complex.ofReal_one, div_one, Int.cast_natCast]
  ring

end Translation

/-! ### Realized elements of `ℚ((q))` and the field `ℚ(j, j_M)` -/

section Realized

/-- `h ∈ ℚ((q))` is the `q`-expansion at `∞` of a `Γ₀(M)`-invariant meromorphic function on the
upper half plane. -/
def IsRealizedAt (M : ℕ) (h : LaurentSeries ℚ) : Prop :=
  ∃ H : ℂ → ℂ, MeromorphicOn H {z : ℂ | 0 < z.im} ∧
    (∀ γ ∈ Gamma0 M, ∀ τ : ℍ, H ((γ • τ : ℍ) : ℂ) = H τ) ∧
    ∃ R : ℝ, HasQExpansionAbove (toComplexLaurent h) H R

/-- The coefficientwise inclusion `ℚ((q)) → ℂ((q))` as a ring homomorphism. -/
def toComplexLaurentHom : LaurentSeries ℚ →+* LaurentSeries ℂ where
  toFun := toComplexLaurent
  map_one' := by
    have h1 := toComplexLaurent_cQ 1
    rw [cQ, map_one, Rat.cast_one, HahnSeries.C_one] at h1
    exact h1
  map_mul' := toComplexLaurent_mul
  map_zero' := toComplexLaurent_zero
  map_add' := toComplexLaurent_add

theorem IsRealizedAt.add {M : ℕ} {x y : LaurentSeries ℚ} (hx : IsRealizedAt M x)
    (hy : IsRealizedAt M y) : IsRealizedAt M (x + y) := by
  obtain ⟨X, hXm, hXi, Rx, eX⟩ := hx
  obtain ⟨Y, hYm, hYi, Ry, eY⟩ := hy
  refine ⟨fun τ => X τ + Y τ, hXm.add hYm, fun γ hγ τ => by beta_reduce; rw [hXi γ hγ, hYi γ hγ],
    max Rx Ry, ?_⟩
  rw [toComplexLaurent_add]
  exact eX.add eY

theorem IsRealizedAt.mul {M : ℕ} {x y : LaurentSeries ℚ} (hx : IsRealizedAt M x)
    (hy : IsRealizedAt M y) : IsRealizedAt M (x * y) := by
  obtain ⟨X, hXm, hXi, Rx, eX⟩ := hx
  obtain ⟨Y, hYm, hYi, Ry, eY⟩ := hy
  refine ⟨fun τ => X τ * Y τ, hXm.mul hYm, fun γ hγ τ => by beta_reduce; rw [hXi γ hγ, hYi γ hγ],
    max Rx Ry, ?_⟩
  rw [toComplexLaurent_mul]
  exact eX.mul eY

theorem IsRealizedAt.inv {M : ℕ} {x : LaurentSeries ℚ} (hx : IsRealizedAt M x) :
    IsRealizedAt M x⁻¹ := by
  obtain ⟨X, hXm, hXi, Rx, eX⟩ := hx
  obtain ⟨R', e'⟩ := eX.inv
  refine ⟨fun τ => (X τ)⁻¹, hXm.inv, fun γ hγ τ => by beta_reduce; rw [hXi γ hγ], R', ?_⟩
  have : toComplexLaurent x⁻¹ = (toComplexLaurent x)⁻¹ := map_inv₀ toComplexLaurentHom x
  rw [this]
  exact e'

theorem isRealizedAt_algebraMap (M : ℕ) (r : ℚ) :
    IsRealizedAt M (algebraMap ℚ (LaurentSeries ℚ) r) := by
  refine ⟨fun _ => (r : ℂ), MeromorphicOn.const _, fun _ _ _ => rfl, 0, ?_⟩
  have := toComplexLaurent_cQ r
  rw [cQ] at this
  rw [this]
  exact hasQExpansionAbove_C _ 0

/-- **Every element of `ℚ(j, j_M)` is realized** once `j` and `j_M` are. -/
theorem isRealizedAt_of_mem_modularFunctionFieldQ (M : ℕ) [NeZero M]
    (hj : IsRealizedAt M jInvariantQ) (hjM : IsRealizedAt M (qPow M jInvariantQ)) :
    ∀ h ∈ modularFunctionFieldQ M, IsRealizedAt M h := by
  intro h hh
  induction hh using IntermediateField.adjoin_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact hj
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact hjM
  | algebraMap r => exact isRealizedAt_algebraMap M r
  | add x y _ _ hx hy => exact hx.add hy
  | inv x _ hx => exact hx.inv
  | mul x y _ _ hx hy => exact hx.mul hy

theorem qPow_coeff_mul (M : ℕ) [NeZero M] (x : LaurentSeries ℚ) (n : ℤ) :
    (qPow M x).coeff ((M : ℤ) * n) = x.coeff n :=
  HahnSeries.embDomain_coeff

theorem qPow_coeff_of_notMem (M : ℕ) [NeZero M] (x : LaurentSeries ℚ) {k : ℤ}
    (hk : k ∉ Set.range (fun n : ℤ => (M : ℤ) * n)) : (qPow M x).coeff k = 0 :=
  HahnSeries.embDomain_of_notMem_range hk

/-- **The substitution `τ ↦ Mτ`** on `q`-expansions is `q ↦ q^M` (`qPow M`). -/
theorem hasQExpansionAbove_comp_mul (M : ℕ) [NeZero M] {x : LaurentSeries ℚ} {J : ℂ → ℂ}
    {R : ℝ} (e : HasQExpansionAbove (toComplexLaurent x) J R) :
    HasQExpansionAbove (toComplexLaurent (qPow M x)) (fun τ => J ((M : ℂ) * τ)) (R / M) := by
  intro τ hτ
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hMτ : R < ((M : ℂ) * τ).im := by
    rw [div_lt_iff₀ hM] at hτ
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    linarith
  have hs := e _ hMτ
  have hinj : Function.Injective (fun n : ℤ => (M : ℤ) * n) :=
    mul_right_injective₀ (by exact_mod_cast NeZero.ne M)
  rw [← hinj.hasSum_iff]
  · convert hs using 1
    funext n
    simp only [Function.comp_apply, toComplexLaurent_coeff, qPow_coeff_mul]
    congr 2
    push_cast
    ring
  · intro k hk
    rw [toComplexLaurent_coeff, qPow_coeff_of_notMem M x hk]
    simp

/-- `τ ↦ J(Mτ)` is `Γ₀(M)`-invariant when `J` is `SL₂(ℤ)`-invariant:
`M · γτ = γ'(Mτ)` with `γ' = [[a, Mb], [c/M, d]]`. -/
theorem comp_mul_invariant {J : ℂ → ℂ}
    (hJ : ∀ γ : SL(2, ℤ), ∀ τ : ℍ, J ((γ • τ : ℍ) : ℂ) = J τ) (M : ℕ) [NeZero M] :
    ∀ γ ∈ Gamma0 M, ∀ τ : ℍ, J ((M : ℂ) * ((γ • τ : ℍ) : ℂ)) = J ((M : ℂ) * τ) := by
  intro γ hγ τ
  rw [Gamma0_mem] at hγ
  obtain ⟨k, hk⟩ : (M : ℤ) ∣ γ 1 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd (γ 1 0) M).mp hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := Matrix.SpecialLinearGroup.det_coe γ
    rwa [Matrix.det_fin_two] at h
  set γ' : SL(2, ℤ) := ⟨!![γ 0 0, (M : ℤ) * γ 0 1; k, γ 1 1], by
    rw [Matrix.det_fin_two_of]
    rw [hk] at hdet
    linear_combination hdet⟩ with hγ'
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  set τM : ℍ := ⟨(M : ℂ) * τ, by
    simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
    exact mul_pos hM τ.im_pos⟩ with hτM
  have hkey : (M : ℂ) * ((γ • τ : ℍ) : ℂ) = ((γ' • τM : ℍ) : ℂ) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply, UpperHalfPlane.coe_specialLinearGroup_apply]
    simp only [hγ', hτM, UpperHalfPlane.coe_mk, Matrix.SpecialLinearGroup.coe_mk, algebraMap_int_eq,
      eq_intCast, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.empty_val', Matrix.cons_val_fin_one]
    rw [hk]
    push_cast
    have hden : ((M : ℂ) * k) * (τ : ℂ) + (γ 1 1 : ℂ) ≠ 0 := by
      have h := UpperHalfPlane.denom_ne_zero (γ : GL (Fin 2) ℝ) τ
      rw [UpperHalfPlane.denom] at h
      convert h using 1
      simp [hk]
    have hden' : (k : ℂ) * ((M : ℂ) * τ) + (γ 1 1 : ℂ) ≠ 0 := by
      convert hden using 1
      ring
    field_simp
  rw [hkey, hJ γ' τM]

end Realized

/-! ### The modular invariant `j` from the Eisenstein series `E₄`, `E₆` -/

section Eisenstein

theorem bernoulli_four_eq : bernoulli 4 = -1 / 30 := by
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_four]

theorem bernoulli'_five_eq : bernoulli' 5 = 0 := by
  have h1 : Nat.choose 5 2 = 10 := by decide
  have h2 : Nat.choose 5 3 = 10 := by decide
  rw [bernoulli'_def]
  norm_num [Finset.sum_range_succ, h1, h2]

theorem bernoulli_six_eq : bernoulli 6 = 1 / 42 := by
  have h1 : Nat.choose 6 2 = 15 := by decide
  have h2 : Nat.choose 6 3 = 20 := by decide
  have h3 : Nat.choose 6 4 = 15 := by decide
  rw [bernoulli_eq_bernoulli'_of_ne_one (by decide), bernoulli'_def]
  norm_num [Finset.sum_range_succ, h1, h2, h3, bernoulli'_five_eq]

/-- The `q`-expansion of the normalized Eisenstein series `E_k` of level one, as a Laurent
expansion on `ℂ`, for coefficients `b` matching Mathlib's `q`-expansion. -/
theorem hasQExpansionAbove_E {k : ℕ} (hk : 3 ≤ k) (b : PowerSeries ℚ)
    (hb : ∀ m : ℕ, (qExpansion 1 (ModularForm.E hk)).coeff m = ((PowerSeries.coeff m b : ℚ) : ℂ)) :
    HasQExpansionAbove (toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ b))
      (fun τ => ModularForm.E hk (ofComplex τ)) 0 := by
  intro τ hτ
  have hs := ModularForm.hasSum_qExpansion (f := ModularForm.E hk) one_pos
    one_mem_strictPeriods_SL (ofComplex τ)
  rw [hasSum_int_iff_nat (m := 0) (fun n hn => by
    rw [toComplexLaurent_coeff, PowerSeries.coeff_coe]
    simp [show n < 0 by omega])]
  convert hs using 1
  funext m
  rw [Nat.cast_zero, sub_zero, toComplexLaurent_coeff, HahnSeries.ofPowerSeries_apply_coeff, hb m,
    ofComplex_apply_of_im_pos hτ]
  congr 1
  rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
  congr 1
  simp only [Complex.ofReal_one, div_one, Int.cast_natCast]
  ring

theorem qExpansion_E₄_coeff (m : ℕ) :
    (qExpansion 1 (ModularForm.E (by norm_num : 3 ≤ 4))).coeff m =
      ((PowerSeries.coeff m eisensteinE4Q : ℚ) : ℂ) := by
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) m, eisensteinE4Q,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · rw [bernoulli_four_eq]
    push_cast
    norm_num

theorem qExpansion_E₆_coeff (m : ℕ) :
    (qExpansion 1 (ModularForm.E (by norm_num : 3 ≤ 6))).coeff m =
      ((PowerSeries.coeff m eisensteinE6Q : ℚ) : ℂ) := by
  rw [EisensteinSeries.E_qExpansion_coeff (by norm_num) (by decide) m, eisensteinE6Q,
    PowerSeries.coeff_mk]
  split_ifs with hm
  · simp
  · rw [bernoulli_six_eq]
    push_cast
    norm_num

open scoped ModularForm in
/-- Weight-`k` transformation law of a level-one modular form. -/
theorem modularForm_SL_smul {k : ℕ} (f : ModularForm 𝒮ℒ k) (γ : SL(2, ℤ)) (τ : ℍ) :
    f (γ • τ) = (denom γ τ) ^ k * f τ := by
  have h1 : (⇑f ∣[(k : ℤ)] γ) = ⇑f := by
    rw [ModularForm.SL_slash]
    exact SlashInvariantForm.slash_action_eqn f _ (MonoidHom.mem_range.mpr ⟨γ, rfl⟩)
  have h2 := congrFun h1 τ
  rw [ModularForm.SL_slash_apply] at h2
  have hd : (denom γ τ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
  rw [← h2, mul_comm, mul_assoc, zpow_neg, zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hd),
    mul_one]

theorem analyticAt_modularForm {k : ℕ} (f : ModularForm 𝒮ℒ k) {τ : ℂ} (hτ : 0 < τ.im) :
    AnalyticAt ℂ (fun σ => f (ofComplex σ)) τ := by
  have hd : DifferentiableOn ℂ (⇑f ∘ ofComplex) {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (ModularFormClass.holo f)
  exact hd.analyticAt (isOpen_upperHalfPlaneSet.mem_nhds hτ)

/-- **The modular invariant** `j = 1728 E₄³/(E₄³ − E₆²)`, read on `ℂ` through `ofComplex`, is
meromorphic on the upper half plane, `SL₂(ℤ)`-invariant, and has the Laurent `q`-expansion
`jInvariantQ` (PROVED). -/
theorem exists_jFunction : ∃ J : ℂ → ℂ, MeromorphicOn J {z : ℂ | 0 < z.im} ∧
    (∀ γ : SL(2, ℤ), ∀ τ : ℍ, J ((γ • τ : ℍ) : ℂ) = J τ) ∧
    ∃ R : ℝ, HasQExpansionAbove (toComplexLaurent jInvariantQ) J R := by
  set a : ℂ → ℂ := fun τ => ModularForm.E (by norm_num : 3 ≤ 4) (ofComplex τ) with ha
  set b : ℂ → ℂ := fun τ => ModularForm.E (by norm_num : 3 ≤ 6) (ofComplex τ) with hb
  refine ⟨fun τ => 1728 * (a τ * a τ * a τ) * (a τ * a τ * a τ - b τ * b τ)⁻¹, ?_, ?_, ?_⟩
  · intro τ hτ
    have h1 : MeromorphicAt a τ := (analyticAt_modularForm _ hτ).meromorphicAt
    have h2 : MeromorphicAt b τ := (analyticAt_modularForm _ hτ).meromorphicAt
    fun_prop
  · intro γ τ
    have hA : a ((γ • τ : ℍ) : ℂ) = (denom γ τ) ^ 4 * a τ := by
      simp only [ha, ofComplex_apply]
      exact modularForm_SL_smul _ γ τ
    have hB : b ((γ • τ : ℍ) : ℂ) = (denom γ τ) ^ 6 * b τ := by
      simp only [hb, ofComplex_apply]
      exact modularForm_SL_smul _ γ τ
    have hD : (denom γ τ) ≠ 0 := UpperHalfPlane.denom_ne_zero _ _
    beta_reduce
    rw [hA, hB]
    have hden : (denom γ τ ^ 4 * a τ) * (denom γ τ ^ 4 * a τ) * (denom γ τ ^ 4 * a τ) -
        (denom γ τ ^ 6 * b τ) * (denom γ τ ^ 6 * b τ) =
        denom γ τ ^ 12 * (a τ * a τ * a τ - b τ * b τ) := by ring
    rw [hden, mul_inv]
    have h12 : denom γ τ ^ 12 * (denom γ τ ^ 12)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero _ hD)
    linear_combination (1728 * (a τ * a τ * a τ) * (a τ * a τ * a τ - b τ * b τ)⁻¹) * h12
  · have e4 := hasQExpansionAbove_E (by norm_num : 3 ≤ 4) eisensteinE4Q qExpansion_E₄_coeff
    have e6 := hasQExpansionAbove_E (by norm_num : 3 ≤ 6) eisensteinE6Q qExpansion_E₆_coeff
    have den := ((e4.mul' e4).mul' e4).sub' (e6.mul' e6)
    obtain ⟨R', einv⟩ := den.inv
    have num := (hasQExpansionAbove_C (1728 : ℂ) 0).mul' ((e4.mul' e4).mul' e4)
    refine ⟨max 0 R', ?_⟩
    have full := num.mul einv
    have hser : toComplexLaurent jInvariantQ =
        HahnSeries.C (1728 : ℂ) * (toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) *
          toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) *
          toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q)) *
        (toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) *
          toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) *
          toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE4Q) -
          toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q) *
          toComplexLaurent (HahnSeries.ofPowerSeries ℤ ℚ eisensteinE6Q))⁻¹ := by
      change toComplexLaurentHom jInvariantQ = _
      rw [jInvariantQ]
      simp only [map_div₀, map_mul, map_sub, map_pow, map_ofNat]
      change (1728 : LaurentSeries ℂ) * toComplexLaurent _ ^ 3 /
        (toComplexLaurent _ ^ 3 - toComplexLaurent _ ^ 2) = _
      rw [div_eq_mul_inv]
      ring
    rw [hser]
    exact full

end Eisenstein

/-- **The `q`-expansion principle for `ℚ(j, j_M)`** (PROVED from `exists_jFunction` and the
closure of realized series under the field operations and the substitution `τ ↦ Mτ`). -/
theorem modularFunctionQExpansion_holds (M : ℕ) [NeZero M] :
    ∀ h ∈ modularFunctionFieldQ M, IsRealizedAt M h := by
  obtain ⟨J, hJm, hJinv, R, eJ⟩ := exists_jFunction
  have hj : IsRealizedAt M jInvariantQ := ⟨J, hJm, fun γ _ τ => hJinv γ τ, R, eJ⟩
  have hM : (0 : ℝ) < M := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne M))
  have hjM : IsRealizedAt M (qPow M jInvariantQ) := by
    refine ⟨fun τ => J ((M : ℂ) * τ), fun τ hτ => ?_, comp_mul_invariant hJinv M, R / M,
      hasQExpansionAbove_comp_mul M eJ⟩
    have hMτ : (M : ℂ) * τ ∈ {z : ℂ | 0 < z.im} := by
      show 0 < ((M : ℂ) * τ).im
      simp only [Complex.mul_im, Complex.natCast_re, Complex.natCast_im, zero_mul, add_zero]
      exact mul_pos hM hτ
    exact (hJm _ hMτ).comp_analyticAt (g := fun τ => (M : ℂ) * τ) (by fun_prop)
  exact isRealizedAt_of_mem_modularFunctionFieldQ M hj hjM

/-! ### The `q`-expansion principle and the proof of `G1` -/

/-- **The `q`-expansion principle for `ℚ(j, j_M)`** (a statement, PROVED below as
`modularFunctionQExpansion`). Every element `h` of `ℚ(j, j_M) ⊆ ℚ((q))`
(`modularFunctionFieldQ M`) is the `q`-expansion at `∞` of a `Γ₀(M)`-invariant meromorphic
function on the upper half plane: there are `H : ℂ → ℂ`, meromorphic on `{Im τ > 0}`, with
`H(γτ) = H(τ)` for all `γ ∈ Γ₀(M)` and `τ ∈ ℍ`, and `R ∈ ℝ` such that
`H(τ) = Σ_{n ∈ ℤ} hₙ e^{2πinτ}` (a convergent sum) whenever `Im τ > R`.

Proof outline: `j = 1728 E₄³ (E₄³ − E₆²)⁻¹`, built pointwise from the normalized Eisenstein
series of level one, is meromorphic and `SL₂(ℤ)`-invariant with Laurent expansion `jInvariantQ`
(`exists_jFunction`; the coefficients of `E₄`, `E₆` are `240 σ₃(n)`, `−504 σ₅(n)` because
`B₄ = −1/30` and `B₆ = 1/42`); `τ ↦ j(Mτ)` is `Γ₀(M)`-invariant with expansion
`qPow M jInvariantQ` (`comp_mul_invariant`, `hasQExpansionAbove_comp_mul`); and expansions are
compatible with sums, products and reciprocals (`HasQExpansionAbove.add`, `.mul`, `.inv`), so the
realized series form a subfield (`isRealizedAt_of_mem_modularFunctionFieldQ`). -/
def ModularFunctionQExpansion : Prop :=
  ∀ (M : ℕ) [NeZero M], ∀ h ∈ modularFunctionFieldQ M,
    ∃ H : ℂ → ℂ, MeromorphicOn H {z : ℂ | 0 < z.im} ∧
      (∀ γ ∈ Gamma0 M, ∀ τ : ℍ, H ((γ • τ : ℍ) : ℂ) = H τ) ∧
      ∃ R : ℝ, ∀ τ : ℂ, R < τ.im →
        HasSum (fun n : ℤ => ((h.coeff n : ℚ) : ℂ) *
          Complex.exp (2 * Real.pi * Complex.I * n * τ)) (H τ)

/-- **`G1` from the `q`-expansion principle** (PROVED): the analytic core
`isParamScale_of_local_curve_point` applied to the `℘`-normalized coordinates
`X + b₂/12`, `(2Y + a₁X + a₃)/2` of the realizations `X`, `Y` of `x`, `y`, at a point near `∞`
where the pull-back `X' = 2πi c g (2Y + a₁X + a₃)` does not vanish. -/
theorem parametrizationPeriodsGlue_of_qExpansion (hQ : ModularFunctionQExpansion) :
    ParametrizationPeriodsGlue := by
  intro M _ g A _ x y hpt c hc hpull Lat hLat
  obtain ⟨hx, hy, heq, hxnc⟩ := hpt
  obtain ⟨X, hXm, hXinv, Rx, hXs⟩ := hQ M x hx
  obtain ⟨Y, -, -, Ry, hYs⟩ := hQ M y hy
  set R : ℝ := max (max Rx Ry) 0 with hR
  have hRx : Rx ≤ R := le_trans (le_max_left _ _) (le_max_left _ _)
  have hRy : Ry ≤ R := le_trans (le_max_right _ _) (le_max_left _ _)
  have hR0 : 0 ≤ R := le_max_right _ _
  set x' := toComplexLaurent x with hx'
  set y' := toComplexLaurent y with hy'
  have eX : HasQExpansionAbove x' X R := fun τ hτ => by
    simpa [hx'] using hXs τ (lt_of_le_of_lt hRx hτ)
  have eY : HasQExpansionAbove y' Y R := fun τ hτ => by
    simpa [hy'] using hYs τ (lt_of_le_of_lt hRy hτ)
  set G : ℂ → ℂ := fun τ => g (ofComplex τ) with hG
  have eG : HasQExpansionAbove (HahnSeries.ofPowerSeries ℤ ℂ (qExpansion 1 g)) G R :=
    (hasQExpansionAbove_cuspForm g).mono hR0
  have eC : ∀ a : ℂ, HasQExpansionAbove (HahnSeries.C a) (fun _ => a) R :=
    fun a => hasQExpansionAbove_C a R
  -- the Weierstrass relation, as functions
  have heq2 : y * y + cQ A.a₁ * x * y + cQ A.a₃ * y =
      x * x * x + cQ A.a₂ * (x * x) + cQ A.a₄ * x + cQ A.a₆ := by
    linear_combination heq
  have heq' := congrArg toComplexLaurent heq2
  simp only [toComplexLaurent_add, toComplexLaurent_mul, toComplexLaurent_cQ] at heq'
  have eL : HasQExpansionAbove (y' * y' + HahnSeries.C (A.a₁ : ℂ) * x' * y' +
      HahnSeries.C (A.a₃ : ℂ) * y')
      (fun τ => Y τ * Y τ + (A.a₁ : ℂ) * X τ * Y τ + (A.a₃ : ℂ) * Y τ) R :=
    ((eY.mul' eY).add' (((eC _).mul' eX).mul' eY)).add' ((eC _).mul' eY)
  have eRt : HasQExpansionAbove (x' * x' * x' + HahnSeries.C (A.a₂ : ℂ) * (x' * x') +
      HahnSeries.C (A.a₄ : ℂ) * x' + HahnSeries.C (A.a₆ : ℂ))
      (fun τ => X τ * X τ * X τ + (A.a₂ : ℂ) * (X τ * X τ) + (A.a₄ : ℂ) * X τ + (A.a₆ : ℂ)) R :=
    ((((eX.mul' eX).mul' eX).add' ((eC _).mul' (eX.mul' eX))).add' ((eC _).mul' eX)).add' (eC _)
  rw [heq'] at eL
  have hW : ∀ τ : ℂ, R < τ.im → Y τ * Y τ + (A.a₁ : ℂ) * X τ * Y τ + (A.a₃ : ℂ) * Y τ =
      X τ * X τ * X τ + (A.a₂ : ℂ) * (X τ * X τ) + (A.a₄ : ℂ) * X τ + (A.a₆ : ℂ) :=
    fun τ hτ => eL.unique eRt hτ hτ
  -- the pull-back identity, as functions
  have hom : toComplexLaurent (omegaDenom A x y) =
      y' + y' + HahnSeries.C (A.a₁ : ℂ) * x' + HahnSeries.C (A.a₃ : ℂ) := by
    rw [omegaDenom, two_mul, toComplexLaurent_add, toComplexLaurent_add, toComplexLaurent_add,
      toComplexLaurent_mul, toComplexLaurent_cQ, toComplexLaurent_cQ]
  have eD : HasQExpansionAbove (y' + y' + HahnSeries.C (A.a₁ : ℂ) * x' + HahnSeries.C (A.a₃ : ℂ))
      (fun τ => Y τ + Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ)) R :=
    ((eY.add' eY).add' ((eC _).mul' eX)).add' (eC _)
  have eP := (eG.mul' eD).const_mul c
  rw [← hom, ← hpull] at eP
  have eθ : HasQExpansionAbove (toComplexLaurent (eulerOp x))
      (fun τ => deriv X τ / (2 * Real.pi * Complex.I)) R := by
    intro τ hτ
    have := (eX.hasDerivAt hτ).1
    convert this using 1
    funext n
    simp [hx']
  have hθ : ∀ τ : ℂ, R < τ.im → deriv X τ / (2 * Real.pi * Complex.I) =
      c * (G τ * (Y τ + Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ))) :=
    fun τ hτ => eθ.unique eP hτ hτ
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [Real.pi_ne_zero]
  have hXd : ∀ τ : ℂ, R < τ.im → HasDerivAt X
      (2 * Real.pi * Complex.I * c * G τ * (Y τ + Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ))) τ := by
    intro τ hτ
    have h1 := (eX.hasDerivAt hτ).2
    have h2 := hθ τ hτ
    rw [div_eq_iff h2pi] at h2
    rw [h2] at h1
    convert h1 using 1
    ring
  have hYd : ∀ τ : ℂ, R < τ.im → HasDerivAt Y (deriv Y τ) τ :=
    fun τ hτ => (eY.hasDerivAt hτ).2
  -- a point near `∞` where the pull-back does not vanish
  obtain ⟨τ₀, hτ₀R, hd0⟩ : ∃ τ₀ : ℂ, R < τ₀.im ∧ deriv X τ₀ ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    have hz := eθ.eq_zero (fun τ hτ => by rw [hcon τ hτ, zero_div])
    obtain ⟨n, hn0, hxn⟩ := hxnc
    have h1 := congrArg (fun z : LaurentSeries ℂ => z.coeff n) hz
    simp only [toComplexLaurent_coeff, eulerOp_coeff, HahnSeries.coeff_zero] at h1
    have h2 : (n : ℚ) * x.coeff n = 0 := by exact_mod_cast h1
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact hn0 (by exact_mod_cast h3)
    · exact hxn h3
  have hd0' := hd0
  rw [(hXd τ₀ hτ₀R).deriv] at hd0'
  have hG0 : G τ₀ ≠ 0 := fun h0 => hd0' (by rw [h0]; ring)
  have hD0 : Y τ₀ + Y τ₀ + (A.a₁ : ℂ) * X τ₀ + (A.a₃ : ℂ) ≠ 0 := fun h0 => hd0' (by rw [h0]; ring)
  -- the `℘`-normalized coordinates and the analytic core
  have hUo : ∀ᶠ τ in 𝓝 τ₀, R < τ.im :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hτ₀R
  obtain ⟨hg₂, hg₃⟩ := hLat
  refine isParamScale_of_local_curve_point g Lat hc
    (X := fun τ => X τ + (A.b₂ : ℂ) / 12)
    (Y := fun τ => (Y τ + Y τ + (A.a₁ : ℂ) * X τ + (A.a₃ : ℂ)) / 2)
    (fun τ hτ => (hXm τ hτ).add (MeromorphicAt.const _ τ))
    (fun γ hγ τ => by rw [hXinv γ hγ τ])
    (lt_of_le_of_lt hR0 hτ₀R) ?_ ?_ ?_ ?_ hG0
  · filter_upwards [hUo] with τ hτ
    have := (hXd τ hτ).add_const ((A.b₂ : ℂ) / 12)
    convert this using 1
    simp only [hG]
    ring
  · filter_upwards [hUo] with τ hτ
    have hw := hW τ hτ
    rw [hg₂, hg₃]
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
      WeierstrassCurve.b₄, WeierstrassCurve.b₆]
    push_cast
    linear_combination hw
  · have hXc := (eX.hasDerivAt hτ₀R).2.continuousAt
    have hYc := (hYd τ₀ hτ₀R).continuousAt
    exact ((((hYc.add hYc).add (continuousAt_const.mul hXc)).add continuousAt_const).div_const 2)
  · exact div_ne_zero hD0 two_ne_zero

/-- **The `q`-expansion principle for `ℚ(j, j_M)` holds** (PROVED). -/
theorem modularFunctionQExpansion : ModularFunctionQExpansion := by
  intro M _ h hh
  obtain ⟨H, hHm, hHi, R, eH⟩ := modularFunctionQExpansion_holds M h hh
  exact ⟨H, hHm, hHi, R, fun τ hτ => by simpa using eH τ hτ⟩

/-- **`G1` holds: `ParametrizationPeriodsGlue` is a theorem** (PROVED, standard axioms only). -/
theorem parametrizationPeriodsGlue_holds : ParametrizationPeriodsGlue :=
  parametrizationPeriodsGlue_of_qExpansion modularFunctionQExpansion

/-- **`NewformPeriodsRational` from the two printed leaves and the two remaining named steps**
`G0` (`NewformOfModularCurveGlue`) and `G2` (`IsogenyLatticeGlue`) (PROVED): `G1` is no longer a
hypothesis. -/
theorem newformPeriodsRational_of_prints_G0_G2
    (hS : Shimura1973Thm1RationalGamma0) (hF : Faltings1983Kor2EllipticQ)
    (h0 : NewformOfModularCurveGlue) (h2 : IsogenyLatticeGlue) :
    ZInQ.Contrib.CloudB3RC53.ModularWeil.NewformPeriodsRational :=
  newformPeriodsRational_of_prints hS hF h0 parametrizationPeriodsGlue_holds h2

end ZInQ.Contrib.RC53Assist.NewformPeriodsG1
