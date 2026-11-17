import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilParam

/-!
# cd-optimal: an analytic parametrization through `℘_L`, and uniqueness of the period lattice

Task cd-optimal (2026-11-16). Report: `docs/research/cd-optimal.md`; log: `scratch/cd-optimal/log.md`.

gz-weil's argument (`GrossZagierHeegner/WeilParam.lean`, C5–C7) for the eta-quotient model of `32a1`,
abstracted over the data: on an open preconnected `U ⊆ ℂ`, analytic `X, Y` with `Y² = X³ + A X + B`
and `X' = 2 Y Φ'` (`Φ' = F ≠ 0`), for a lattice `L` of `y² = x³ + A x + B`, `X = ℘_L(Φ + c₀)` on `U`
(`global_eq_gen`), and every `ω` with `X ∘ g = X`, `Φ ∘ g = Φ + ω` lies in `L` (`period_mem_gen`).

Applied to `U = ℂ ∖ L'`, `X = ℘_{L'}`, `Y = ℘'_{L'}/2`, `Φ = id`, it gives **uniqueness of the period
lattice**: two period pairs with the same `g₂, g₃` have the same lattice (`lattice_eq_of_g₂_g₃`).
No `sorry`, no `axiom`.
-/

noncomputable section

open Filter Topology Complex

namespace ZInQ.CdOpt

section Gen

variable (L : PeriodPair) {A B : ℂ} (hA : L.g₂ = -4 * A) (hB : L.g₃ = -4 * B)
  {U : Set ℂ} (hU : IsOpen U) {X Y Φ F : ℂ → ℂ}
  (hXa : ∀ σ ∈ U, AnalyticAt ℂ X σ) (hYa : ∀ σ ∈ U, AnalyticAt ℂ Y σ)
  (hFa : ∀ σ ∈ U, AnalyticAt ℂ F σ)
  (hΦ : ∀ σ ∈ U, HasDerivAt Φ (F σ) σ) (hX : ∀ σ ∈ U, HasDerivAt X (2 * Y σ * F σ) σ)
  (heq : ∀ σ ∈ U, Y σ ^ 2 = X σ ^ 3 + A * X σ + B)

include hA hB in
theorem relation_gen {z : ℂ} (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z ^ 2 = 4 * L.weierstrassP z ^ 3 + 4 * A * L.weierstrassP z + 4 * B := by
  rw [L.derivWeierstrassP_sq z hz, hA, hB]; ring

include hU hΦ in
theorem analyticAt_Φ_gen {σ : ℂ} (hσ : σ ∈ U) : AnalyticAt ℂ Φ σ := by
  have hd : DifferentiableOn ℂ Φ U := fun w hw => (hΦ w hw).differentiableAt.differentiableWithinAt
  exact hd.analyticAt (hU.mem_nhds hσ)

include hA hB hU hXa hYa hFa hΦ hX heq in
/-- **Local identity.** If `℘(z₀) = X(τ₀)`, `℘'(z₀) = 2Y(τ₀) ≠ 0`, then `℘(Φ + c₀) = X` near `τ₀`,
`c₀ = z₀ − Φ(τ₀)` (order of vanishing of `Ψ = ℘(Φ + c₀) − X`, `Ψ' = hΨ`, `Ψ(τ₀) = 0`). -/
theorem local_eq_gen {τ0 : ℂ} (hτ0 : τ0 ∈ U) (hy0 : Y τ0 ≠ 0) {z0 : ℂ} (hz0 : z0 ∉ L.lattice)
    (hx : L.weierstrassP z0 = X τ0) (hy : L.derivWeierstrassP z0 = 2 * Y τ0) :
    ∀ᶠ σ in 𝓝 τ0, L.weierstrassP (Φ σ + (z0 - Φ τ0)) = X σ := by
  set c0 := z0 - Φ τ0 with hc0
  set w : ℂ → ℂ := fun σ => Φ σ + c0 with hw
  have hwτ : w τ0 = z0 := by simp [hw, hc0]
  set Ψ : ℂ → ℂ := fun σ => L.weierstrassP (w σ) - X σ with hΨ
  have hwa : AnalyticAt ℂ w τ0 := (analyticAt_Φ_gen hU hΦ hτ0).add analyticAt_const
  have hwc : ContinuousAt w τ0 := hwa.continuousAt
  have hΨa : AnalyticAt ℂ Ψ τ0 :=
    ((L.analyticOnNhd_weierstrassP _ (hwτ ▸ hz0)).comp hwa).sub (hXa τ0 hτ0)
  have hΨ0 : Ψ τ0 = 0 := by simp [hΨ, hwτ, hx]
  have hevU : ∀ᶠ σ in 𝓝 τ0, σ ∈ U := hU.mem_nhds hτ0
  have hevL : ∀ᶠ σ in 𝓝 τ0, w σ ∉ L.lattice :=
    hwc.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds (hwτ ▸ hz0))
  have hden_c : ContinuousAt (fun σ => L.derivWeierstrassP (w σ) + 2 * Y σ) τ0 := by
    refine ContinuousAt.add ?_ ((hYa τ0 hτ0).continuousAt.const_mul 2)
    exact ContinuousAt.comp_of_eq (g := L.derivWeierstrassP) (f := w)
      (L.analyticOnNhd_derivWeierstrassP _ (hwτ ▸ hz0)).continuousAt hwc hwτ
  have hden0 : L.derivWeierstrassP (w τ0) + 2 * Y τ0 ≠ 0 := by
    rw [hwτ, hy]; intro h; apply hy0; linear_combination h / 4
  have hevD : ∀ᶠ σ in 𝓝 τ0, L.derivWeierstrassP (w σ) + 2 * Y σ ≠ 0 :=
    hden_c.eventually_ne hden0
  set h : ℂ → ℂ := fun σ => F σ *
    (4 * (L.weierstrassP (w σ) ^ 2 + L.weierstrassP (w σ) * X σ + X σ ^ 2 + A)) /
      (L.derivWeierstrassP (w σ) + 2 * Y σ) with hh
  have hha : AnalyticAt ℂ h τ0 := by
    have hpw : AnalyticAt ℂ (fun σ => L.weierstrassP (w σ)) τ0 :=
      (L.analyticOnNhd_weierstrassP _ (hwτ ▸ hz0)).comp hwa
    have hpw' : AnalyticAt ℂ (fun σ => L.derivWeierstrassP (w σ)) τ0 :=
      (L.analyticOnNhd_derivWeierstrassP _ (hwτ ▸ hz0)).comp hwa
    have hxa := hXa τ0 hτ0
    have hya := hYa τ0 hτ0
    have hfa := hFa τ0 hτ0
    refine AnalyticAt.div ?_ (hpw'.add (analyticAt_const.mul hya)) hden0
    exact hfa.mul
      (analyticAt_const.mul ((((hpw.pow 2).add (hpw.mul hxa)).add (hxa.pow 2)).add analyticAt_const))
  have hderiv : deriv Ψ =ᶠ[𝓝 τ0] h * Ψ := by
    filter_upwards [hevU.eventually_nhds, hevL.eventually_nhds, hevD] with σ hσU hσL hσD
    have hσ : σ ∈ U := hσU.self_of_nhds
    have hL' : w σ ∉ L.lattice := hσL.self_of_nhds
    have hdw : HasDerivAt w (F σ) σ := (hΦ σ hσ).add_const c0
    have hdΨ : HasDerivAt Ψ (L.derivWeierstrassP (w σ) * F σ - 2 * Y σ * F σ) σ :=
      ((ZInQ.GZWeil.hasDerivAt_wp L hL').comp σ hdw).sub (hX σ hσ)
    rw [hdΨ.deriv]
    have hrel := relation_gen L hA hB hL'
    have he := heq σ hσ
    simp only [Pi.mul_apply, hh, hΨ]
    field_simp
    linear_combination (F σ) * (hrel - 4 * he)
  suffices hΨev : ∀ᶠ σ in 𝓝 τ0, Ψ σ = 0 by
    filter_upwards [hΨev] with σ hσ
    exact sub_eq_zero.mp hσ
  rw [← analyticOrderAt_eq_top]
  by_contra hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := (hΨa.analyticOrderAt_eq_zero).mp (by rw [← hm]; rfl)
    exact this hΨ0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have h1 : analyticOrderAt (deriv Ψ) τ0 = n :=
    analyticOrderAt_deriv_of_pos hΨa (by rw [← hm]; rfl)
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hha hΨa, ← hm] at h1
  have : ((n.succ : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
    rw [← h1]; exact le_add_self
  norm_cast at this
  omega

variable (hUc : IsPreconnected U) (hF0 : ∀ σ ∈ U, F σ ≠ 0)

include hA hB hU hXa hYa hFa hΦ hX heq hUc hF0 in
/-- **Global identity.** Under the hypotheses of `local_eq_gen`, for every `σ ∈ U`,
`Φ(σ) + c₀ ∉ L` and `℘(Φ(σ) + c₀) = X(σ)`. -/
theorem global_eq_gen {τ0 : ℂ} (hτ0 : τ0 ∈ U) (hy0 : Y τ0 ≠ 0) {z0 : ℂ} (hz0 : z0 ∉ L.lattice)
    (hx : L.weierstrassP z0 = X τ0) (hy : L.derivWeierstrassP z0 = 2 * Y τ0)
    {σ : ℂ} (hσ : σ ∈ U) :
    Φ σ + (z0 - Φ τ0) ∉ L.lattice ∧ L.weierstrassP (Φ σ + (z0 - Φ τ0)) = X σ := by
  set c0 := z0 - Φ τ0 with hc0
  set w : ℂ → ℂ := fun σ => Φ σ + c0 with hw
  have hwτ : w τ0 = z0 := by simp [hw, hc0]
  set P : ℂ → Prop := fun s => w s ∉ L.lattice ∧ L.weierstrassP (w s) = X s with hP
  set S : Set ℂ := U ∩ {s | ∀ᶠ t in 𝓝 s, P t} with hS
  have hSo : IsOpen S := hU.inter isOpen_setOfPred_eventually_nhds
  have hwa : ∀ s ∈ U, AnalyticAt ℂ w s := fun s hs =>
    (analyticAt_Φ_gen hU hΦ hs).add analyticAt_const
  have hwd : ∀ s ∈ U, HasDerivAt w (F s) s := fun s hs => (hΦ s hs).add_const c0
  have hτ0S : τ0 ∈ S := by
    refine ⟨hτ0, ?_⟩
    have hevL : ∀ᶠ s in 𝓝 τ0, w s ∉ L.lattice :=
      (hwa _ hτ0).continuousAt.eventually
        (L.isClosed_lattice.isOpen_compl.mem_nhds (hwτ ▸ hz0))
    filter_upwards [hevL, local_eq_gen L hA hB hU hXa hYa hFa hΦ hX heq hτ0 hy0 hz0 hx hy]
      with s h1 h2
    exact ⟨h1, h2⟩
  have hcl : closure S ∩ U ⊆ S := by
    rintro σ1 ⟨hcl, hσ1⟩
    by_cases hσ1S : σ1 ∈ S
    · exact hσ1S
    have hfreq : ∃ᶠ s in 𝓝[≠] σ1, P s := by
      rw [Filter.frequently_iff]
      intro V hV
      obtain ⟨u, hu, hσu, huV⟩ := mem_nhdsWithin.mp hV
      obtain ⟨s0, hs0u, hs0S⟩ := mem_closure_iff.mp hcl u hu hσu
      have hne : s0 ≠ σ1 := fun h => hσ1S (h ▸ hs0S)
      exact ⟨s0, huV ⟨hs0u, hne⟩, hs0S.2.self_of_nhds⟩
    have hd1 : F σ1 ≠ 0 := hF0 σ1 hσ1
    have hwL : w σ1 ∉ L.lattice := by
      intro hin
      have hwt : Tendsto w (𝓝[≠] σ1) (𝓝[≠] (w σ1)) :=
        tendsto_nhdsWithin_iff.mpr ⟨(hwa σ1 hσ1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds,
          (hwd σ1 hσ1).eventually_ne hd1⟩
      have hc := (ZInQ.GZWeil.tendsto_weierstrassP_cobounded L hin).comp hwt
      rw [← tendsto_norm_atTop_iff_cobounded] at hc
      have hbig := hc.eventually (eventually_gt_atTop (‖X σ1‖ + 1))
      have hxc : ∀ᶠ s in 𝓝[≠] σ1, ‖X s‖ < ‖X σ1‖ + 1 := by
        have := (hXa σ1 hσ1).continuousAt.norm.eventually (gt_mem_nhds (lt_add_one ‖X σ1‖))
        exact this.filter_mono nhdsWithin_le_nhds
      obtain ⟨s, hs, hs1, hs2⟩ := (hfreq.and_eventually (hbig.and hxc)).exists
      simp only [Function.comp] at hs1
      rw [hs.2] at hs1
      linarith
    have hΨa : AnalyticAt ℂ (fun s => L.weierstrassP (w s) - X s) σ1 :=
      ((L.analyticOnNhd_weierstrassP _ hwL).comp (hwa σ1 hσ1)).sub (hXa σ1 hσ1)
    have hz : ∀ᶠ s in 𝓝 σ1, L.weierstrassP (w s) - X s = 0 := by
      rw [← hΨa.frequently_zero_iff_eventually_zero]
      exact hfreq.mono fun s hs => sub_eq_zero.mpr hs.2
    have hevL : ∀ᶠ s in 𝓝 σ1, w s ∉ L.lattice :=
      (hwa σ1 hσ1).continuousAt.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds hwL)
    refine ⟨hσ1, ?_⟩
    filter_upwards [hevL, hz] with s h1 h2
    exact ⟨h1, sub_eq_zero.mp h2⟩
  have hsub := hUc.subset_of_closure_inter_subset hSo ⟨τ0, hτ0, hτ0S⟩ hcl
  exact (hsub hσ).2.self_of_nhds

include hA hB hU hXa hYa hFa hΦ hX heq hUc hF0 in
/-- **Periods.** If some `Y(τ₀) ≠ 0`, `g` maps `U` into `U`, `X ∘ g = X` and `Φ ∘ g = Φ + ω` on `U`,
then `ω ∈ L`. -/
theorem period_mem_gen (hY : ∃ τ0 ∈ U, Y τ0 ≠ 0) {g : ℂ → ℂ} (hg : ∀ σ ∈ U, g σ ∈ U)
    (hXg : ∀ σ ∈ U, X (g σ) = X σ) {ω : ℂ} (hΦg : ∀ σ ∈ U, Φ (g σ) = Φ σ + ω) :
    ω ∈ L.lattice := by
  obtain ⟨τ, hτU, hYτ⟩ := hY
  obtain ⟨z1, hz1, hx1⟩ := ZInQ.GZWeil.weierstrassP_surjective L (X τ)
  have hrel := relation_gen L hA hB hz1
  have heqτ := heq τ hτU
  obtain ⟨z0, hz0, hx, hy⟩ : ∃ z0, z0 ∉ L.lattice ∧ L.weierstrassP z0 = X τ ∧
      L.derivWeierstrassP z0 = 2 * Y τ := by
    have hsq : (L.derivWeierstrassP z1 - 2 * Y τ) * (L.derivWeierstrassP z1 + 2 * Y τ) = 0 := by
      rw [hx1] at hrel
      linear_combination hrel - 4 * heqτ
    rcases mul_eq_zero.mp hsq with h | h
    · exact ⟨z1, hz1, hx1, by linear_combination h⟩
    · refine ⟨-z1, fun h' => hz1 (by simpa using neg_mem h'), by rw [L.weierstrassP_neg, hx1], ?_⟩
      rw [L.derivWeierstrassP_neg]; linear_combination -h
  set c0 := z0 - Φ τ with hc0
  set w : ℂ → ℂ := fun σ => Φ σ + c0 with hw
  have hwτ : w τ = z0 := by simp [hw, hc0]
  have hG := fun {σ : ℂ} (hσ : σ ∈ U) =>
    global_eq_gen L hA hB hU hXa hYa hFa hΦ hX heq hUc hF0 hτU hYτ hz0 hx hy hσ
  have hshift : ∀ σ ∈ U, w σ + ω = w (g σ) := by
    intro σ hσ
    simp only [hw, hΦg σ hσ]
    ring
  have hkey : ∀ σ ∈ U, L.weierstrassP (w σ + ω) = L.weierstrassP (w σ) := by
    intro σ hσ
    rw [hshift σ hσ, (hG (hg σ hσ)).2, (hG hσ).2, hXg σ hσ]
  set Ω : Set ℂ := {u | u ∉ L.lattice ∧ u + ω ∉ L.lattice} with hΩ
  have hΩc : IsPreconnected Ω := by
    have hc : ((L.lattice : Set ℂ) ∪ (fun u => u + ω) ⁻¹' (L.lattice : Set ℂ)).Countable :=
      (ZInQ.GZWeil.countable_lattice L).union
        ((ZInQ.GZWeil.countable_lattice L).preimage (add_left_injective ω))
    have := (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hc).isPreconnected
    convert this using 1
    ext u; simp [hΩ]
  have hsh : ∀ u, u + ω ∉ L.lattice → AnalyticAt ℂ (fun v => L.weierstrassP (v + ω)) u :=
    fun u hu => AnalyticAt.comp (g := L.weierstrassP) (f := fun v => v + ω) (x := u)
      (L.analyticOnNhd_weierstrassP _ hu) (analyticAt_id.add analyticAt_const)
  have hg1a : AnalyticOnNhd ℂ (fun u => L.weierstrassP (u + ω)) Ω := fun u hu => hsh u hu.2
  have hg2a : AnalyticOnNhd ℂ L.weierstrassP Ω := fun u hu => L.analyticOnNhd_weierstrassP _ hu.1
  have hu0 : w τ ∈ Ω := ⟨(hG hτU).1, by rw [hshift τ hτU]; exact (hG (hg τ hτU)).1⟩
  have hwa : AnalyticAt ℂ w τ := (analyticAt_Φ_gen hU hΦ hτU).add analyticAt_const
  have hwd : HasDerivAt w (F τ) τ := (hΦ τ hτU).add_const c0
  have hd1 : F τ ≠ 0 := hF0 τ hτU
  have hmap : 𝓝 (w τ) ≤ Filter.map w (𝓝 τ) := by
    rcases hwa.eventually_constant_or_nhds_le_map_nhds with h | h
    · exfalso
      have hne := hwd.eventually_ne hd1 (c := w τ)
      obtain ⟨s, hs1, hs2⟩ := ((h.filter_mono nhdsWithin_le_nhds).and hne).exists
      exact hs2 hs1
    · exact h
  have hev : (fun u => L.weierstrassP (u + ω)) =ᶠ[𝓝 (w τ)] L.weierstrassP := by
    refine Filter.Eventually.filter_mono hmap ?_
    rw [Filter.eventually_map]
    filter_upwards [hU.mem_nhds hτU] with s hs
    exact hkey s hs
  have hEq := hg1a.eqOn_of_preconnected_of_eventuallyEq hg2a hΩc hu0 hev
  by_contra hωL
  have h0L : (0 : ℂ) ∈ L.lattice := L.lattice.zero_mem
  have hev0 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∈ Ω := by
    have h1 : ∀ᶠ u in 𝓝[≠] (0 : ℂ), u ∉ L.lattice := by
      filter_upwards [nhdsWithin_le_nhds (s := ({0}ᶜ : Set ℂ))
        (L.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin] with u hu hu0
      exact fun huL => hu ⟨huL, hu0⟩
    have h2 : ∀ᶠ u in 𝓝 (0 : ℂ), u + ω ∉ L.lattice := by
      have hc : ContinuousAt (fun u : ℂ => u + ω) 0 := (continuous_id.add continuous_const).continuousAt
      exact hc.eventually (L.isClosed_lattice.isOpen_compl.mem_nhds (by simpa using hωL))
    filter_upwards [h1, h2.filter_mono nhdsWithin_le_nhds] with u hu1 hu2
    exact ⟨hu1, hu2⟩
  have hcont : ContinuousAt (fun u => L.weierstrassP (u + ω)) 0 :=
    (hsh 0 (by simpa using hωL)).continuousAt
  have hb : ∀ᶠ u in 𝓝[≠] (0 : ℂ), ‖L.weierstrassP (u + ω)‖ < ‖L.weierstrassP ω‖ + 1 := by
    have h0 : (fun u => ‖L.weierstrassP (u + ω)‖) 0 < ‖L.weierstrassP ω‖ + 1 := by simp
    exact (hcont.norm.eventually (gt_mem_nhds h0)).filter_mono nhdsWithin_le_nhds
  have hc := ZInQ.GZWeil.tendsto_weierstrassP_cobounded L h0L
  rw [← tendsto_norm_atTop_iff_cobounded] at hc
  have hbig := hc.eventually (eventually_gt_atTop (‖L.weierstrassP ω‖ + 1))
  obtain ⟨u, hu1, hu2, hu3⟩ := (hev0.and (hb.and hbig)).exists
  have he := hEq hu1
  simp only at he
  rw [he] at hu2
  linarith

end Gen

/-! ## Uniqueness of the period lattice -/

/-- **A lattice is determined by `g₂, g₃`** (one inclusion): if `g₂(L) = g₂(L')` and
`g₃(L) = g₃(L')`, then `L' ⊆ L`. `℘_{L'}` parametrizes the curve of `L`, so `℘_{L'} = ℘_L(· + c₀)` on
`ℂ ∖ L'` (`global_eq_gen`), and the periods of `℘_{L'}` lie in `L` (`period_mem_gen`). -/
theorem lattice_le_of_g₂_g₃ {L L' : PeriodPair} (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) :
    L'.lattice ≤ L.lattice := by
  intro ω hω
  set U : Set ℂ := (L'.lattice : Set ℂ)ᶜ with hUdef
  have hU : IsOpen U := L'.isClosed_lattice.isOpen_compl
  have hUc : IsPreconnected U := (ZInQ.GZWeil.isConnected_compl_lattice L').isPreconnected
  refine period_mem_gen L (A := -L'.g₂ / 4) (B := -L'.g₃ / 4) (by rw [h2]; ring) (by rw [h3]; ring)
    hU (X := L'.weierstrassP) (Y := fun z => L'.derivWeierstrassP z / 2) (Φ := id)
    (F := fun _ => 1)
    (fun σ hσ => L'.analyticOnNhd_weierstrassP σ hσ)
    (fun σ hσ => (L'.analyticOnNhd_derivWeierstrassP σ hσ).div_const)
    (fun σ _ => analyticAt_const)
    (fun σ _ => hasDerivAt_id σ)
    (fun σ hσ => by
      have := ZInQ.GZWeil.hasDerivAt_wp L' hσ
      convert this using 1; ring)
    (fun σ hσ => by
      have := L'.derivWeierstrassP_sq σ hσ
      linear_combination this / 4)
    hUc (fun _ _ => one_ne_zero) ?_ (g := fun σ => σ + ω) ?_ ?_ ?_
  · by_contra hcon
    push Not at hcon
    apply ZInQ.GZWeil.weierstrassP_not_const L'
    have hz₀ : L'.ω₁ / 2 ∈ U := L'.ω₁_div_two_notMem_lattice
    refine ⟨L'.weierstrassP (L'.ω₁ / 2), fun z hz => ?_⟩
    refine hU.is_const_of_deriv_eq_zero hUc
      (fun w hw => (ZInQ.GZWeil.hasDerivAt_wp L' hw).differentiableAt.differentiableWithinAt)
      (fun w hw => ?_) hz hz₀
    rw [(ZInQ.GZWeil.hasDerivAt_wp L' hw).deriv]
    have := hcon w hw
    simp only [Pi.zero_apply]
    linear_combination 2 * this
  · intro σ hσ hmem
    exact hσ (by simpa using sub_mem hmem hω)
  · intro σ _
    exact L'.weierstrassP_add_coe σ ⟨ω, hω⟩
  · intro σ _
    rfl

/-- **Two period pairs with the same `g₂, g₃` have the same lattice.** -/
theorem lattice_eq_of_g₂_g₃ {L L' : PeriodPair} (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) :
    L.lattice = L'.lattice :=
  le_antisymm (lattice_le_of_g₂_g₃ h2.symm h3.symm) (lattice_le_of_g₂_g₃ h2 h3)

end ZInQ.CdOpt
