import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.WeilParam
import ZInQKernel.Contrib.OneProof.GrossZagierHeegner.Heegner

/-! gz-conj, part 1: a lattice is determined by `g₂, g₃`; the conjugate lattice. -/

noncomputable section

open Filter Topology Complex

namespace ZInQ.GZConj

section Lattice

variable (L L' : PeriodPair)

theorem exists_deriv_ne : ∃ z ∉ L.lattice, L.derivWeierstrassP z ≠ 0 := by
  by_contra! h
  apply GZWeil.weierstrassP_not_const L
  have hUo : IsOpen (L.lattice : Set ℂ)ᶜ := L.isClosed_lattice.isOpen_compl
  have hc := (GZWeil.isConnected_compl_lattice L).isPreconnected
  refine ⟨L.weierstrassP (L.ω₁ / 2), fun z hz => ?_⟩
  exact hUo.is_const_of_deriv_eq_zero hc
    (fun w hw => (GZWeil.hasDerivAt_wp L hw).differentiableAt.differentiableWithinAt)
    (fun w hw => by rw [(GZWeil.hasDerivAt_wp L hw).deriv]; exact h w hw) hz
    L.ω₁_div_two_notMem_lattice

/-- **Local uniqueness.** Two Weierstrass functions with the same `g₂, g₃` and the same value and
derivative at a point (`℘' ≠ 0` there) agree near it, after the shift. -/
theorem local_eq_shift (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) {z0 δ : ℂ} (hz0 : z0 ∉ L.lattice)
    (hz1 : z0 + δ ∉ L'.lattice) (hx : L'.weierstrassP (z0 + δ) = L.weierstrassP z0)
    (hy : L'.derivWeierstrassP (z0 + δ) = L.derivWeierstrassP z0)
    (hy0 : L.derivWeierstrassP z0 ≠ 0) :
    ∀ᶠ z in 𝓝 z0, L'.weierstrassP (z + δ) = L.weierstrassP z := by
  set Ψ : ℂ → ℂ := fun z => L'.weierstrassP (z + δ) - L.weierstrassP z with hΨ
  have hwa : AnalyticAt ℂ (fun z : ℂ => z + δ) z0 := analyticAt_id.add analyticAt_const
  have hP'a : AnalyticAt ℂ (fun z => L'.weierstrassP (z + δ)) z0 :=
    AnalyticAt.comp (f := fun z : ℂ => z + δ) (L'.analyticOnNhd_weierstrassP _ hz1) hwa
  have hpa : AnalyticAt ℂ L.weierstrassP z0 := L.analyticOnNhd_weierstrassP _ hz0
  have hD'a : AnalyticAt ℂ (fun z => L'.derivWeierstrassP (z + δ)) z0 :=
    AnalyticAt.comp (f := fun z : ℂ => z + δ) (L'.analyticOnNhd_derivWeierstrassP _ hz1) hwa
  have hDa : AnalyticAt ℂ L.derivWeierstrassP z0 := L.analyticOnNhd_derivWeierstrassP _ hz0
  have hΨa : AnalyticAt ℂ Ψ z0 := hP'a.sub hpa
  have hΨ0 : Ψ z0 = 0 := by simp [hΨ, hx]
  have hevL : ∀ᶠ z in 𝓝 z0, z ∉ L.lattice := L.isClosed_lattice.isOpen_compl.mem_nhds hz0
  have hevL' : ∀ᶠ z in 𝓝 z0, z + δ ∉ L'.lattice :=
    (continuous_id.add continuous_const : Continuous fun z : ℂ => z + δ).continuousAt.eventually
      (L'.isClosed_lattice.isOpen_compl.mem_nhds hz1)
  have hden0 : L'.derivWeierstrassP (z0 + δ) + L.derivWeierstrassP z0 ≠ 0 := by
    rw [hy]; intro h; apply hy0; linear_combination h / 2
  have hevD : ∀ᶠ z in 𝓝 z0, L'.derivWeierstrassP (z + δ) + L.derivWeierstrassP z ≠ 0 :=
    (hD'a.add hDa).continuousAt.eventually_ne hden0
  set h : ℂ → ℂ := fun z => (4 * (L'.weierstrassP (z + δ) ^ 2 +
      L'.weierstrassP (z + δ) * L.weierstrassP z + L.weierstrassP z ^ 2) - L.g₂) /
      (L'.derivWeierstrassP (z + δ) + L.derivWeierstrassP z) with hh
  have hha : AnalyticAt ℂ h z0 := by
    refine AnalyticAt.div ?_ (hD'a.add hDa) hden0
    exact (analyticAt_const.mul (((hP'a.pow 2).add (hP'a.mul hpa)).add (hpa.pow 2))).sub
      analyticAt_const
  have hderiv : deriv Ψ =ᶠ[𝓝 z0] h * Ψ := by
    filter_upwards [hevL.eventually_nhds, hevL'.eventually_nhds, hevD] with z hzL hzL' hzD
    have hL0 : z ∉ L.lattice := hzL.self_of_nhds
    have hL1 : z + δ ∉ L'.lattice := hzL'.self_of_nhds
    have hcomp : HasDerivAt (fun z => L'.weierstrassP (z + δ)) (L'.derivWeierstrassP (z + δ) * 1) z :=
      HasDerivAt.comp (h := fun x : ℂ => x + δ) z (GZWeil.hasDerivAt_wp L' hL1) ((hasDerivAt_id' z).add_const δ)
    have hdΨ : HasDerivAt Ψ (L'.derivWeierstrassP (z + δ) * 1 - L.derivWeierstrassP z) z :=
      hcomp.sub (GZWeil.hasDerivAt_wp L hL0)
    rw [hdΨ.deriv]
    have r1 := L.derivWeierstrassP_sq z hL0
    have r2 := L'.derivWeierstrassP_sq (z + δ) hL1
    rw [← h2, ← h3] at r2
    simp only [Pi.mul_apply, hh, hΨ]
    field_simp
    linear_combination r2 - r1
  suffices hΨev : ∀ᶠ z in 𝓝 z0, Ψ z = 0 by
    filter_upwards [hΨev] with z hz
    exact sub_eq_zero.mp hz
  rw [← analyticOrderAt_eq_top]
  by_contra hne
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hne
  have hm0 : m ≠ 0 := by
    rintro rfl
    have := (hΨa.analyticOrderAt_eq_zero).mp (by rw [← hm]; rfl)
    exact this hΨ0
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have h1 : analyticOrderAt (deriv Ψ) z0 = n :=
    analyticOrderAt_deriv_of_pos hΨa (by rw [← hm]; rfl)
  rw [analyticOrderAt_congr hderiv, analyticOrderAt_mul hha hΨa, ← hm] at h1
  have : ((n.succ : ℕ) : ℕ∞) ≤ (n : ℕ∞) := by
    rw [← h1]; exact le_add_self
  norm_cast at this
  omega

/-- **A lattice is determined by `g₂` and `g₃`** (one inclusion). -/
theorem lattice_le_of_g (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) : L.lattice ≤ L'.lattice := by
  obtain ⟨z0, hz0, hy0⟩ := exists_deriv_ne L
  obtain ⟨z1, hz1, hx1⟩ := GZWeil.weierstrassP_surjective L' (L.weierstrassP z0)
  have hsq : L'.derivWeierstrassP z1 ^ 2 = L.derivWeierstrassP z0 ^ 2 := by
    rw [L'.derivWeierstrassP_sq z1 hz1, L.derivWeierstrassP_sq z0 hz0, hx1, h2, h3]
  obtain ⟨z2, hz2, hx2, hy2⟩ : ∃ z2 ∉ L'.lattice, L'.weierstrassP z2 = L.weierstrassP z0 ∧
      L'.derivWeierstrassP z2 = L.derivWeierstrassP z0 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact ⟨z1, hz1, hx1, h⟩
    · refine ⟨-z1, fun hm => hz1 (by simpa using L'.lattice.neg_mem hm), ?_, ?_⟩
      · rw [L'.weierstrassP_neg, hx1]
      · rw [L'.derivWeierstrassP_neg, h, neg_neg]
  set δ := z2 - z0 with hδdef
  have e : z0 + δ = z2 := by simp [δ]
  have hloc := local_eq_shift L L' h2 h3 hz0 (e ▸ hz2) (e ▸ hx2) (e ▸ hy2) hy0
  set U : Set ℂ := (L.lattice : Set ℂ)ᶜ ∩ ((fun z => z + δ) ⁻¹' (L'.lattice : Set ℂ))ᶜ with hU
  have hcount : ((L.lattice : Set ℂ) ∪ (fun z => z + δ) ⁻¹' (L'.lattice : Set ℂ)).Countable :=
    (GZWeil.countable_lattice L).union ((GZWeil.countable_lattice L').preimage (add_left_injective δ))
  have hUeq : U = ((L.lattice : Set ℂ) ∪ (fun z => z + δ) ⁻¹' (L'.lattice : Set ℂ))ᶜ := by
    rw [hU, Set.compl_union]
  have hUc : IsConnected U := hUeq ▸ hcount.isConnected_compl_of_one_lt_rank (by simp)
  have hΨa : AnalyticOnNhd ℂ (fun z => L'.weierstrassP (z + δ) - L.weierstrassP z) U :=
    fun z hz => (AnalyticAt.comp (f := fun z : ℂ => z + δ) (L'.analyticOnNhd_weierstrassP _ hz.2)
      (analyticAt_id.add analyticAt_const)).sub (L.analyticOnNhd_weierstrassP z hz.1)
  have hz0U : z0 ∈ U := ⟨hz0, show z0 + δ ∉ L'.lattice by rw [e]; exact hz2⟩
  have heq : Set.EqOn (fun z => L'.weierstrassP (z + δ) - L.weierstrassP z) 0 U :=
    hΨa.eqOn_zero_of_preconnected_of_eventuallyEq_zero hUc.isPreconnected hz0U
      (by filter_upwards [hloc] with z hz; simp [hz])
  have key : ∀ l ∈ L.lattice, l + δ ∈ L'.lattice := by
    intro l hl
    by_contra hl'
    have hT := GZWeil.tendsto_weierstrassP_cobounded L hl
    have hc : ContinuousAt (fun z => L'.weierstrassP (z + δ)) l :=
      (AnalyticAt.comp (f := fun z : ℂ => z + δ) (L'.analyticOnNhd_weierstrassP _ hl')
        (analyticAt_id.add analyticAt_const)).continuousAt
    have hev : (fun z => L'.weierstrassP (z + δ)) =ᶠ[𝓝[≠] l] L.weierstrassP := by
      have e1 : ∀ᶠ z in 𝓝[≠] l, z ∉ L.lattice := by
        filter_upwards [nhdsWithin_le_nhds (L.compl_lattice_sdiff_singleton_mem_nhds l),
          self_mem_nhdsWithin] with z hz hzl
        exact fun hm => hz ⟨hm, hzl⟩
      have e2 : ∀ᶠ z in 𝓝[≠] l, z + δ ∉ L'.lattice :=
        ((continuous_id.add continuous_const : Continuous fun z : ℂ => z + δ).continuousAt.eventually
          (L'.isClosed_lattice.isOpen_compl.mem_nhds hl')).filter_mono nhdsWithin_le_nhds
      filter_upwards [e1, e2] with z hz1 hz2
      have := heq ⟨hz1, hz2⟩
      simpa [sub_eq_zero] using this
    have hT' := hT.congr' hev.symm
    have hb : Tendsto (fun z => L'.weierstrassP (z + δ)) (𝓝[≠] l)
        (𝓝 (L'.weierstrassP (l + δ))) := hc.tendsto.mono_left nhdsWithin_le_nhds
    rw [← tendsto_norm_atTop_iff_cobounded] at hT'
    exact not_tendsto_atTop_of_tendsto_nhds hb.norm hT'
  have hδ : δ ∈ L'.lattice := by simpa using key 0 L.lattice.zero_mem
  intro l hl
  simpa using L'.lattice.sub_mem (key l hl) hδ

/-- **A lattice is determined by `g₂` and `g₃`.** -/
theorem lattice_eq_of_g (h2 : L.g₂ = L'.g₂) (h3 : L.g₃ = L'.g₃) : L.lattice = L'.lattice :=
  le_antisymm (lattice_le_of_g L L' h2 h3) (lattice_le_of_g L' L h2.symm h3.symm)

end Lattice


section ConjLattice

open scoped ComplexConjugate

/-- The complex conjugate `L̄` of a period pair. -/
def conjPP (L : PeriodPair) : PeriodPair where
  ω₁ := conj L.ω₁
  ω₂ := conj L.ω₂
  indep := by
    have := L.indep.map' Complex.conjLIE.toLinearEquiv.toLinearMap
      Complex.conjLIE.toLinearEquiv.ker
    convert this using 1
    ext i; fin_cases i <;> rfl

theorem mem_conjPP {L : PeriodPair} {x : ℂ} : x ∈ (conjPP L).lattice ↔ conj x ∈ L.lattice := by
  rw [PeriodPair.mem_lattice, PeriodPair.mem_lattice]
  constructor
  · rintro ⟨m, n, e⟩
    refine ⟨m, n, ?_⟩
    rw [← e]; simp [conjPP]
  · rintro ⟨m, n, e⟩
    refine ⟨m, n, ?_⟩
    have := congrArg conj e
    simp only [map_add, map_mul, map_intCast, Complex.conj_conj] at this
    simpa [conjPP] using this

/-- `l ↦ l̄`, `L → L̄`. -/
def conjEquiv (L : PeriodPair) : L.lattice ≃ (conjPP L).lattice where
  toFun l := ⟨conj (l : ℂ), mem_conjPP.2 (by simp)⟩
  invFun l := ⟨conj (l : ℂ), mem_conjPP.1 l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

theorem G_conjPP (L : PeriodPair) (n : ℕ) : (conjPP L).G n = conj (L.G n) := by
  rw [PeriodPair.G, PeriodPair.G, Complex.conj_tsum, ← (conjEquiv L).tsum_eq]
  congr 1
  ext l
  simp [conjEquiv]

theorem g₂_conjPP (L : PeriodPair) : (conjPP L).g₂ = conj L.g₂ := by
  rw [PeriodPair.g₂, PeriodPair.g₂, G_conjPP, map_mul, map_ofNat]

theorem g₃_conjPP (L : PeriodPair) : (conjPP L).g₃ = conj L.g₃ := by
  rw [PeriodPair.g₃, PeriodPair.g₃, G_conjPP, map_mul, map_ofNat]

/-- **A lattice with real `g₂, g₃` is stable under complex conjugation.** -/
theorem conj_mem_iff_of_real {L : PeriodPair} (h2 : conj L.g₂ = L.g₂) (h3 : conj L.g₃ = L.g₃)
    (x : ℂ) : conj x ∈ L.lattice ↔ x ∈ L.lattice := by
  have h := lattice_eq_of_g (conjPP L) L (by rw [g₂_conjPP, h2]) (by rw [g₃_conjPP, h3])
  rw [← mem_conjPP, h]

variable {L : PeriodPair} (hc : ∀ x, conj x ∈ L.lattice ↔ x ∈ L.lattice)

/-- `l ↦ l̄` on a conjugation-stable lattice. -/
def conjSelf : L.lattice ≃ L.lattice where
  toFun l := ⟨conj (l : ℂ), (hc l).2 l.2⟩
  invFun l := ⟨conj (l : ℂ), (hc l).2 l.2⟩
  left_inv l := by ext; simp
  right_inv l := by ext; simp

include hc in
theorem weierstrassP_conj (z : ℂ) : L.weierstrassP (conj z) = conj (L.weierstrassP z) := by
  rw [PeriodPair.weierstrassP, PeriodPair.weierstrassP, Complex.conj_tsum,
    ← (conjSelf hc).tsum_eq]
  congr 1
  ext l
  simp [conjSelf]

include hc in
theorem derivWeierstrassP_conj (z : ℂ) :
    L.derivWeierstrassP (conj z) = conj (L.derivWeierstrassP z) := by
  rw [PeriodPair.derivWeierstrassP, PeriodPair.derivWeierstrassP, map_neg, Complex.conj_tsum,
    ← (conjSelf hc).tsum_eq]
  congr 2
  ext l
  simp [conjSelf, map_ofNat]

end ConjLattice

section WeierPtConj

open scoped ComplexConjugate WeierstrassCurve.Affine
open WeierstrassCurve

/-- Complex conjugation as a `ℚ`-algebra map. -/
abbrev cq : ℂ →ₐ[ℚ] ℂ := (starRingEnd ℂ).toRatAlgHom

theorem cq_apply (z : ℂ) : cq z = conj z := rfl

theorem conj_algebraMap (q : ℚ) : conj (algebraMap ℚ ℂ q) = algebraMap ℚ ℂ q := cq.commutes q

/-- The period lattice of `E/ℚ` is stable under complex conjugation. -/
theorem conj_mem_iff_of_isPeriodLattice {E : WeierstrassCurve ℚ} {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (x : ℂ) : conj x ∈ L.lattice ↔ x ∈ L.lattice := by
  refine conj_mem_iff_of_real ?_ ?_ x
  · rw [hL.1, show (E⁄ℂ).c₄ = algebraMap ℚ ℂ E.c₄ from E.map_c₄ _, map_div₀, conj_algebraMap,
      map_ofNat]
  · rw [hL.2, show (E⁄ℂ).c₆ = algebraMap ℚ ℂ E.c₆ from E.map_c₆ _, map_div₀, conj_algebraMap,
      map_ofNat]

/-- **Complex conjugation commutes with `z ↦ (℘(z) − b₂/12, …)`** for the period lattice of a
curve over `ℚ`. -/
theorem map_conj_weierPt (E : WeierstrassCurve ℚ) [E.IsElliptic] {L : PeriodPair}
    (hL : ZInQ.GZHL3.IsPeriodLattice E L) (z : ℂ) :
    Affine.Point.map cq (ZInQ.GZHL3.weierPt E L z) = ZInQ.GZHL3.weierPt E L (conj z) := by
  have hc := conj_mem_iff_of_isPeriodLattice hL
  by_cases hz : z ∈ L.lattice
  · rw [GZHeegner.weierPt_eq_zero E L hz, GZHeegner.weierPt_eq_zero E L ((hc z).2 hz),
      Affine.Point.map_zero]
  · have hz' : conj z ∉ L.lattice := fun h => hz ((hc z).1 h)
    rw [GZHeegner.weierPt_eq_some E hL hz, GZHeegner.weierPt_eq_some E hL hz',
      Affine.Point.map_some]
    have hb : conj (E⁄ℂ).b₂ = (E⁄ℂ).b₂ := by
      rw [show (E⁄ℂ).b₂ = algebraMap ℚ ℂ E.b₂ from E.map_b₂ _, conj_algebraMap]
    have ha1 : conj (E⁄ℂ).a₁ = (E⁄ℂ).a₁ := conj_algebraMap _
    have ha3 : conj (E⁄ℂ).a₃ = (E⁄ℂ).a₃ := conj_algebraMap _
    simp only [cq_apply, map_sub, map_div₀, map_mul, map_ofNat, hb, ha1,
      ha3, weierstrassP_conj hc, derivWeierstrassP_conj hc]

end WeierPtConj

end ZInQ.GZConj
