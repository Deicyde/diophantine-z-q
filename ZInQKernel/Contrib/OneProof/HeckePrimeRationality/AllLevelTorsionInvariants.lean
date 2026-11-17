import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllLevelTorsionWeightThreeForms
import Mathlib.Analysis.Meromorphic.RCLike

/-!
# Actual Weierstrass invariants from nonzero torsion values

The invariants are Mathlib's lattice-defined `g₂ = 60 G₄` and `g₃ = 140 G₆`.
The cubic equation is summed only at non-lattice torsion points, with the
actual count of those points. Ordinary pole-cancelled distribution germs
supply the second-derivative normalization used for the square sum.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

open Complex Filter Set
open scoped Topology Real UpperHalfPlane

namespace ZInQ.Contrib.HeckePrimeRationality.TorsionInvariants

open ZInQ.Contrib.HeckePrimeRationality
open CompletedTheta TorsionWeierstrassData TorsionWeightThree
open WeierstrassDistributionNat

/-- The actual nonzero N-torsion indices. -/
def nonzeroIndices (N : ℕ) (hN : 0 < N) : Finset (Fin N × Fin N) :=
  Finset.univ.erase (WeierstrassDistributionNat.p0 N hN)

lemma card_nonzeroIndices (N : ℕ) (hN : 0 < N) : (nonzeroIndices N hN).card = N ^ 2 - 1 := by
  rw [nonzeroIndices, Finset.card_erase_of_mem (Finset.mem_univ _)]
  simp [Fintype.card_prod, pow_two]

lemma tp_eq_cn (N : ℕ) (p : Fin N × Fin N) (τ : ℍ) :
    CompletedTheta.torsionPoint N (p.1 : ℕ) (p.2 : ℕ) τ = TorsionDistributionNat.cn τ N p := rfl

lemma xValue_eq_wp_cn (N : ℕ) (hN : 0 < N) (p : Fin N × Fin N) (τ : ℍ) :
    xValue N (p.1 : ℕ) (p.2 : ℕ) τ = (ThetaWeierstrass.periodPair τ).weierstrassP
      (TorsionDistributionNat.cn τ N p) := by
  by_cases hp : p = WeierstrassDistributionNat.p0 N hN
  · subst p
    simp [WeierstrassDistributionNat.p0, TorsionDistributionNat.cn, xValue_zero]
  · have hz := WeierstrassDistributionNat.cn_notMem N hN τ hp
    have hg : ¬ ((N : ℤ) ∣ ((p.1 : ℕ) : ℤ) ∧ (N : ℤ) ∣ ((p.2 : ℕ) : ℤ)) := by
      intro hbad
      have hx : CompletedTheta.H τ (CompletedTheta.torsionPoint N (p.1 : ℕ) (p.2 : ℕ) τ) = 0 := by
        have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
        obtain ⟨m, hm⟩ := hbad.1
        obtain ⟨n, hn⟩ := hbad.2
        apply (ThetaWeierstrass.H_zero_iff_mem_lattice τ _).mpr
        rw [ThetaWeierstrass.mem_periodPair_lattice_iff]
        refine ⟨n, m, ?_⟩
        unfold CompletedTheta.torsionPoint
        rw [hm, hn]
        push_cast
        field_simp
        ring
      exact hz ((ThetaWeierstrass.H_zero_iff_mem_lattice τ _).mp hx)
    rw [xValue_of_good N (p.1 : ℕ) (p.2 : ℕ) τ hg, tp_eq_cn]

lemma yValue_eq_wpderiv_cn (N : ℕ) (hN : 0 < N) (p : Fin N × Fin N) (τ : ℍ) :
    yValue N (p.1 : ℕ) (p.2 : ℕ) τ = (ThetaWeierstrass.periodPair τ).derivWeierstrassP
      (TorsionDistributionNat.cn τ N p) := by
  rw [yValue_eq_actual N hN, tp_eq_cn]

/-- The actual lattice-normalized regular-part second derivative at the origin. -/
lemma wp_regular_second_zero (L : _root_.PeriodPair) :
    iteratedDeriv 2 (L.weierstrassPExcept 0) 0 = L.g₂ / 10 := by
  rw [L.iteratedDeriv_weierstrassPExcept_self]
  simp [PeriodPair.sumInvPow_zero, PeriodPair.g₂]
  ring

/-- The actual Weierstrass derivative has finite meromorphic order at zero. -/
lemma wpderiv_order_zero (L : _root_.PeriodPair) : meromorphicOrderAt L.derivWeierstrassP 0 = (-3 : ℤ) := by
  rw [meromorphicOrderAt_eq_int_iff (L.meromorphic_derivWeierstrassP 0)]
  refine ⟨fun z : ℂ => z ^ 3 * L.derivWeierstrassPExcept 0 z - 2, ?_, by simp, ?_⟩
  · exact (analyticAt_id.pow 3 |>.mul (L.analyticAt_derivWeierstrassPExcept 0)).sub analyticAt_const
  · filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : z ≠ 0 := hz
    have h := L.derivWeierstrassPExcept_def (0 : L.lattice) z
    simp only [Submodule.coe_zero, sub_zero] at h
    rw [show L.derivWeierstrassP z = L.derivWeierstrassPExcept 0 z - 2 / z ^ 3 by linear_combination -h]
    simp only [sub_zero, smul_eq_mul, _root_.zpow_neg, _root_.zpow_ofNat]
    field_simp [hz0]

/-- Differentiating the true cubic produces the second differential equation off critical points. -/
lemma wp_second_times_derivative (L : _root_.PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    L.derivWeierstrassP z * (2 * deriv L.derivWeierstrassP z - 12 * L.weierstrassP z ^ 2 + L.g₂) = 0 := by
  have hP := L.analyticOnNhd_weierstrassP z hz
  have hD := L.analyticOnNhd_derivWeierstrassP z hz
  have heq : (fun w : ℂ => L.derivWeierstrassP w ^ 2) =ᶠ[𝓝 z]
      (fun w => 4 * L.weierstrassP w ^ 3 - L.g₂ * L.weierstrassP w - L.g₃) := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw
    exact L.derivWeierstrassP_sq w hw
  have hleft := (hD.differentiableAt.hasDerivAt.pow 2).deriv
  have hright := (((hP.differentiableAt.hasDerivAt.pow 3).const_mul 4).sub
    (hP.differentiableAt.hasDerivAt.const_mul L.g₂) |>.sub_const L.g₃).deriv
  have h := heq.deriv_eq
  have hleft' : deriv (fun w : ℂ => L.derivWeierstrassP w ^ 2) z =
      2 * L.derivWeierstrassP z * deriv L.derivWeierstrassP z := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one] using! hleft
  simp only [Pi.pow_apply, Pi.sub_apply] at hright
  rw [hleft', hright, L.deriv_weierstrassP] at h
  norm_num at h
  linear_combination h

/-- The actual second differential equation holds also at zeros of WP′, by analytic continuation. -/
lemma wp_second_eq (L : _root_.PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 := by
  have hfinite : ∀ w : ℂ, meromorphicOrderAt L.derivWeierstrassP w ≠ ⊤ := by
    apply (L.meromorphic_derivWeierstrassP.exists_meromorphicOrderAt_ne_top_iff_forall).mp
    refine ⟨0, ?_⟩
    rw [wpderiv_order_zero]
    simp
  have hn := (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (L.meromorphic_derivWeierstrassP z)).mp
    (hfinite z)
  have hQ : ContinuousAt (fun w : ℂ => deriv L.derivWeierstrassP w -
      (6 * L.weierstrassP w ^ 2 - L.g₂ / 2)) z := by
    have hP := L.analyticOnNhd_weierstrassP z hz
    have hD := L.analyticOnNhd_derivWeierstrassP z hz
    exact (hD.deriv.sub ((analyticAt_const.mul (hP.pow 2)).sub analyticAt_const)).continuousAt
  have heq : (fun w : ℂ => deriv L.derivWeierstrassP w -
      (6 * L.weierstrassP w ^ 2 - L.g₂ / 2)) =ᶠ[𝓝[≠] z] (fun _ => (0 : ℂ)) := by
    filter_upwards [hn, nhdsWithin_le_nhds (L.isClosed_lattice.isOpen_compl.mem_nhds hz)] with w hw hwL
    have h := wp_second_times_derivative L hwL
    have hp := (mul_eq_zero.mp h).resolve_left hw
    linear_combination hp / 2
  have ht : Tendsto (fun w : ℂ => deriv L.derivWeierstrassP w -
      (6 * L.weierstrassP w ^ 2 - L.g₂ / 2)) (𝓝[≠] z)
      (𝓝 (deriv L.derivWeierstrassP z - (6 * L.weierstrassP z ^ 2 - L.g₂ / 2))) :=
    hQ.tendsto.mono_left nhdsWithin_le_nhds
  have h0 := tendsto_nhds_unique (ht.congr' heq) (tendsto_const_nhds (x := (0 : ℂ)))
  exact sub_eq_zero.mp h0

/-- The true cubic summed over nonzero torsion gives the actual g₃ constant with its exact count. -/
theorem g3_torsion_sum (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    (4 * ∑ p ∈ nonzeroIndices N hN, xValue N (p.1 : ℕ) (p.2 : ℕ) τ ^ 3 -
      ∑ p ∈ nonzeroIndices N hN, yValue N (p.1 : ℕ) (p.2 : ℕ) τ ^ 2) =
      ((N : ℂ) ^ 2 - 1) * (ThetaWeierstrass.periodPair τ).g₃ := by
  have hx0 : (∑ p ∈ nonzeroIndices N hN,
      (ThetaWeierstrass.periodPair τ).weierstrassP (TorsionDistributionNat.cn τ N p)) = 0 :=
    WeierstrassDistributionNat.weierstrassP_sum_nonzero N hN τ
  have hc : ((nonzeroIndices N hN).card : ℂ) = (N : ℂ) ^ 2 - 1 := by
    rw [card_nonzeroIndices]
    have hn : 1 ≤ N ^ 2 := by nlinarith
    rw [Nat.cast_sub hn]
    push_cast
    ring
  have hs := Finset.sum_congr (s₁ := nonzeroIndices N hN) (s₂ := nonzeroIndices N hN) rfl (fun p hp =>
    (ThetaWeierstrass.periodPair τ).derivWeierstrassP_sq (TorsionDistributionNat.cn τ N p)
      (WeierstrassDistributionNat.cn_notMem N hN τ (Finset.ne_of_mem_erase hp)))
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hx0, mul_zero,
    sub_zero, hc] at hs
  simp only [xValue_eq_wp_cn N hN, yValue_eq_wpderiv_cn N hN]
  linear_combination -hs

/-! ## The ordinary pole-cancelled distribution germ -/

/-- Removing the origin pole gives an ordinary analytic distribution germ. -/
theorem regular_distribution_germ (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    (fun z : ℂ => ∑ p ∈ nonzeroIndices N hN,
      (ThetaWeierstrass.periodPair τ).weierstrassP (z + TorsionDistributionNat.cn τ N p)) =ᶠ[𝓝 (0 : ℂ)]
      (fun z => (N : ℂ) ^ 2 * (ThetaWeierstrass.periodPair τ).weierstrassPExcept 0 ((N : ℂ) * z) -
        (ThetaWeierstrass.periodPair τ).weierstrassPExcept 0 z) := by
  let L := ThetaWeierstrass.periodPair τ
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have ht : Tendsto (fun z : ℂ => (N : ℂ) * z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_, ?_⟩
    · have ht : Tendsto (fun z : ℂ => (N : ℂ) * z) (𝓝 0) (𝓝 0) := by
        simpa only [Pi.mul_apply, id_eq, mul_zero] using!
          (continuous_const.mul continuous_id).tendsto (0 : ℂ)
      exact ht.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact mul_ne_zero hNc hz
  have hzU : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ L.lattice := by
    have hU := L.compl_lattice_sdiff_singleton_mem_nhds (0 : ℂ)
    filter_upwards [nhdsWithin_le_nhds hU, self_mem_nhdsWithin] with z hz hz0
    exact fun h => hz ⟨h, hz0⟩
  have hNzU := ht.eventually hzU
  have hp : ∀ p : Fin N × Fin N, p ≠ p0 N hN →
      ∀ᶠ z in 𝓝[≠] (0 : ℂ), z + TorsionDistributionNat.cn τ N p ∉ L.lattice := by
    intro p hp
    have ht : Tendsto (fun z : ℂ => z + TorsionDistributionNat.cn τ N p) (𝓝 0)
        (𝓝 (TorsionDistributionNat.cn τ N p)) := by
      simpa only [Pi.add_apply, id_eq, zero_add] using!
        (continuous_id.add continuous_const).tendsto (0 : ℂ)
    exact (ht.eventually_mem (L.isClosed_lattice.isOpen_compl.mem_nhds (cn_notMem N hN τ hp))).filter_mono
      nhdsWithin_le_nhds
  have hall : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ p : Fin N × Fin N,
      p ≠ p0 N hN → z + TorsionDistributionNat.cn τ N p ∉ L.lattice :=
    Filter.eventually_all.mpr fun p => by
      by_cases h : p = p0 N hN
      · exact Eventually.of_forall fun z hp => (hp h).elim
      · exact (hp p h).mono fun z hz _ => hz
  have heq : (fun z : ℂ => ∑ p ∈ nonzeroIndices N hN,
      L.weierstrassP (z + TorsionDistributionNat.cn τ N p)) =ᶠ[𝓝[≠] (0 : ℂ)]
      (fun z => (N : ℂ) ^ 2 * L.weierstrassPExcept 0 ((N : ℂ) * z) - L.weierstrassPExcept 0 z) := by
    filter_upwards [hzU, hNzU, hall, self_mem_nhdsWithin] with z hz hNz hall hz0
    have hzall : ∀ p : Fin N × Fin N, z + TorsionDistributionNat.cn τ N p ∉ L.lattice := by
      intro p
      by_cases hp0 : p = p0 N hN
      · rw [hp0, cn_p0, add_zero]
        exact hz
      · exact hall p hp0
    have h := WeierstrassDistributionNat.weierstrassP_sum N hN τ hzall hNz
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (p0 N hN)), cn_p0, add_zero] at h
    have hpz := L.weierstrassPExcept_add (0 : L.lattice) z
    have hpNz := L.weierstrassPExcept_add (0 : L.lattice) ((N : ℂ) * z)
    simp only [Submodule.coe_zero, sub_zero, zero_pow (by decide : 2 ≠ 0), div_zero, sub_zero] at hpz hpNz
    have hpole : (N : ℂ) ^ 2 * (1 / ((N : ℂ) * z) ^ 2) = 1 / z ^ 2 := by field_simp
    change L.weierstrassP z + (∑ p ∈ nonzeroIndices N hN,
      L.weierstrassP (z + TorsionDistributionNat.cn τ N p)) = (N : ℂ) ^ 2 * L.weierstrassP ((N : ℂ) * z) at h
    linear_combination h + hpz - (N : ℂ) ^ 2 * hpNz + hpole
  have hzero : (∑ p ∈ nonzeroIndices N hN,
      L.weierstrassP (0 + TorsionDistributionNat.cn τ N p)) =
      (N : ℂ) ^ 2 * L.weierstrassPExcept 0 ((N : ℂ) * 0) - L.weierstrassPExcept 0 0 := by
    simp only [zero_add, mul_zero, PeriodPair.weierstrassPExcept_zero, mul_zero, sub_zero]
    exact WeierstrassDistributionNat.weierstrassP_sum_nonzero N hN τ
  have hn := eventually_nhdsWithin_iff.mp heq
  filter_upwards [hn] with z hz
  by_cases hz0 : z = 0
  · subst z
    exact hzero
  · exact hz hz0

/-- Ordinary differentiation of the regular distribution gives the actual g₂-normalized second sum. -/
theorem wp_second_torsion_sum (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    (∑ p ∈ nonzeroIndices N hN, deriv (ThetaWeierstrass.periodPair τ).derivWeierstrassP
      (TorsionDistributionNat.cn τ N p)) =
      ((N : ℂ) ^ 4 - 1) * (ThetaWeierstrass.periodPair τ).g₂ / 10 := by
  let L := ThetaWeierstrass.periodPair τ
  have hterms (p : Fin N × Fin N) (hp : p ∈ nonzeroIndices N hN) :
      AnalyticAt ℂ (fun z : ℂ => L.weierstrassP (z + TorsionDistributionNat.cn τ N p)) 0 := by
    have hP : AnalyticAt ℂ L.weierstrassP (0 + TorsionDistributionNat.cn τ N p) := by
      simpa only [zero_add] using L.analyticOnNhd_weierstrassP _
        (WeierstrassDistributionNat.cn_notMem N hN τ (Finset.ne_of_mem_erase hp))
    exact hP.comp (f := fun z : ℂ => z + TorsionDistributionNat.cn τ N p) (x := (0 : ℂ)) (by fun_prop)
  have hB := L.analyticAt_weierstrassPExcept 0
  have hB0 : AnalyticAt ℂ (L.weierstrassPExcept 0) ((N : ℂ) * 0) := by simpa only [mul_zero] using hB
  have hA : AnalyticAt ℂ (fun z : ℂ => (N : ℂ) ^ 2 * L.weierstrassPExcept 0 ((N : ℂ) * z)) 0 :=
    analyticAt_const.mul (hB0.comp (f := fun z : ℂ => (N : ℂ) * z) (x := (0 : ℂ)) (by fun_prop))
  have h := (regular_distribution_germ N hN τ).iteratedDeriv_eq 2
  rw [iteratedDeriv_fun_sum (fun p hp => (hterms p hp).contDiffAt),
    iteratedDeriv_fun_sub hA.contDiffAt hB.contDiffAt, iteratedDeriv_const_mul_field] at h
  have ha := TorsionWeightThree.second_affine (N : ℂ) 0 hB
  simp only [add_zero] at ha
  rw [ha, wp_regular_second_zero] at h
  have hpder (p : Fin N × Fin N) :
      iteratedDeriv 2 (fun z : ℂ => L.weierstrassP (z + TorsionDistributionNat.cn τ N p)) 0 =
      deriv L.derivWeierstrassP (TorsionDistributionNat.cn τ N p) := by
    rw [iteratedDeriv_comp_add_const]
    simp only [zero_add, iteratedDeriv_succ, iteratedDeriv_zero, L.deriv_weierstrassP]
  simp only [hpder] at h
  linear_combination h

/-- The finite square sum gives the actual lattice g₂ invariant with its exact degree factor. -/
theorem g2_torsion_sum (N : ℕ) (hN : 0 < N) (τ : ℍ) :
    (60 : ℂ) * ∑ p ∈ nonzeroIndices N hN, xValue N (p.1 : ℕ) (p.2 : ℕ) τ ^ 2 =
      (((N : ℂ) ^ 2 - 1) * ((N : ℂ) ^ 2 + 6)) * (ThetaWeierstrass.periodPair τ).g₂ := by
  have hs := Finset.sum_congr (s₁ := nonzeroIndices N hN) (s₂ := nonzeroIndices N hN) rfl
    (fun p hp => wp_second_eq (ThetaWeierstrass.periodPair τ)
      (WeierstrassDistributionNat.cn_notMem N hN τ (Finset.ne_of_mem_erase hp)))
  have hc : ((nonzeroIndices N hN).card : ℂ) = (N : ℂ) ^ 2 - 1 := by
    rw [card_nonzeroIndices]
    have hn : 1 ≤ N ^ 2 := by nlinarith
    rw [Nat.cast_sub hn]
    push_cast
    ring
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul, hc,
    wp_second_torsion_sum] at hs
  simp only [xValue_eq_wp_cn N hN]
  linear_combination -(10 : ℂ) * hs

lemma invariant_denominator_two (N : ℕ) (hN : 2 ≤ N) : (N : ℂ) ^ 2 - 1 ≠ 0 := by
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have h : (N : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  exact_mod_cast h

lemma invariant_denominator_four (N : ℕ) (hN : 2 ≤ N) :
    ((N : ℂ) ^ 2 - 1) * ((N : ℂ) ^ 2 + 6) ≠ 0 := by
  have h : (N : ℝ) ^ 2 + 6 ≠ 0 := by positivity
  exact mul_ne_zero (invariant_denominator_two N hN) (by exact_mod_cast h)

/-- The actual g₂ invariant, not a torsion-defined replacement, is a finite torsion polynomial. -/
theorem g2_eq_torsion_polynomial (N : ℕ) (hN : 2 ≤ N) (τ : ℍ) :
    (ThetaWeierstrass.periodPair τ).g₂ =
      (60 * ∑ p ∈ nonzeroIndices N (by omega), xValue N (p.1 : ℕ) (p.2 : ℕ) τ ^ 2) /
        (((N : ℂ) ^ 2 - 1) * ((N : ℂ) ^ 2 + 6)) := by
  apply (eq_div_iff (invariant_denominator_four N hN)).mpr
  have hs := g2_torsion_sum N (by omega) τ
  linear_combination -hs

/-- The actual g₃ invariant follows from the true cubic summed only over nonzero torsion. -/
theorem g3_eq_torsion_polynomial (N : ℕ) (hN : 2 ≤ N) (τ : ℍ) :
    (ThetaWeierstrass.periodPair τ).g₃ =
      (4 * ∑ p ∈ nonzeroIndices N (by omega), xValue N (p.1 : ℕ) (p.2 : ℕ) τ ^ 3 -
        ∑ p ∈ nonzeroIndices N (by omega), yValue N (p.1 : ℕ) (p.2 : ℕ) τ ^ 2) /
        ((N : ℂ) ^ 2 - 1) := by
  apply (eq_div_iff (invariant_denominator_two N hN)).mpr
  have hs := g3_torsion_sum N (by omega) τ
  linear_combination -hs

end ZInQ.Contrib.HeckePrimeRationality.TorsionInvariants
