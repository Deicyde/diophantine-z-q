import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.AllWeightTorsionRectangularScale
import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.TorsionWeierstrassForms

/-!
# Actual rectangular Weierstrass transport and cyclic normalization

The one-dimensional completed-theta multiplication identities are
logarithmically differentiated on ordinary zero-free neighborhoods.
Mathlib's actual Weierstrass function and regular part fix the cyclic
constant by double-pole cancellation; no constant or distribution formula
is assumed in the actual endpoints.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1600000

open Complex Filter Set Function
open scoped Topology Real UpperHalfPlane MatrixGroups

namespace ZInQ.Contrib.HeckePrimeRationality.RectangularWeierstrassAnalytic

open ZInQ.Contrib.HeckePrimeRationality
open CompletedTheta ThetaWeierstrass RectangularThetaLattice

/-- Actual real cyclic translates. -/
def realShift (n : ℕ) (b : Fin n) : ℂ := (b : ℂ) / (n : ℂ)

/-- Actual imaginary cyclic translates. -/
def imagShift (n : ℕ) (τ : ℍ) (a : Fin n) : ℂ := (a : ℂ) * (τ : ℂ) / (n : ℂ)

/-- The actual completed-theta logarithmic derivative. -/
def thetaLog (τ : ℍ) (z : ℂ) : ℂ := deriv (H τ) z / H τ z

lemma thetaLog_analytic (τ : ℍ) {z : ℂ} (hz : H τ z ≠ 0) : AnalyticAt ℂ (thetaLog τ) z :=
  (differentiable_H τ).analyticAt z |>.deriv.div ((differentiable_H τ).analyticAt z) hz

/-- The proved real multiplication identity yields an ordinary zero-free logarithmic germ. -/
theorem real_log_germ (n : ℕ) (hn : 0 < n) (τ : ℍ) {z : ℂ}
    (hs : ∀ b : Fin n, H τ (z + realShift n b) ≠ 0)
    (ht : H (upTau n hn τ) ((n : ℂ)*z) ≠ 0) :
    (fun w : ℂ => ∑ b : Fin n, thetaLog τ (w + realShift n b)) =ᶠ[𝓝 z]
      (fun w => (n : ℂ) * thetaLog (upTau n hn τ) ((n : ℂ)*w)) := by
  have hnear : ∀ b : Fin n, ∀ᶠ w in 𝓝 z, H τ (w + realShift n b) ≠ 0 := fun b =>
    ((differentiable_H τ).continuous.comp (continuous_id.add continuous_const)).continuousAt.eventually_ne (hs b)
  have htnear : ∀ᶠ w in 𝓝 z, H (upTau n hn τ) ((n : ℂ)*w) ≠ 0 :=
    ((differentiable_H _).continuous.comp (continuous_const.mul continuous_id)).continuousAt.eventually_ne ht
  filter_upwards [Filter.eventually_all.mpr hnear, htnear] with w hw htw
  simpa only [thetaLog, realShift, ← CompletedTheta.deriv_H] using!
    ThetaRectangular.real_logDeriv n hn τ w hw htw

/-- Imaginary multiplication gives the actual logarithmic identity with its compensating constant phase. -/
theorem imag_log_value (n : ℕ) (hn : 0 < n) (τ : ℍ) (z : ℂ)
    (hs : ∀ a : Fin n, H τ (z + imagShift n τ a) ≠ 0)
    (ht : H (downTau n hn τ) z ≠ 0) :
    (∑ a : Fin n, thetaLog τ (z + imagShift n τ a)) =
      -(Real.pi : ℂ) * I * ((n-1 : ℕ) : ℂ) + thetaLog (downTau n hn τ) z := by
  obtain ⟨C, hC, hid⟩ := ThetaRectangular.H_imag_multiplication n hn τ
  let q : ℂ := -(Real.pi : ℂ) * I * ((n-1 : ℕ) : ℂ)
  have hl := TorsionDistributionNat.hasDerivAt_prod_logDeriv
    (f := fun a : Fin n => fun w : ℂ => H τ (w + imagShift n τ a))
    (fun a => (hasDerivAt_H τ (z + imagShift n τ a)).comp_add_const z _) hs
  have he : HasDerivAt (fun w : ℂ => cexp (q*w)) (q*cexp (q*z)) z := by
    simpa only [id_eq, one_mul, mul_comm] using! ((hasDerivAt_id z).const_mul q).cexp
  have hr := (he.mul (hasDerivAt_H (downTau n hn τ) z)).const_mul C
  have hfun : (fun w : ℂ => ∏ a : Fin n, H τ (w + imagShift n τ a)) =
      (fun w => C * (cexp (q*w) * H (downTau n hn τ) w)) := by
    funext w
    simpa only [imagShift, q, mul_assoc, neg_mul] using! hid w
  have hr' := hr.congr_of_eventuallyEq (Eventually.of_forall (fun w => congrFun hfun w))
  have h := hl.unique hr'
  rw [congrFun hfun z] at h
  simp only [thetaLog, ← CompletedTheta.deriv_H] at h ⊢
  have hc : C * cexp (q*z) ≠ 0 := mul_ne_zero hC (Complex.exp_ne_zero _)
  have h' : (C * cexp (q*z)) *
      (H (downTau n hn τ) z * (∑ a : Fin n, deriv (H τ) (z+imagShift n τ a) / H τ (z+imagShift n τ a))) =
    (C * cexp (q*z)) * (q * H (downTau n hn τ) z + deriv (H (downTau n hn τ)) z) := by
    linear_combination h
  have hh := mul_left_cancel₀ hc h'
  have hquot : (∑ a : Fin n, deriv (H τ) (z+imagShift n τ a) / H τ (z+imagShift n τ a)) =
      q + deriv (H (downTau n hn τ)) z / H (downTau n hn τ) z := by
    field_simp [ht]
    linear_combination hh
  exact hquot

/-- The imaginary logarithmic identity is established on an ordinary zero-free neighborhood. -/
theorem imag_log_germ (n : ℕ) (hn : 0 < n) (τ : ℍ) {z : ℂ}
    (hs : ∀ a : Fin n, H τ (z + imagShift n τ a) ≠ 0)
    (ht : H (downTau n hn τ) z ≠ 0) :
    (fun w : ℂ => ∑ a : Fin n, thetaLog τ (w + imagShift n τ a)) =ᶠ[𝓝 z]
      (fun w => -(Real.pi : ℂ) * I * ((n-1 : ℕ) : ℂ) + thetaLog (downTau n hn τ) w) := by
  have hnear : ∀ a : Fin n, ∀ᶠ w in 𝓝 z, H τ (w + imagShift n τ a) ≠ 0 := fun a =>
    ((differentiable_H τ).continuous.comp (continuous_id.add continuous_const)).continuousAt.eventually_ne (hs a)
  have htnear : ∀ᶠ w in 𝓝 z, H (downTau n hn τ) w ≠ 0 :=
    (differentiable_H _ z).continuousAt.eventually_ne ht
  filter_upwards [Filter.eventually_all.mpr hnear, htnear] with w hw htw
  exact imag_log_value n hn τ w hw htw

/-- The real rectangular WP identity, with the actual finite-part correction still displayed. -/
theorem wp_real_with_finitePart (n : ℕ) (hn : 0 < n) (τ : ℍ) {z : ℂ}
    (hs : ∀ b : Fin n, z+realShift n b ∉ (periodPair τ).lattice)
    (ht : (n : ℂ)*z ∉ (periodPair (upTau n hn τ)).lattice) :
    (n : ℂ)^2 * (periodPair (upTau n hn τ)).weierstrassP ((n : ℂ)*z) =
      (∑ b : Fin n, (periodPair τ).weierstrassP (z+realShift n b)) +
        (n : ℂ)^2 * finitePart (upTau n hn τ) - (n : ℂ)*finitePart τ := by
  have hhs := fun b => H_ne_zero_of_notMem τ (hs b)
  have hht := H_ne_zero_of_notMem (upTau n hn τ) ht
  have heq := real_log_germ n hn τ hhs hht
  have hL : HasDerivAt (fun w : ℂ => ∑ b : Fin n, thetaLog τ (w+realShift n b))
      (∑ b : Fin n, deriv (thetaLog τ) (z+realShift n b)) z :=
    HasDerivAt.fun_sum fun b _ => ((thetaLog_analytic τ (hhs b)).differentiableAt.hasDerivAt).comp_add_const z _
  have hR := ((thetaLog_analytic _ hht).differentiableAt.hasDerivAt.comp z
    ((hasDerivAt_id z).const_mul (n : ℂ))).const_mul (n : ℂ)
  have h := hL.unique (hR.congr_of_eventuallyEq heq)
  have hw (σ : ℍ) (w : ℂ) (hm : w ∉ (periodPair σ).lattice) :
      (periodPair σ).weierstrassP w = -deriv (thetaLog σ) w + finitePart σ :=
    weierstrassP_eq_neg_deriv_logDerivative σ w hm
  rw [hw _ _ ht]
  simp_rw [hw τ _ (hs _), Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination h

/-- The imaginary rectangular WP identity; the first-derivative phase constant disappears. -/
theorem wp_imag_with_finitePart (n : ℕ) (hn : 0 < n) (τ : ℍ) {z : ℂ}
    (hs : ∀ a : Fin n, z+imagShift n τ a ∉ (periodPair τ).lattice)
    (ht : z ∉ (periodPair (downTau n hn τ)).lattice) :
    (periodPair (downTau n hn τ)).weierstrassP z =
      (∑ a : Fin n, (periodPair τ).weierstrassP (z+imagShift n τ a)) +
        finitePart (downTau n hn τ) - (n : ℂ)*finitePart τ := by
  have hhs := fun a => H_ne_zero_of_notMem τ (hs a)
  have hht := H_ne_zero_of_notMem (downTau n hn τ) ht
  have heq := imag_log_germ n hn τ hhs hht
  have hL : HasDerivAt (fun w : ℂ => ∑ a : Fin n, thetaLog τ (w+imagShift n τ a))
      (∑ a : Fin n, deriv (thetaLog τ) (z+imagShift n τ a)) z :=
    HasDerivAt.fun_sum fun a _ => ((thetaLog_analytic τ (hhs a)).differentiableAt.hasDerivAt).comp_add_const z _
  have hR := (thetaLog_analytic _ hht).differentiableAt.hasDerivAt.const_add
    (-(Real.pi : ℂ)*I*((n-1 : ℕ) : ℂ))
  have h := hL.unique (hR.congr_of_eventuallyEq heq)
  have hw (σ : ℍ) (w : ℂ) (hm : w ∉ (periodPair σ).lattice) :
      (periodPair σ).weierstrassP w = -deriv (thetaLog σ) w + finitePart σ :=
    weierstrassP_eq_neg_deriv_logDerivative σ w hm
  rw [hw _ _ ht]
  simp_rw [hw τ _ (hs _), Finset.sum_add_distrib, Finset.sum_neg_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  linear_combination h

/-- The actual zero index in each positive cyclic grid. -/
def cyclicZero (n : ℕ) (hn : 0 < n) : Fin n := ⟨0,hn⟩

lemma realShift_zero (n : ℕ) (hn : 0 < n) : realShift n (cyclicZero n hn) = 0 := by simp [realShift,cyclicZero]
lemma imagShift_zero (n : ℕ) (hn : 0 < n) (τ : ℍ) : imagShift n τ (cyclicZero n hn) = 0 := by simp [imagShift,cyclicZero]

lemma realShift_notMem (n : ℕ) (hn : 0 < n) (τ : ℍ) {b : Fin n} (hb : b ≠ cyclicZero n hn) :
    realShift n b ∉ (periodPair τ).lattice := by
  have hp : (cyclicZero n hn,b) ≠ WeierstrassDistributionNat.p0 n hn := by
    intro h
    exact hb (congrArg Prod.snd h)
  have h := WeierstrassDistributionNat.cn_notMem n hn τ hp
  simpa only [TorsionDistributionNat.cn, cyclicZero, Nat.cast_zero, zero_mul, zero_add, realShift] using h

lemma imagShift_notMem (n : ℕ) (hn : 0 < n) (τ : ℍ) {a : Fin n} (ha : a ≠ cyclicZero n hn) :
    imagShift n τ a ∉ (periodPair τ).lattice := by
  have hp : (a,cyclicZero n hn) ≠ WeierstrassDistributionNat.p0 n hn := by
    intro h
    exact ha (congrArg Prod.fst h)
  have h := WeierstrassDistributionNat.cn_notMem n hn τ hp
  simpa only [TorsionDistributionNat.cn, cyclicZero, Nat.cast_zero, add_zero, imagShift] using h

/-- Ordinary pole cancellation determines the cyclic constant for an actual WP distribution.
The hypotheses are geometric/calculus data; the actual real/imaginary applications below supply them. -/
lemma cyclic_finitePart (n : ℕ) (hn : 0 < n) (τ σ : ℍ) (q C : ℂ) (hq : q ≠ 0)
    (shift : Fin n → ℂ) (h0 : shift (cyclicZero n hn)=0)
    (hs : ∀ b : Fin n, b ≠ cyclicZero n hn → shift b ∉ (periodPair τ).lattice)
    (hid : ∀ z : ℂ, (∀ b : Fin n,z+shift b ∉ (periodPair τ).lattice) →
      q*z ∉ (periodPair σ).lattice → q^2*(periodPair σ).weierstrassP (q*z) =
        (∑ b : Fin n,(periodPair τ).weierstrassP (z+shift b))+C) :
    (∑ b ∈ Finset.univ.erase (cyclicZero n hn),(periodPair τ).weierstrassP (shift b)) = -C := by
  let P := periodPair τ
  let Q := periodPair σ
  have hzP : ∀ᶠ z in 𝓝[≠] (0 : ℂ), z ∉ P.lattice := by
    filter_upwards [nhdsWithin_le_nhds (P.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin]
      with z hz hzne
    exact fun h => hz ⟨h,hzne⟩
  have htq : Tendsto (fun z : ℂ => q*z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨?_,?_⟩
    · have h : Tendsto (fun z : ℂ => q*z) (𝓝 (0 : ℂ)) (𝓝 (0 : ℂ)) := by
        simpa only [Pi.mul_apply,id_eq,mul_zero] using!
          (continuous_const.mul continuous_id : Continuous (fun z : ℂ => q*z)).tendsto (0 : ℂ)
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      exact mul_ne_zero hq hz
  have hzQ : ∀ᶠ z in 𝓝[≠] (0 : ℂ), q*z ∉ Q.lattice := by
    have hz : ∀ᶠ w in 𝓝[≠] (0 : ℂ), w ∉ Q.lattice := by
      filter_upwards [nhdsWithin_le_nhds (Q.compl_lattice_sdiff_singleton_mem_nhds 0), self_mem_nhdsWithin]
        with w hw hzne
      exact fun h => hw ⟨h,hzne⟩
    exact htq.eventually hz
  have hnear : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ∀ b : Fin n,
      b ≠ cyclicZero n hn → z+shift b ∉ P.lattice := by
    apply Filter.eventually_all.mpr
    intro b
    by_cases hb : b=cyclicZero n hn
    · exact Eventually.of_forall fun z h => (h hb).elim
    · have ht : Tendsto (fun z : ℂ => z+shift b) (𝓝 0) (𝓝 (shift b)) := by
        simpa only [Pi.add_apply,id_eq,zero_add] using! (continuous_id.add continuous_const).tendsto (0 : ℂ)
      exact ((ht.eventually_mem (P.isClosed_lattice.isOpen_compl.mem_nhds (hs b hb))).filter_mono
        nhdsWithin_le_nhds).mono fun z hz _ => hz
  have heq : (fun z : ℂ => ∑ b ∈ Finset.univ.erase (cyclicZero n hn), P.weierstrassP (z+shift b)) =ᶠ[
      𝓝[≠] (0 : ℂ)]
      (fun z => q^2*Q.weierstrassPExcept 0 (q*z)-P.weierstrassPExcept 0 z-C) := by
    filter_upwards [hzP,hzQ,hnear,self_mem_nhdsWithin] with z hzP hzQ hb hzne
    have hall : ∀ b : Fin n,z+shift b ∉ P.lattice := by
      intro b
      by_cases h : b=cyclicZero n hn
      · rw [h,h0,add_zero]; exact hzP
      · exact hb b h
    have h := hid z hall hzQ
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ (cyclicZero n hn)),h0,add_zero] at h
    have hp := weierstrassP_eq_principal_part τ z
    have ht := weierstrassP_eq_principal_part σ (q*z)
    have pole : q^2*(1/(q*z)^2)=1/z^2 := by field_simp
    linear_combination -h - hp + q^2*ht + pole
  have hleft : Tendsto (fun z : ℂ => ∑ b ∈ Finset.univ.erase (cyclicZero n hn),P.weierstrassP (z+shift b))
      (𝓝[≠] (0 : ℂ)) (𝓝 (∑ b ∈ Finset.univ.erase (cyclicZero n hn),P.weierstrassP (shift b))) := by
    apply tendsto_finsetSum
    intro b hb
    have hd := P.analyticOnNhd_weierstrassP (shift b) (hs b (Finset.ne_of_mem_erase hb))
    have ht : Tendsto (fun z : ℂ => z+shift b) (𝓝 0) (𝓝 (shift b)) := by
      simpa only [Pi.add_apply,id_eq,zero_add] using! (continuous_id.add continuous_const).tendsto (0 : ℂ)
    exact (hd.continuousAt.tendsto.comp ht).mono_left nhdsWithin_le_nhds
  have hright : Tendsto (fun z : ℂ => q^2*Q.weierstrassPExcept 0 (q*z)-P.weierstrassPExcept 0 z-C)
      (𝓝[≠] (0 : ℂ)) (𝓝 (-C)) := by
    have hP : Tendsto (P.weierstrassPExcept 0) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      simpa only [PeriodPair.weierstrassPExcept_zero] using!
        (P.analyticAt_weierstrassPExcept 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    have hQ : Tendsto (Q.weierstrassPExcept 0) (𝓝[≠] (0 : ℂ)) (𝓝 0) := by
      simpa only [PeriodPair.weierstrassPExcept_zero] using!
        (Q.analyticAt_weierstrassPExcept 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa only [mul_zero,sub_zero,zero_sub] using! ((hQ.comp htq).const_mul (q^2)).sub hP |>.sub_const C
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

/-- Actual real cyclic finite-part normalization, proved by ordinary double-pole cancellation. -/
theorem real_cyclic_finitePart (n : ℕ) (hn : 0 < n) (τ : ℍ) :
    (∑ b ∈ Finset.univ.erase (cyclicZero n hn),(periodPair τ).weierstrassP (realShift n b)) =
      (n : ℂ)*finitePart τ - (n : ℂ)^2*finitePart (upTau n hn τ) := by
  have h := cyclic_finitePart n hn τ (upTau n hn τ) (n : ℂ)
    ((n : ℂ)^2*finitePart (upTau n hn τ)-(n : ℂ)*finitePart τ)
    (Nat.cast_ne_zero.mpr hn.ne') (realShift n) (realShift_zero n hn)
    (fun b hb => realShift_notMem n hn τ hb)
    (fun z hs ht => by linear_combination wp_real_with_finitePart n hn τ hs ht)
  linear_combination h

/-- Actual imaginary cyclic normalization; no pole value is assigned to the bad origin. -/
theorem imag_cyclic_finitePart (n : ℕ) (hn : 0 < n) (τ : ℍ) :
    (∑ a ∈ Finset.univ.erase (cyclicZero n hn),(periodPair τ).weierstrassP (imagShift n τ a)) =
      (n : ℂ)*finitePart τ - finitePart (downTau n hn τ) := by
  have h := cyclic_finitePart n hn τ (downTau n hn τ) 1
    (finitePart (downTau n hn τ)-(n : ℂ)*finitePart τ)
    one_ne_zero (imagShift n τ) (imagShift_zero n hn τ)
    (fun a ha => imagShift_notMem n hn τ ha)
    (fun z hs ht => by
      have hz : z ∉ (periodPair (downTau n hn τ)).lattice := by simpa only [one_mul] using ht
      have hw := wp_imag_with_finitePart n hn τ hs hz
      simp only [one_mul,one_pow]
      linear_combination hw)
  linear_combination h

end ZInQ.Contrib.HeckePrimeRationality.RectangularWeierstrassAnalytic
