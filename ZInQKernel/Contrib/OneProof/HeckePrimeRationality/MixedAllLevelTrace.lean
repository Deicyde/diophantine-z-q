import ZInQKernel.Contrib.OneProof.HeckePrimeRationality.MixedCoprimeTrace

/-!
# Mixed weight-three trace for all divisible levels

For a level `N ≥ 3` let `mixedSpace N` be the span of the mixed forms `x_U λ_V` (all integer
labels) together with the weight-three congruence-class series forms. For every `M > 0` with
`N ∣ M`:

* the actual normalized trace from `Γ(M)` to `Γ(N)` maps `mixedSpace M` into `mixedSpace N`
  (`mixed_trace_all`), hence into the degree-three product span (`mixed_trace_all_degreeThree`);
* a member of `mixedSpace M` invariant under `Γ(N)` is the restriction of a member of
  `mixedSpace N` (`invariant_mixed_descent`).

Proof: for a prime `p` the trace from `pK` to `K` maps `mixedSpace (pK)` into `mixedSpace K`, by
the repeated-prime (`p ∣ K`) and coprime (`p ∤ K`) mixed trace theorems and the class-series trace.
The restriction of the trace preserves `mixedSpace M`, because each quotient summand of a mixed form
or class-series form is again such a form by `SL(2, ℤ)`-covariance of the labels. Invariant descent
then follows by strong induction on the upper level, constructing the lower member before using
injectivity of restriction.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open UpperHalfPlane CongruenceSubgroup Matrix.SpecialLinearGroup
open scoped BigOperators MatrixGroups ModularForm

namespace ZInQ.Contrib.HeckePrimeRationality.MixedAllLevelTrace

open TorsionWeightThree MixedWeightThreeAddition MixedWeightThreeDistribution
open RepeatedPrimeMixedTrace RepeatedPrimeMixedTraceBinder MixedWeightThreeSlope
open AllWeightSeriesTrace (restrictionK normalizedTraceK seriesSpanK)
open DivisionEisensteinLevelMaps (principal_group_le traceIndex)
open ThetaFiveTorsion (act)

set_option quotPrecheck false in
local notation "ΓP" N => (CongruenceSubgroup.Gamma N).map (mapGL ℝ)

/-- The mixed space at level `N`. -/
def mixedSpace (N : ℕ) (hN : 0 < N) : Submodule ℂ (Weight N 3) :=
  lowerMixedSpan N hN ⊔ classSeriesSpan N hN

theorem mixedSpace_le_degreeThree (N : ℕ) (h3 : 3 ≤ N) :
    mixedSpace N (by omega) ≤ degreeThreeProductSpan N (by omega) :=
  sup_le (lowerMixedSpan_le N h3) (classSeriesSpan_le N h3)

theorem crossForm_mem_mixedSpace (N : ℕ) (hN : 0 < N) (u v u' v' : ℤ) :
    crossForm N hN u v u' v' ∈ mixedSpace N hN :=
  Submodule.mem_sup_left (Submodule.subset_span ⟨((u, v), (u', v')), rfl⟩)

/-! ### Level maps at weight three -/

theorem restriction3_injective (N M : ℕ) (hNM : N ∣ M) :
    Function.Injective (restriction3 N M hNM) := by
  rw [restriction3_eq]
  exact AllWeightSeriesTrace.restrictionK_injective N M 3 hNM

theorem restriction3_trans {N K M : ℕ} (hNK : N ∣ K) (hKM : K ∣ M) (g : Weight N 3) :
    restriction3 K M hKM (restriction3 N K hNK g) = restriction3 N M (dvd_trans hNK hKM) g := by
  apply _root_.ModularForm.ext
  intro τ
  rfl

theorem restriction3_self (N : ℕ) (g : Weight N 3) : restriction3 N N (dvd_refl N) g = g := by
  apply _root_.ModularForm.ext
  intro τ
  rfl

/-! ### Prime step -/

theorem prime_trace_mem (p K : ℕ) [Fact p.Prime] (h3 : 3 ≤ K) {f : Weight (p * K) 3}
    (hf : f ∈ mixedSpace (p * K) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega))) :
    normalizedTrace3 K (p * K) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) f ∈
      mixedSpace K (by omega) := by
  have hp := (Fact.out : p.Prime)
  set hM := Nat.mul_pos hp.pos (show 0 < K by omega)
  have hle : mixedSpace (p * K) hM ≤ (mixedSpace K (by omega)).comap (normalizedTrace3 K (p * K) hM) := by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      change normalizedTrace3 K (p * K) hM (crossForm (p * K) hM w.1.1 w.1.2 w.2.1 w.2.2) ∈
        mixedSpace K (by omega)
      by_cases hpK : p ∣ K
      · exact trace_cross_mem_lower p K h3 hpK _ _ _ _
      · have hcop : Nat.Coprime p K := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpK
        exact MixedCoprimeTrace.trace_cross_coprime_lower p K h3 hcop _ _ _ _
    · intro g hg
      exact Submodule.mem_sup_right (trace_classSeries_mem h3 hM (dvd_mul_left K p) hg)
  exact hle hf

/-! ### Restriction of the trace preserves the upper mixed space -/

theorem restriction_trace_cross_mem {N M : ℕ} (hM : 0 < M) (hNM : N ∣ M) (u v u' v' : ℤ) :
    restriction3 N M hNM (normalizedTrace3 N M hM (crossForm M hM u v u' v')) ∈
      lowerMixedSpan M hM := by
  classical
  let : NeZero M := ⟨hM.ne'⟩
  let Q := (ΓP N) ⧸ (ΓP M).subgroupOf (ΓP N)
  let : Fintype Q := Fintype.ofFinite Q
  have hq (q : Q) : ∃ w : (ℤ × ℤ) × (ℤ × ℤ),
      SlashInvariantForm.quotientFunc (crossForm M hM u v u' v') q =
        ⇑(crossForm M hM w.1.1 w.1.2 w.2.1 w.2.2) := by
    induction q using QuotientGroup.induction_on' with
    | H g =>
      obtain ⟨γ, _, he⟩ := Subgroup.mem_map.mp g.property
      refine ⟨(act (u, v) γ⁻¹, act (u', v') γ⁻¹), ?_⟩
      rw [SlashInvariantForm.quotientFunc_mk]
      have hg : g.val⁻¹ = mapGL ℝ (γ⁻¹) := by rw [← he, map_inv]
      rw [hg]
      have h := crossFun_slash hM γ⁻¹ (u, v) (u', v')
      rw [ModularForm.SL_slash] at h
      have h1 : ⇑(crossForm M hM u v u' v') = crossFun M (u, v) (u', v') :=
        coe_crossForm M hM (u, v) (u', v')
      have h2 : ⇑(crossForm M hM (act (u, v) γ⁻¹).1 (act (u, v) γ⁻¹).2 (act (u', v') γ⁻¹).1
          (act (u', v') γ⁻¹).2) = crossFun M (act (u, v) γ⁻¹) (act (u', v') γ⁻¹) :=
        coe_crossForm M hM _ _
      rw [h1, h2]
      exact h
  choose b hb using hq
  have he : restriction3 N M hNM (normalizedTrace3 N M hM (crossForm M hM u v u' v')) =
      ((traceIndex N M : ℂ)⁻¹) • ∑ q : Q, crossForm M hM (b q).1.1 (b q).1.2 (b q).2.1 (b q).2.2 := by
    apply DFunLike.coe_injective
    change ⇑(_root_.ModularForm.restrict (principal_group_le hNM)
      (normalizedTrace3 N M hM (crossForm M hM u v u' v'))) = _
    rw [_root_.ModularForm.coe_restrict, normalizedTrace3_apply, FunLike.coe_smul,
      _root_.ModularForm.coe_trace, FunLike.coe_smul, FunLike.coe_sum]
    apply congrArg (fun F : ℍ → ℂ => (traceIndex N M : ℂ)⁻¹ • F)
    apply Finset.sum_congr rfl
    intro q _
    exact hb q
  rw [he]
  apply Submodule.smul_mem
  apply Submodule.sum_mem
  intro q _
  exact Submodule.subset_span ⟨b q, rfl⟩

theorem restriction_trace_mem_upper {N M : ℕ} (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    {f : Weight M 3} (hf : f ∈ mixedSpace M hM) :
    restriction3 N M hNM (normalizedTrace3 N M hM f) ∈ mixedSpace M hM := by
  have hM3 : 3 ≤ M := h3.trans (Nat.le_of_dvd hM hNM)
  let T := (restriction3 N M hNM).comp (normalizedTrace3 N M hM)
  have hle : mixedSpace M hM ≤ (mixedSpace M hM).comap T := by
    apply sup_le
    · apply Submodule.span_le.mpr
      rintro _ ⟨w, rfl⟩
      exact Submodule.mem_sup_left (restriction_trace_cross_mem hM hNM _ _ _ _)
    · intro g hg
      apply Submodule.mem_sup_right
      change restriction3 N M hNM (normalizedTrace3 N M hM g) ∈ classSeriesSpan M hM
      have hg' : g ∈ seriesSpanK M hM3 3 le_rfl := by
        rw [← classSeriesSpan_eq_seriesSpanK M hM3]; exact hg
      rw [classSeriesSpan_eq_seriesSpanK M hM3, restriction3_eq, normalizedTrace3_eq_traceK]
      exact AllWeightSeriesTrace.restrictionK_trace_mem_upper h3 hM3 le_rfl hNM hg'
  exact hle hf

/-! ### Invariant descent -/

theorem invariant_mixed_prime (p K : ℕ) [Fact p.Prime] (h3 : 3 ≤ K) (f : Weight (p * K) 3)
    (hf : f ∈ mixedSpace (p * K) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)))
    (hinv : ∀ γ ∈ (ΓP K), ⇑f ∣[(3 : ℤ)] γ = ⇑f) :
    ∃ g : Weight K 3, g ∈ mixedSpace K (by omega) ∧
      restriction3 K (p * K) (dvd_mul_left K p) g = f := by
  refine ⟨normalizedTrace3 K (p * K) (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) f,
    prime_trace_mem p K h3 hf, ?_⟩
  rw [restriction3_eq, normalizedTrace3_eq_traceK]
  exact AllWeightSeriesTrace.restrictionK_trace_invariant (by omega)
    (Nat.mul_pos (Fact.out : p.Prime).pos (by omega)) (dvd_mul_left K p) f hinv

/-- **Invariant descent** of the mixed space for all divisible levels. -/
theorem invariant_mixed_descent (M : ℕ) :
    ∀ (N : ℕ) (hN3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M) (f : Weight M 3),
      f ∈ mixedSpace M hM → (∀ γ ∈ (ΓP N), ⇑f ∣[(3 : ℤ)] γ = ⇑f) →
      ∃ g : Weight N 3, g ∈ mixedSpace N (by omega) ∧ restriction3 N M hNM g = f := by
  induction M using Nat.strong_induction_on with
  | h M ih =>
    intro N hN3 hM hNM f hf hinv
    have hN : 0 < N := by omega
    by_cases hEq : N = M
    · subst N
      exact ⟨f, hf, restriction3_self M f⟩
    obtain ⟨t, ht⟩ := hNM
    have ht1 : t ≠ 1 := by
      intro h1
      rw [h1, mul_one] at ht
      exact hEq ht.symm
    obtain ⟨p, hp, hpt⟩ := Nat.exists_prime_and_dvd ht1
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ := hpt
    have hu0 : 0 < u := by
      by_contra hz
      have hz0 : u = 0 := Nat.eq_zero_of_not_pos hz
      rw [hu, hz0, mul_zero, mul_zero] at ht
      exact hM.ne' ht
    set K := N * u with hKdef
    have hK : 0 < K := Nat.mul_pos hN hu0
    have he : M = p * K := by rw [ht, hu, hKdef]; ring
    have hKM : K < M := by rw [he]; have hp2 := hp.two_le; nlinarith
    have hNK : N ∣ K := dvd_mul_right N u
    have hK3 : 3 ≤ K := hN3.trans (Nat.le_of_dvd hK hNK)
    subst he
    have hinvK : ∀ γ ∈ (ΓP K), ⇑f ∣[(3 : ℤ)] γ = ⇑f :=
      fun γ hγ => hinv γ (principal_group_le hNK hγ)
    obtain ⟨gK, hgK, heK⟩ := invariant_mixed_prime p K hK3 f hf hinvK
    have hcoef : (gK : ℍ → ℂ) = (f : ℍ → ℂ) := by
      funext τ
      rw [← heK]
      rfl
    have hinvN : ∀ γ ∈ (ΓP N), ⇑gK ∣[(3 : ℤ)] γ = ⇑gK := by
      intro γ hγ
      rw [hcoef]
      exact hinv γ hγ
    obtain ⟨g, hg, heG⟩ := ih K hKM N hN3 hK hNK gK hgK hinvN
    refine ⟨g, hg, ?_⟩
    rw [← restriction3_trans hNK (dvd_mul_left K p) g, heG, heK]

/-! ### Trace for all divisible levels -/

/-- **Mixed trace for all divisible levels.** -/
theorem mixed_trace_all {N M : ℕ} (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M) {f : Weight M 3}
    (hf : f ∈ mixedSpace M hM) :
    normalizedTrace3 N M hM f ∈ mixedSpace N (by omega) := by
  set T := normalizedTrace3 N M hM f
  have hUpper := restriction_trace_mem_upper h3 hM hNM hf
  have hInv : ∀ γ ∈ (ΓP N), ⇑(restriction3 N M hNM T) ∣[(3 : ℤ)] γ = ⇑(restriction3 N M hNM T) :=
    fun γ hγ => T.slash_action_eq' γ hγ
  obtain ⟨g, hg, he⟩ := invariant_mixed_descent M N h3 hM hNM (restriction3 N M hNM T) hUpper hInv
  have hEq : g = T := restriction3_injective N M hNM he
  rwa [hEq] at hg

theorem mixed_trace_all_degreeThree {N M : ℕ} (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    {f : Weight M 3} (hf : f ∈ mixedSpace M hM) :
    normalizedTrace3 N M hM f ∈ degreeThreeProductSpan N (by omega) :=
  mixedSpace_le_degreeThree N h3 (mixed_trace_all h3 hM hNM hf)

/-- Every integer-labelled mixed form, every divisible level pair. -/
theorem cross_trace_all {N M : ℕ} (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M) (a b c d : ℤ) :
    normalizedTrace3 N M hM (crossForm M hM a b c d) ∈ mixedSpace N (by omega) :=
  mixed_trace_all h3 hM hNM (crossForm_mem_mixedSpace M hM a b c d)

theorem cross_trace_all_degreeThree {N M : ℕ} (h3 : 3 ≤ N) (hM : 0 < M) (hNM : N ∣ M)
    (a b c d : ℤ) :
    normalizedTrace3 N M hM (crossForm M hM a b c d) ∈ degreeThreeProductSpan N (by omega) :=
  mixedSpace_le_degreeThree N h3 (cross_trace_all h3 hM hNM a b c d)

end ZInQ.Contrib.HeckePrimeRationality.MixedAllLevelTrace
