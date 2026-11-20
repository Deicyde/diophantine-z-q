import ZInQKernel.Contrib.CloudB3RC53.Hasse.Final
import ZInQKernel.Contrib.OneProof.RC.Height.ModelInvariance
import ZInQKernel.Contrib.OneProof.HKGZ.HKGZPrints

/-! # Quadratic base change, with the trivial character at conductor one -/

noncomputable section

namespace ZInQ.Manuscript.HKGZ

open ArithmeticFunction IsDedekindDomain NumberField WeierstrassCurve
open ZInQ.Contrib.CloudB3RC53 ZInQ.Contrib.CloudB3RC53.CST
open ZInQ.Contrib.CloudB3RC53.GenusOdd
open scoped BigOperators

theorem trivial_twistedLFunction_eq (E : WeierstrassCurve ℚ)
    (K : Type) [Field K] [NumberField K] :
    twistedLFunction E (fun _ : HeightOneSpectrum (𝓞 K) => 1) =
      ((E.baseChange K).LFunction : ArithmeticFunction ℂ) := by
  classical
  let q (v : HeightOneSpectrum (𝓞 K)) :=
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers K))
  let a (v : HeightOneSpectrum (𝓞 K)) :=
    ((E.baseChange K).baseChange (v.adicCompletion K)).localPowerSeries (v.adicCompletionIntegers K)
  let b (v : HeightOneSpectrum (𝓞 K)) := PowerSeries.map (Int.castRingHom ℂ) (a v)
  let : Northcott q := northcott_natCard_residueField_K
  have ha (v) : (a v).constantCoeff = 1 := by simp [a, WeierstrassCurve.localPowerSeries]
  have hb (v) : (b v).constantCoeff = 1 := by
    change PowerSeries.constantCoeff (PowerSeries.map (Int.castRingHom ℂ) (a v)) = 1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, ha, map_one]
  have hloc (v) : ofPowerSeries (q v) (b v) =
      ((ofPowerSeries (q v) (a v) : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
    ext n
    have hq : 1 < q v := (isPrimePow_natCard_residueField v).one_lt
    rw [intCoe_apply]
    by_cases h : n ∈ Set.range (fun j : ℕ => q v ^ j)
    · obtain ⟨j, rfl⟩ := h
      rw [ofPowerSeries_apply_pow hq, ofPowerSeries_apply_pow hq, PowerSeries.coeff_map]
      rfl
    · rw [ofPowerSeries_apply hq, ofPowerSeries_apply hq,
        Function.extend_apply' _ _ _ h, Function.extend_apply' _ _ _ h]
      simp
  have hprod (T : Finset (HeightOneSpectrum (𝓞 K))) :
      (∏ v ∈ T, ofPowerSeries (q v) (b v)) =
        ((∏ v ∈ T, ofPowerSeries (q v) (a v) : ArithmeticFunction ℤ) : ArithmeticFunction ℂ) := by
    induction T using Finset.induction_on with
    | empty => simp
    | insert v T hv ih => rw [Finset.prod_insert hv, Finset.prod_insert hv, hloc, ih, intCoe_mul]
  simp only [twistedLFunction, PowerSeries.rescale_one, RingHom.id_apply]
  change eulerProduct (fun v => ofPowerSeries (q v) (b v)) =
    ((eulerProduct (fun v => ofPowerSeries (q v) (a v)) : ArithmeticFunction ℤ) :
      ArithmeticFunction ℂ)
  ext n
  rw [intCoe_apply]
  apply (Filter.eventually_const (f := (Filter.atTop : Filter (Finset (HeightOneSpectrum (𝓞 K)))))).mp
  filter_upwards [tendsTo_eulerProduct_ofPowerSeries q a ha n,
    tendsTo_eulerProduct_ofPowerSeries q b hb n] with T h₁ h₂
  rw [← h₁, ← h₂, hprod, intCoe_apply]

theorem chiAt_conductor_one (K : Type) [Field K] [NumberField K] :
    chiAt (conductorOrder K 1) 1 = (fun _ => 1) := by
  funext v
  obtain ⟨p, _, hp, _, _, hmem⟩ := exists_prime_absNorm_eq_pow v
  rw [chiAt_eq_of_not_dvd
    (not_dvd_conductor_of_not_dvd (c := 1) hp hmem (fun h => hp.ne_one (Nat.dvd_one.mp h))) 1]
  simp

/-- The tree's Artin factorization, specialized to conductor one and the trivial class
character, gives the Euler product identity for `E/K` on the convergence half-plane. -/
theorem quadratic_LSeries_factorization (hM : RC.PrintsAnalytic.ModularNewform)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK : SplitHeegnerField E K) (hodd : Odd (discr K))
    (hcop : Nat.Coprime (discr K).natAbs (newformLevel E))
    (s : ℂ) (hs : 3 / 2 < s.re) :
    (E.baseChange K).LSeries s = E.LSeries s * (qtwist E (discr K)).LSeries s := by
  have hχ : IsQuadRingClassChar K 1 1 1 := by
    constructor
    · simp
    · intros
      simp [chiD]
  have h := Hasse.artinFactorization_unconditional hM E K hK.1 hK.2.1 hodd hK.2.2.2.2.2
    1 1 (discr K) (by ring) (by norm_num) (by simp) (one_dvd _)
    (Nat.coprime_one_left _) (by simpa using hcop) 1 hχ s hs
  rw [chiAt_conductor_one, trivial_twistedLFunction_eq, Int.cast_one,
    RC.Height.LSeries_qtwist_one] at h
  exact h

/-- The continuations on the right give a continuation of the base change with nonzero
derivative, by the product rule at the simple zero. -/
theorem exists_baseChange_simple_derivative (hM : RC.PrintsAnalytic.ModularNewform)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (hK : SplitHeegnerField E K) (hodd : Odd (discr K))
    (hcop : Nat.Coprime (discr K).natAbs (newformLevel E))
    (hE : AnalyticRankOne E) (hD : AnalyticRank (qtwist E (discr K)) 0) :
    ∃ F : ℂ → ℂ, Differentiable ℂ F ∧
      (∀ s : ℂ, 3 / 2 < s.re → F s = (E.baseChange K).LSeries s) ∧ deriv F 1 ≠ 0 := by
  obtain ⟨G, hG, hG0, hG'⟩ := analyticRank_one ((analyticRank_one_iff E).mpr hE)
  obtain ⟨J, hJ, hJ0⟩ := analyticRank_zero_iff.mp hD
  refine ⟨fun s => G s * J s, hG.1.mul hJ.1, ?_, ?_⟩
  · intro s hs
    change G s * J s = _
    rw [hG.2 s hs, hJ.2 s hs, quadratic_LSeries_factorization hM E K hK hodd hcop s hs]
  · rw [deriv_fun_mul (hG.1 1) (hJ.1 1), hG0, zero_mul, add_zero]
    exact mul_ne_zero hG' hJ0

end ZInQ.Manuscript.HKGZ
