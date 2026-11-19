import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalInertGood
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.InertBadLemmas
import ZInQKernel.Contrib.HeckeAll.LocalCd

/-!
# GenusOdd: the inert clause of `LocalFactorK` at a prime of bad reduction

Let `𝔭 ∣ p` be unramified with `N𝔭 = p²`, and let `W₀ = C₀ • E` be a rational model of `E` that is
minimal over `ℤ_p` (as in clause 2). If `E` has multiplicative reduction at `p`, or `p ≥ 5`, then
`W₀` is minimal over `𝓞_𝔭` as well:

* multiplicative reduction: `c₄(W₀)` is a `p`-adic unit, hence a `𝔭`-adic unit, and an integral
  model with unit `c₄` is minimal (`HeckeAll.isMinimal_baseChange_of_c₄`);
* `p ≥ 5`: `v_p(Δ) < 12` or `v_p(c₄) < 4` (`not_mem_pow_twelve_and_mem_pow_four`), these
  valuations are the same at `𝔭` (`mem_pow_iff_of_rat`, `e = 1`), and either inequality forces
  minimality (`isMinimal_baseChange_of_notMem`, `HeckeAll.isMinimal_baseChange_of_c₄`).

The two reductions then correspond through `𝔽_p → k_𝔭` (`reduction_map_eq_of_rat_hom`), so the
reduction stays bad and has the same type (multiplicative or additive). A multiplicative reduction
becomes split over `k_𝔭 ≅ 𝔽_{p²}`, since the tangent quadratic splits there
(`splits_map_of_card_sq`). Hence `L_𝔭 = 1 − T` in the multiplicative case and `L_𝔭 = 1` in the
additive case, and `L_𝔭(T²) = L_p(T) L_p(−T)` (`localFactorInert_bad`).

* `MultAt E v`: the minimal model of `E` over `ℚ_v` has multiplicative reduction.
* `LocalFactorInertBadTame`: the inert clause when `E` is bad at `p` and (multiplicative at `p` or
  `p ≥ 5`). PROVED.
* `LocalFactorInertAdditive23`: the inert clause when `E` has additive reduction at `p ∈ {2, 3}`.
  GLUE (there the valuation criterion for minimality is only sufficient).
* `localFactorInertBad_of_additive23`: `LocalFactorInertAdditive23 → LocalFactorInertBad`
  (PROVED), with `localFactorInert_of_additive23`, `artinFactorization_of_additive23`,
  `genusLower34_of_additive23`.
-/

noncomputable section

open NumberField IsDedekindDomain WeierstrassCurve Rat.HeightOneSpectrum IsLocalRing Polynomial

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic

/-- `E` has multiplicative reduction at the place `v` of `ℚ`: the minimal model of `E` over `ℚ_v`
has multiplicative reduction (as `GoodAt`). -/
def MultAt (E : WeierstrassCurve ℚ) (v : HeightOneSpectrum (𝓞 ℚ)) : Prop :=
  ((E.baseChange (v.adicCompletion ℚ)).minimal (v.adicCompletionIntegers ℚ)).HasMultiplicativeReduction
    (v.adicCompletionIntegers ℚ)

section Place

variable {K : Type} [Field K] [NumberField K]

/-- **The inert clause of `LocalFactorK` at a prime of bad reduction, multiplicative or `p ≥ 5`**
(PROVED). -/
theorem localFactorInert_bad (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : 𝔭 ∈ primesAbove K (natGenerator v)) (hN : Ideal.absNorm 𝔭.asIdeal = natGenerator v ^ 2)
    (hu : UnramifiedOver 𝔭 (natGenerator v)) (hbad : ¬ GoodAt E v)
    (hcase : MultAt E v ∨ (natGenerator v ≠ 2 ∧ natGenerator v ≠ 3)) :
    Polynomial.expand ℤ 2 (localPolyK E 𝔭) =
      localPolyQ E v * (localPolyQ E v).comp (Polynomial.C (-1) * Polynomial.X) := by
  have hp := prime_natGenerator v
  have : Fact (natGenerator v).Prime := ⟨hp⟩
  set ιv := algebraMap ℚ (v.adicCompletion ℚ)
  obtain ⟨C₀, hC₀⟩ := exists_isMinimal_map (v.adicCompletionIntegers ℚ) ιv
    (decomp_D1 hp (mem_primesAbove_rat v) (absNorm_rat v) (unramifiedOver_rat v) _)
    (decomp_D2 hp (mem_primesAbove_rat v) (unramifiedOver_rat v) _) E
  have hEΔ : (E.map ιv).Δ ≠ 0 := by rw [map_Δ]; exact (_root_.map_ne_zero ιv).mpr E.isUnit_Δ.ne_zero
  -- reduction types of the rational model over `ℤ_p`
  have h1 : (C₀ • E).map ιv = ((C₀.map ιv) *
      ((E.map ιv).exists_isMinimal (v.adicCompletionIntegers ℚ)).choose⁻¹) •
      (E.map ιv).minimal (v.adicCompletionIntegers ℚ) := by
    rw [ZInQ.Literature.minimal_eq_smul, mul_smul, inv_smul_smul, map_variableChange]
  have hm : (((E.map ιv).minimal (v.adicCompletionIntegers ℚ))).Δ ≠ 0 := by
    rw [ZInQ.Literature.minimal_eq_smul, variableChange_Δ]
    exact mul_ne_zero (pow_ne_zero _ (Units.ne_zero _)) hEΔ
  have : IsMinimal (v.adicCompletionIntegers ℚ) ((C₀.map ιv *
      ((E.map ιv).exists_isMinimal (v.adicCompletionIntegers ℚ)).choose⁻¹) •
      (E.map ιv).minimal (v.adicCompletionIntegers ℚ)) := h1 ▸ hC₀
  have hbad₀ : ¬ ((C₀ • E).map ιv).HasGoodReduction (v.adicCompletionIntegers ℚ) := by
    intro hg
    rw [h1] at hg
    exact hbad ((ZInQ.Manuscript.RC.TwistDictionary.hasGoodReduction_smul_iff _ hm _).mp hg)
  have hmult₀ : MultAt E v →
      ((C₀ • E).map ιv).HasMultiplicativeReduction (v.adicCompletionIntegers ℚ) := by
    intro hM
    have hM' : ((E.map ιv).minimal (v.adicCompletionIntegers ℚ)).HasMultiplicativeReduction
        (v.adicCompletionIntegers ℚ) := hM
    rw [h1]
    exact (ZInQ.Manuscript.RC.TwistDictionary.hasMultiplicativeReduction_smul_iff _ hm _).mpr hM'
  have hΔ0 : ((C₀ • E).map ιv).Δ ≠ 0 := by
    rw [map_Δ]; exact (_root_.map_ne_zero _).mpr (C₀ • E).isUnit_Δ.ne_zero
  have hΔ2 : ((C₀ • E).map (iotaK 𝔭)).Δ ≠ 0 := by
    rw [map_Δ]; exact (_root_.map_ne_zero _).mpr (C₀ • E).isUnit_Δ.ne_zero
  -- `v_p(Δ) < 12` or `v_p(c₄) < 4` for the `ℤ_p`-minimal rational model
  have hkey : (integralModel (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)).Δ ∉
        maximalIdeal (v.adicCompletionIntegers ℚ) ^ 12 ∨
      (integralModel (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)).c₄ ∉
        maximalIdeal (v.adicCompletionIntegers ℚ) ^ 4 := by
    rcases hcase with hM | ⟨hp2, hp3⟩
    · right
      intro hc
      have hmr := hmult₀ hM
      rw [hasMultiplicativeReduction_iff_reduction] at hmr
      apply hmr.2
      have : (integralModel (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)).c₄ ∈
          maximalIdeal (v.adicCompletionIntegers ℚ) := Ideal.pow_le_self (by norm_num) hc
      rw [← residue_eq_zero_iff] at this
      rw [reduction, map_c₄]
      exact this
    · exact not_and_or.mp (not_mem_pow_twelve_and_mem_pow_four hp hp2 hp3 (mem_primesAbove_rat v)
        (unramifiedOver_rat v) _ hΔ0)
  -- integrality and minimality over `𝓞_𝔭`
  have hint : IsIntegral (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭)) :=
    isIntegral_map_of_hint (𝔭.adicCompletionIntegers K) (iotaK 𝔭) ιv
      (hint_rat hp h𝔭 (mem_primesAbove_rat v) _ _) (C₀ • E) inferInstance
  have eΔv : ((integralModel (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)).Δ :
      v.adicCompletion ℚ) = ιv (C₀ • E).Δ := by
    have := integralModel_Δ_eq (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)
    rw [map_Δ] at this; exact this
  have ec4v : ((integralModel (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)).c₄ :
      v.adicCompletion ℚ) = ιv (C₀ • E).c₄ := by
    have := integralModel_c₄_eq (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)
    rw [map_c₄] at this; exact this
  have eΔk : ((integralModel (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))).Δ :
      𝔭.adicCompletion K) = iotaK 𝔭 (C₀ • E).Δ := by
    have := integralModel_Δ_eq (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))
    rw [map_Δ] at this; exact this
  have ec4k : ((integralModel (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))).c₄ :
      𝔭.adicCompletion K) = iotaK 𝔭 (C₀ • E).c₄ := by
    have := integralModel_c₄_eq (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))
    rw [map_c₄] at this; exact this
  have hmin : IsMinimal (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭)) := by
    rw [← baseChange_integralModel_eq (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))]
    rcases hkey with hΔ | hc
    · apply ZInQ.Literature.isMinimal_baseChange_of_notMem
      rwa [← mem_pow_iff_of_rat hp (mem_primesAbove_rat v) (unramifiedOver_rat v) h𝔭 hu ιv
        (iotaK 𝔭) eΔv eΔk]
    · apply ZInQ.Contrib.HeckeAll.isMinimal_baseChange_of_c₄
      intro r hr W' he
      apply hc
      rw [mem_pow_iff_of_rat hp (mem_primesAbove_rat v) (unramifiedOver_rat v) h𝔭 hu ιv
        (iotaK 𝔭) ec4v ec4k, he]
      exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hr 4)
  -- the residue fields and the comparison of reductions
  have hfinv := finite_residueField (𝔭 := v)
  have hfink := finite_residueField (𝔭 := 𝔭)
  have hcv : Nat.card (ResidueField (v.adicCompletionIntegers ℚ)) = natGenerator v := by
    rw [natCard_residueField', absNorm_rat]
  have hck : Nat.card (ResidueField (𝔭.adicCompletionIntegers K)) = natGenerator v ^ 2 := by
    rw [natCard_residueField', hN]
  have := charP_residueField hp (mem_primesAbove_rat v)
  have := charP_residueField hp h𝔭
  let ψ : ResidueField (v.adicCompletionIntegers ℚ) →+* ResidueField (𝔭.adicCompletionIntegers K) :=
    (ZMod.castHom dvd_rfl _).comp
      (ringEquivOfCard hp hcv (by rw [Nat.card_eq_fintype_card, ZMod.card]) :
        ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (natGenerator v)).toRingHom
  have hred := reduction_map_eq_of_rat_hom (p := natGenerator v) ψ ιv (iotaK 𝔭) (C₀ • E)
  have hΔred : (((C₀ • E).map ιv).reduction (v.adicCompletionIntegers ℚ)).Δ = 0 := by
    by_contra h
    exact hbad₀ ((hasGoodReduction_iff_reduction_Δ _).mpr h)
  have hbadk : ¬ ((C₀ • E).map (iotaK 𝔭)).HasGoodReduction (𝔭.adicCompletionIntegers K) := by
    rw [hasGoodReduction_iff_reduction_Δ, hred, map_Δ, hΔred, map_zero, not_not]
  have hmultk : ((C₀ • E).map (iotaK 𝔭)).HasMultiplicativeReduction (𝔭.adicCompletionIntegers K) ↔
      ((C₀ • E).map ιv).HasMultiplicativeReduction (v.adicCompletionIntegers ℚ) := by
    rw [hasMultiplicativeReduction_iff_reduction, hasMultiplicativeReduction_iff_reduction, hred,
      map_Δ, map_c₄, map_eq_zero_iff _ ψ.injective, map_ne_zero_iff _ ψ.injective]
  have hsplitk : ((C₀ • E).map (iotaK 𝔭)).HasSplitMultiplicativeReduction
        (𝔭.adicCompletionIntegers K) ↔
      ((C₀ • E).map ιv).HasMultiplicativeReduction (v.adicCompletionIntegers ℚ) := by
    rw [ZInQ.Manuscript.RC.TwistDictionary.hasSplitMultiplicativeReduction_iff, hmultk,
      and_iff_left_iff_imp]
    intro _
    let _ := Fintype.ofFinite (ResidueField (v.adicCompletionIntegers ℚ))
    let _ := Fintype.ofFinite (ResidueField (𝔭.adicCompletionIntegers K))
    have hL : Fintype.card (ResidueField (𝔭.adicCompletionIntegers K)) =
        Fintype.card (ResidueField (v.adicCompletionIntegers ℚ)) ^ 2 := by
      rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hcv, hck]
    rw [hred, ← ZInQ.Manuscript.RC.TwistDictionary.splitPoly_map]
    refine splits_map_of_card_sq ψ hL ?_
    unfold ZInQ.Manuscript.RC.TwistDictionary.splitPoly
    compute_degree
  -- the local polynomials
  rw [localPolyK_eq, localPolyQ_eq, ← localPolynomial_map_smul (iotaK 𝔭) E C₀,
    ← localPolynomial_map_smul ιv E C₀,
    ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_of_isMinimal _ hΔ0,
    ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_of_isMinimal _ hΔ2,
    ite_eq_right hbad₀, ite_eq_right hbadk]
  by_cases hM : ((C₀ • E).map ιv).HasMultiplicativeReduction (v.adicCompletionIntegers ℚ)
  · rw [ite_eq_left (hsplitk.mpr hM)]
    by_cases hs : ((C₀ • E).map ιv).HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ)
    · rw [ite_eq_left hs]
      simp only [map_sub, map_one, expand_X, sub_comp, one_comp, X_comp, C_neg]
      ring
    · rw [ite_eq_right hs, ite_eq_left hM]
      simp only [map_sub, map_one, expand_X, add_comp, one_comp, X_comp, C_neg]
      ring
  · have hs : ¬ ((C₀ • E).map ιv).HasSplitMultiplicativeReduction (v.adicCompletionIntegers ℚ) :=
      fun h => hM h.toHasMultiplicativeReduction
    rw [ite_eq_right (fun h => hM (hsplitk.mp h)), ite_eq_right (fun h => hM (hmultk.mp h)), ite_eq_right hs,
      ite_eq_right hM]
    simp

end Place

/-- **Node `LocalFactorInertBadTame`** (the inert clause of `LocalFactorK` at a prime of bad
reduction that is multiplicative, or with `p ≥ 5`): for `N𝔭 = p²`, `𝔭² ∤ p`, `E` bad at `p`, and
`E` multiplicative at `p` or `p ∉ {2, 3}`: `L_𝔭(T²) = L_p(T) L_p(−T)`.
PROVED (`localFactorInertBadTame_proof`). -/
def LocalFactorInertBadTame : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)),
    𝔭 ∈ primesAbove K (natGenerator v) →
      Ideal.absNorm 𝔭.asIdeal = natGenerator v ^ 2 → UnramifiedOver 𝔭 (natGenerator v) →
        ¬ GoodAt E v → (MultAt E v ∨ (natGenerator v ≠ 2 ∧ natGenerator v ≠ 3)) →
          Polynomial.expand ℤ 2 (localPolyK E 𝔭) =
            localPolyQ E v * (localPolyQ E v).comp (Polynomial.C (-1) * Polynomial.X)

theorem localFactorInertBadTame_proof : LocalFactorInertBadTame :=
  fun E _ _ _ _ 𝔭 v h𝔭 hN hu hb hc => localFactorInert_bad E 𝔭 v h𝔭 hN hu hb hc

/-- **Node `LocalFactorInertAdditive23`** (GLUE; not needed for `ArtinFactorization`
or (3.4), see `ArtinUnconditional.lean`): the inert
clause of `LocalFactorK` when `E` has additive reduction at `p ∈ {2, 3}`. For `N𝔭 = p²`, `𝔭² ∤ p`
(`K_𝔭/ℚ_p` unramified quadratic), `p = 2` or `p = 3`, and `E` neither good nor multiplicative at
`p`: `L_𝔭(T²) = L_p(T) L_p(−T)`, i.e. the reduction stays additive over `K_𝔭` (both sides are `1`).
-/
def LocalFactorInertAdditive23 : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)),
    𝔭 ∈ primesAbove K (natGenerator v) →
      Ideal.absNorm 𝔭.asIdeal = natGenerator v ^ 2 → UnramifiedOver 𝔭 (natGenerator v) →
        (natGenerator v = 2 ∨ natGenerator v = 3) → ¬ GoodAt E v → ¬ MultAt E v →
          Polynomial.expand ℤ 2 (localPolyK E 𝔭) =
            localPolyQ E v * (localPolyQ E v).comp (Polynomial.C (-1) * Polynomial.X)

/-- **`LocalFactorInertBad` from its additive case at `2` and `3`** (PROVED). -/
theorem localFactorInertBad_of_additive23 (h : LocalFactorInertAdditive23) : LocalFactorInertBad := by
  intro E _ K _ _ 𝔭 v h𝔭 hN hu hb
  by_cases hc : MultAt E v ∨ (natGenerator v ≠ 2 ∧ natGenerator v ≠ 3)
  · exact localFactorInertBadTame_proof E K 𝔭 v h𝔭 hN hu hb hc
  · rw [not_or, not_and_or, not_not, not_not] at hc
    exact h E K 𝔭 v h𝔭 hN hu hc.2 hb hc.1

/-- **`LocalFactorInert` from `LocalFactorInertAdditive23`** (PROVED). -/
theorem localFactorInert_of_additive23 (h : LocalFactorInertAdditive23) : LocalFactorInert :=
  localFactorInert_of_bad (localFactorInertBad_of_additive23 h)

/-- **`ArtinFactorization` from `HasseConvergence`, `ModularNewform` and
`LocalFactorInertAdditive23`** (PROVED reduction). -/
theorem artinFactorization_of_additive23 (hH : HasseConvergence) (hMN : ModularNewform)
    (h : LocalFactorInertAdditive23) : ArtinFactorization :=
  artinFactorization_of_inertBad hH hMN (localFactorInertBad_of_additive23 h)

/-- **(3.4) from the printed leaves, `HasseConvergence`, `ModularNewform` and
`LocalFactorInertAdditive23`** (PROVED reduction). -/
theorem genusLower34_of_additive23 (P : Prints) (hH : HasseConvergence) (hMN : ModularNewform)
    (h : LocalFactorInertAdditive23) : GenusLower34 :=
  genusLower34_of_inertBad P hH hMN (localFactorInertBad_of_additive23 h)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
