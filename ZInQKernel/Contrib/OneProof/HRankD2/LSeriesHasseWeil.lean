import ZInQKernel.Contrib.OneProof.MillerRankMinimal
import ZInQKernel.Contrib.OneProof.RankModelTangent
import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# Mathlib's L-series is the Hasse–Weil L-series on global minimal equations

Let `E₀ : y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` be a Weierstrass equation with integer
coefficients and nonzero discriminant, which is a global minimal equation over `ℚ`
(`IsGlobalMinimalQ`: integral, and minimal at every prime). The Hasse–Weil L-series of
the curve is the Euler product of Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed.
(GTM 106, Springer, 2009), App. C, §16:

  `L(E/ℚ, s) = ∏_p L_p(p^{-s})^{-1}`, with
  * `L_p(T) = 1 - a_p T + p T²`, `a_p = p + 1 - #Ẽ(𝔽_p)`, if `p ∤ Δ` (good reduction);
  * `L_p(T) = 1 - T` if `p ∣ Δ`, `p ∤ c₄` and the reduction is split multiplicative;
  * `L_p(T) = 1 + T` if `p ∣ Δ`, `p ∤ c₄` and the reduction is nonsplit multiplicative;
  * `L_p(T) = 1` if `p ∣ Δ` and `p ∣ c₄` (additive reduction).

The reduction types are read off the minimal equation as in Silverman, AEC, Prop. VII.5.1.
Here `Ẽ` is the reduction `E₀ mod p` (`hwReduction`), and `#Ẽ(𝔽_p)` counts the point at
infinity. Split means that the tangent polynomial of `Ẽ` at its node splits over `𝔽_p`;
`HRankD2/NodeSlopes.lean` shows that this is Silverman's condition that the slopes of the
tangent lines at the node lie in `𝔽_p`.

`hwEulerPoly E₀ p` is `L_p(T)`, `hwCoeff E₀ n` is the coefficient of `n^{-s}` in the expanded
product, and the main theorem `LSeries_eq_hasseWeil` says that Mathlib's
`WeierstrassCurve.LSeries` of `E₀` over `ℚ` is the Dirichlet series of `hwCoeff E₀`, for
every `s`. The Euler product itself is in `HRankD2/EulerProduct.lean`.

Mathlib defines the local factor at `p` on a minimal model over `ℤ_p` chosen by
`Classical.choice`. This file shows that it agrees with the factor read off `E₀`. At good
primes this is the point count of the reduction; at bad primes it needs the reduction type
(multiplicative or additive, from `p ∣ c₄`) and the splitting test, which are invariant
between two minimal models.
-/

set_option autoImplicit false

namespace ZInQ.Manuscript.RankModel

open Polynomial WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open ZInQ.Literature Rat.HeightOneSpectrum

/-! ## The Hasse–Weil side -/

/-- The reduction `E₀ mod n` of an integral Weierstrass equation. -/
noncomputable def hwReduction (E₀ : WeierstrassCurve ℤ) (n : ℕ) : WeierstrassCurve (ZMod n) :=
  E₀.map (Int.castRingHom (ZMod n))

open Classical in
/-- The Hasse–Weil local polynomial `L_p(T)` of an integral equation at `p`
(Silverman, AEC, App. C, §16): `1 - a_p T + p T²` with `a_p = p + 1 - #Ẽ(𝔽_p)` if `p ∤ Δ`;
`1 - T` (split) or `1 + T` (nonsplit) if `p ∣ Δ` and `p ∤ c₄`; and `1` if `p ∣ Δ` and
`p ∣ c₄`. -/
noncomputable def hwEulerPoly (E₀ : WeierstrassCurve ℤ) (p : ℕ) : ℤ[X] :=
  if ¬ (p : ℤ) ∣ E₀.Δ then
    1 - C ((p : ℤ) + 1 - Nat.card (hwReduction E₀ p).toAffine.Point) * X + C (p : ℤ) * X ^ 2
  else if ¬ (p : ℤ) ∣ E₀.c₄ then
    (if (tangentPolynomial (hwReduction E₀ p)).Splits then 1 - X else 1 + X)
  else 1

/-- The Dirichlet coefficients of the Hasse–Weil L-series: the coefficient at `n ≠ 0` is
`∏_{p^k ∥ n} [T^k] (1 / L_p(T))`, the coefficient of `n^{-s}` in `∏_p L_p(p^{-s})^{-1}`. -/
noncomputable def hwCoeff (E₀ : WeierstrassCurve ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 0 else n.factorization.prod fun p k =>
    PowerSeries.coeff k (PowerSeries.invOfUnit (hwEulerPoly E₀ p : PowerSeries ℤ) 1)

theorem hwEulerPoly_coeff_zero (E₀ : WeierstrassCurve ℤ) (p : ℕ) :
    (hwEulerPoly E₀ p).coeff 0 = 1 := by
  unfold hwEulerPoly; split_ifs <;> simp

/-! ## Local comparison at a finite place -/

section Local

/-- The tangent polynomial commutes with a ring map. -/
theorem map_tangentPolynomial' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (W : WeierstrassCurve R) :
    (tangentPolynomial W).map f = tangentPolynomial (W.map f) := by
  simp [tangentPolynomial, map_ofNat]

/-- The splitting test is unchanged by a ring isomorphism. -/
theorem splits_tangentPolynomial_map_ringEquiv {F F' : Type*} [Field F] [Field F']
    (W : WeierstrassCurve F) (e : F ≃+* F') :
    (tangentPolynomial (W.map (e : F →+* F'))).Splits ↔ (tangentPolynomial W).Splits := by
  rw [← map_tangentPolynomial']
  refine ⟨fun h => ?_, fun h => h.map _⟩
  have := h.map (e.symm : F' →+* F)
  rwa [Polynomial.map_map, RingEquiv.symm_comp, Polynomial.map_id] at this

variable {R K : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- On two minimal equations related by a change of coordinates, the reduction data used by
the local polynomial agree (the same argument as in `RankModelInvariant`). -/
theorem localData_of_minimal_change' (W : WeierstrassCurve K) (U : VariableChange K)
    [IsMinimal R W] [IsMinimal R (U • W)] (hΔ : W.Δ ≠ 0) :
    (HasGoodReduction R (U • W) ↔ HasGoodReduction R W) ∧
    (HasSplitMultiplicativeReduction R (U • W) ↔ HasSplitMultiplicativeReduction R W) ∧
    (HasMultiplicativeReduction R (U • W) ↔ HasMultiplicativeReduction R W) := by
  have hu := ZInQ.Literature.vK_u_eq_one (R := R) hΔ U
  let v := valuation K (IsDiscreteValuationRing.maximalIdeal R)
  have hd : v (U • W).Δ = v W.Δ := by
    dsimp only [v]
    rw [variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
      hu, inv_one, one_pow, one_mul]
  have hc : v (U • W).c₄ = v W.c₄ := by
    dsimp only [v]
    rw [variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
      hu, inv_one, one_pow, one_mul]
  have hg : HasGoodReduction R (U • W) ↔ HasGoodReduction R W := by
    rw [hasGoodReduction_iff, hasGoodReduction_iff]
    simp only [and_iff_right (show IsMinimal R (U • W) from inferInstance),
      and_iff_right (show IsMinimal R W from inferInstance)]
    exact congrArg (· = 1) hd |>.to_iff
  have hm : HasMultiplicativeReduction R (U • W) ↔ HasMultiplicativeReduction R W := by
    rw [hasMultiplicativeReduction_iff, hasMultiplicativeReduction_iff]
    simp only [and_iff_right (show IsMinimal R (U • W) from inferInstance),
      and_iff_right (show IsMinimal R W from inferInstance)]
    change (v (U • W).Δ < 1 ∧ v (U • W).c₄ = 1) ↔ (v W.Δ < 1 ∧ v W.c₄ = 1)
    rw [hd, hc]
  have hred := ZInQ.Literature.exists_reduction_variableChange W U hu
  refine ⟨hg, ?_, hm⟩
  rw [hasSplitMultiplicativeReduction_iff_residue, hasSplitMultiplicativeReduction_iff_residue,
    hm, residueSplit_iff_of_variableChange hred]

open Classical in
/-- The local polynomial at a place of multiplicative reduction of a minimal model `W` is
`1 - T` or `1 + T`, according to the splitting test on the reduction of `W` itself. -/
theorem localPolynomial_of_hasMultiplicativeReduction (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    [h : HasMultiplicativeReduction R W] : W.localPolynomial R =
      if (tangentPolynomial (W.reduction R)).Splits then 1 - X else 1 + X := by
  have : IsMinimal R ((W.exists_isMinimal R).choose • W) := (W.exists_isMinimal R).choose_spec
  obtain ⟨hg, hs, hm⟩ := localData_of_minimal_change' (R := R) W (W.exists_isMinimal R).choose hΔ
  have hng : ¬ (W.minimal R).HasGoodReduction R := fun h' =>
    h.badReduction.ne (hg.mp h').goodReduction
  have hmm : (W.minimal R).HasMultiplicativeReduction R := hm.mpr h
  have hsp : (W.minimal R).HasSplitMultiplicativeReduction R ↔
      (tangentPolynomial (W.reduction R)).Splits := by
    change HasSplitMultiplicativeReduction R ((W.exists_isMinimal R).choose • W) ↔ _
    rw [hs, hasSplitMultiplicativeReduction_iff_residue]
    exact and_iff_right h
  unfold localPolynomial
  simp only [hng, hmm, hsp, ↓reduceIte]

end Local

section Completion

variable (E₀ : WeierstrassCurve ℤ) (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- Base change of `E₀` to the completion `ℚ_v`, via `ℚ` or via `ℤ_v`. -/
theorem baseChange_baseChange_eq :
    (E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ) =
      (E₀.baseChange (v.adicCompletionIntegers ℚ)).baseChange (v.adicCompletion ℚ) := by
  simp only [baseChange, WeierstrassCurve.map_map]
  exact congrArg E₀.map (RingHom.ext_int _ _)

theorem baseChange_completion_Δ :
    ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).Δ =
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
        ((E₀.Δ : ℤ) : v.adicCompletionIntegers ℚ) := by
  rw [baseChange_baseChange_eq, baseChange, map_Δ, baseChange, map_Δ, algebraMap_int_eq,
    eq_intCast]

theorem baseChange_completion_c₄ :
    ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).c₄ =
      algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
        ((E₀.c₄ : ℤ) : v.adicCompletionIntegers ℚ) := by
  rw [baseChange_baseChange_eq, baseChange, map_c₄, baseChange, map_c₄, algebraMap_int_eq,
    eq_intCast]

theorem baseChange_completion_Δ_ne_zero (hΔ : E₀.Δ ≠ 0) :
    ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).Δ ≠ 0 := by
  rw [baseChange, map_Δ, baseChange, map_Δ]
  refine (_root_.map_ne_zero _).mpr ?_
  rw [algebraMap_int_eq, eq_intCast]
  exact_mod_cast hΔ

theorem valuation_intCast_lt_one_iff (n : ℤ) :
    valuation (v.adicCompletion ℚ) (IsDiscreteValuationRing.maximalIdeal
      (v.adicCompletionIntegers ℚ)) (algebraMap (v.adicCompletionIntegers ℚ)
        (v.adicCompletion ℚ) (n : v.adicCompletionIntegers ℚ)) < 1 ↔
      (natGenerator v : ℤ) ∣ n := by
  rw [valuation_of_algebraMap, intValuation_lt_one_iff_mem]
  have := intCast_mem_maximalIdeal_pow_iff v n 1
  simp only [pow_one] at this
  exact this

theorem valuation_intCast_eq_one_iff (n : ℤ) :
    valuation (v.adicCompletion ℚ) (IsDiscreteValuationRing.maximalIdeal
      (v.adicCompletionIntegers ℚ)) (algebraMap (v.adicCompletionIntegers ℚ)
        (v.adicCompletion ℚ) (n : v.adicCompletionIntegers ℚ)) = 1 ↔
      ¬ (natGenerator v : ℤ) ∣ n := by
  rw [valuation_of_algebraMap, intValuation_eq_one_iff]
  have := intCast_mem_maximalIdeal_pow_iff v n 1
  simp only [pow_one] at this
  exact not_congr this

variable [hmin : IsMinimal (v.adicCompletionIntegers ℚ)
  ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ))]

theorem integralModel_completion_eq :
    integralModel (v.adicCompletionIntegers ℚ)
      ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)) =
        E₀.baseChange (v.adicCompletionIntegers ℚ) := by
  apply WeierstrassCurve.map_injective (IsFractionRing.injective _ (v.adicCompletion ℚ))
  change (integralModel _ ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ))).baseChange
    (v.adicCompletion ℚ) = (E₀.baseChange (v.adicCompletionIntegers ℚ)).baseChange _
  rw [baseChange_integralModel_eq, baseChange_baseChange_eq]

/-- The reduction of the completed equation, read in `ZMod p`, is `E₀ mod p`. -/
theorem reduction_completion_map :
    (((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).reduction
        (v.adicCompletionIntegers ℚ)).map (residueEquiv v : _ →+* ZMod (natGenerator v)) =
      hwReduction E₀ (natGenerator v) := by
  rw [reduction, integralModel_completion_eq, baseChange, WeierstrassCurve.map_map,
    WeierstrassCurve.map_map, hwReduction]
  exact congrArg E₀.map (RingHom.ext_int _ _)

end Completion

/-- **The local comparison.** At every finite place `v`, with `p = natGenerator v`, Mathlib's
local polynomial of a global minimal equation `E₀` is the Hasse–Weil polynomial `L_p(T)`. -/
theorem localPolynomial_eq_hwEulerPoly (E₀ : WeierstrassCurve ℤ) (hΔ : E₀.Δ ≠ 0)
    (hmin : IsGlobalMinimalQ (E₀.baseChange ℚ))
    (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).localPolynomial
      (v.adicCompletionIntegers ℚ) = hwEulerPoly E₀ (natGenerator v) := by
  have hm : IsMinimal (v.adicCompletionIntegers ℚ)
      ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)) := hmin.2 v
  have hΔv := baseChange_completion_Δ_ne_zero E₀ v hΔ
  unfold hwEulerPoly
  by_cases hgood : (natGenerator v : ℤ) ∣ E₀.Δ
  · simp only [hgood, not_true_eq_false, ↓reduceIte]
    have hlt : valuation (v.adicCompletion ℚ) (IsDiscreteValuationRing.maximalIdeal
        (v.adicCompletionIntegers ℚ)) ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)).Δ
          < 1 := by
      rw [baseChange_completion_Δ]; exact (valuation_intCast_lt_one_iff v _).mpr hgood
    by_cases hc : (natGenerator v : ℤ) ∣ E₀.c₄
    · simp only [hc, not_true_eq_false, ↓reduceIte]
      have : HasAdditiveReduction (v.adicCompletionIntegers ℚ)
          ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)) := by
        refine (hasAdditiveReduction_iff _ _).mpr ⟨hm, hlt, ?_⟩
        rw [baseChange_completion_c₄]; exact (valuation_intCast_lt_one_iff v _).mpr hc
      exact localPolynomial_of_hasAdditiveReduction _ hΔv
    · simp only [hc, not_false_eq_true, ↓reduceIte]
      have : HasMultiplicativeReduction (v.adicCompletionIntegers ℚ)
          ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)) := by
        refine (hasMultiplicativeReduction_iff _ _).mpr ⟨hm, hlt, ?_⟩
        rw [baseChange_completion_c₄]; exact (valuation_intCast_eq_one_iff v _).mpr hc
      rw [localPolynomial_of_hasMultiplicativeReduction _ hΔv, ← reduction_completion_map,
        splits_tangentPolynomial_map_ringEquiv]
  · simp only [hgood, not_false_eq_true, ↓reduceIte]
    have : HasGoodReduction (v.adicCompletionIntegers ℚ)
        ((E₀.baseChange ℚ).baseChange (v.adicCompletion ℚ)) := by
      refine (hasGoodReduction_iff _ _).mpr ⟨hm, ?_⟩
      rw [baseChange_completion_Δ]; exact (valuation_intCast_eq_one_iff v _).mpr hgood
    have hE := (hasGoodReduction_iff_isElliptic_reduction _).mp this
    rw [localPolynomial_of_hasGoodReduction, natCard_residueField,
      ← natCard_point_map_ringEquiv _ (residueEquiv v), reduction_completion_map]

/-! ## The global comparison -/

open ArithmeticFunction

/-- The coefficient of Mathlib's L-function at a prime power, for any equation whose local
polynomials are given by a family `P` of polynomials indexed by the rational primes. This is
the argument of `LFunction_cd_apply_prime_pow`, with the local family as a parameter. -/
theorem LFunction_apply_prime_pow_of_localPolynomial (W : WeierstrassCurve ℚ) (P : ℕ → ℤ[X])
    (hP : ∀ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
      (W.baseChange (v.adicCompletion ℚ)).localPolynomial (v.adicCompletionIntegers ℚ) =
        P (natGenerator v))
    (p : ℕ) [hp' : Fact p.Prime] (k : ℕ) :
    W.LFunction (p ^ k) = PowerSeries.coeff k (PowerSeries.invOfUnit (P p : PowerSeries ℤ) 1) := by
  classical
  have hp := hp'.out
  obtain ⟨v, rfl⟩ := exists_natGenerator_eq p
  set q := fun w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)) with hq_def
  set F := fun w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    (W.baseChange (w.adicCompletion ℚ)).localPowerSeries (w.adicCompletionIntegers ℚ) with hF_def
  have hF : ∀ w, PowerSeries.constantCoeff (F w) = 1 := fun w => by
    simp [F, localPowerSeries, PowerSeries.constantCoeff_invOfUnit]
  have hf1 : ∀ w, ofPowerSeries (q w) (F w) 1 = 1 := fun w => by
    rw [ofPowerSeries_apply_one, hF]
  have hvan : ∀ w, w ≠ v → ∀ m, m ∣ natGenerator v ^ k → m ≠ 1 →
      ofPowerSeries (q w) (F w) m = 0 := by
    intro w hw m hm hm1
    obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).mp hm
    have hqw : q w = natGenerator w := natCard_residueField w
    rw [hqw, ofPowerSeries_apply (prime_natGenerator w).one_lt, Function.extend_apply']
    · rfl
    rintro ⟨l, hl⟩
    rcases j with _ | j
    · exact hm1 (pow_zero _)
    rcases l with _ | l
    · exact (Nat.one_lt_pow (Nat.succ_ne_zero j) hp.one_lt).ne (by simpa using hl)
    · have hdvd : natGenerator w ∣ natGenerator v ^ (j + 1) :=
        hl ▸ dvd_pow_self _ (Nat.succ_ne_zero l)
      exact hw (natGenerator_injective ((Nat.prime_dvd_prime_iff_eq (prime_natGenerator w) hp).mp
        ((prime_natGenerator w).dvd_of_dvd_pow hdvd)))
  obtain ⟨s0, hs0⟩ := Filter.eventually_atTop.mp
    (tendsTo_eulerProduct_ofPowerSeries q F hF (natGenerator v ^ k))
  have key := hs0 (insert v s0) (Finset.subset_insert _ _)
  change eulerProduct (fun w => ofPowerSeries (q w) (F w)) (natGenerator v ^ k) = _
  have hrest := prod_vanish (fun w => ofPowerSeries (q w) (F w)) (natGenerator v ^ k)
    ((insert v s0).erase v) fun w hw => ⟨hf1 w, hvan w (Finset.ne_of_mem_erase hw)⟩
  rw [← key, ← Finset.mul_prod_erase _ _ (Finset.mem_insert_self v s0), mul_comm,
    mul_apply_of_vanish hrest.1 hrest.2]
  have hq : q v = natGenerator v := natCard_residueField v
  rw [hq, ofPowerSeries_apply_pow hp.one_lt]
  simp only [F, localPowerSeries]
  rw [hP v]

/-- Every coefficient of Mathlib's L-function of a global minimal equation is the
corresponding Hasse–Weil coefficient. -/
theorem LFunction_apply_eq_hwCoeff (E₀ : WeierstrassCurve ℤ) (hΔ : E₀.Δ ≠ 0)
    (hmin : IsGlobalMinimalQ (E₀.baseChange ℚ)) (n : ℕ) :
    (E₀.baseChange ℚ).LFunction n = hwCoeff E₀ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [hwCoeff]
  simp only [hwCoeff, hn, ↓reduceIte]
  rw [(isMultiplicative_LFunction _).multiplicative_factorization _ hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)⟩
  exact LFunction_apply_prime_pow_of_localPolynomial _ (hwEulerPoly E₀)
    (localPolynomial_eq_hwEulerPoly E₀ hΔ hmin) p _

/-- **Mathlib's L-series is the Hasse–Weil L-series (D2).** For a Weierstrass equation `E₀`
with integer coefficients and `Δ ≠ 0` that is a global minimal equation over `ℚ`, Mathlib's
`WeierstrassCurve.LSeries` of `E₀` over `ℚ` is, at every `s`, the Dirichlet series of the
Hasse–Weil coefficients `hwCoeff E₀`, the expansion of `∏_p L_p(p^{-s})^{-1}` with the
local factors of Silverman, AEC, App. C, §16 (`hwEulerPoly`). -/
theorem LSeries_eq_hasseWeil (E₀ : WeierstrassCurve ℤ) (hΔ : E₀.Δ ≠ 0)
    (hmin : IsGlobalMinimalQ (E₀.baseChange ℚ)) (s : ℂ) :
    (E₀.baseChange ℚ).LSeries s = LSeries (fun n => (hwCoeff E₀ n : ℂ)) s := by
  refine LSeries_congr (fun {n} _ => ?_) s
  simp only [Function.comp_apply, LFunction_apply_eq_hwCoeff E₀ hΔ hmin n]

/-- The same for an elliptic curve over `ℚ` given by a global minimal equation, which is the
convention of Miller, LMS J. Comput. Math. 14 (2011), §1, p. 327: its integral model `E₀`
has `E₀.baseChange ℚ = E`, and `L(E, s)` is the Hasse–Weil series of `E₀`. -/
theorem LSeries_eq_hasseWeil_of_isGlobalMinimalQ (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmin : IsGlobalMinimalQ E) : ∃ E₀ : WeierstrassCurve ℤ, E₀.baseChange ℚ = E ∧
      ∀ s : ℂ, E.LSeries s = LSeries (fun n => (hwCoeff E₀ n : ℂ)) s := by
  obtain ⟨E₀, rfl⟩ := hmin.1.integral
  refine ⟨E₀, rfl, LSeries_eq_hasseWeil E₀ ?_ hmin⟩
  intro h0
  have h := (E₀.baseChange ℚ).isUnit_Δ.ne_zero
  rw [baseChange, map_Δ, h0] at h
  exact h (_root_.map_zero _)

end ZInQ.Manuscript.RankModel
