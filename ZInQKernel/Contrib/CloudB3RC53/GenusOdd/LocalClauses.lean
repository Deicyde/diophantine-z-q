import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalBridge
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalRational
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.RationalModel
import ZInQKernel.Contrib.CloudB3RC53.GenusOdd.LocalConsistency

/-!
# GenusOdd: clauses 1 and 2 of `LocalFactorK` (PROVED)

Both clauses compare Mathlib's local polynomial of `E` over `ℚ_v` and over `K_𝔭` (`N𝔭 = p`) through
one Weierstrass equation `W₀ = C₀ • E` with RATIONAL coefficients that is minimal over both
completions; its two reductions are then the same curve over `𝔽_p`
(`reduction_map_eq_of_rat`), so the local polynomials agree
(`localPolynomial_eq_of_reduction_map`).

* Clause 2 (`localFactorK_clause_good`, `E` good at `p`, any ramification): `ℚ_v = ℚ + ℤ_v` and
  every element of `ℚ_v` is a rational times a unit, so `E` has a rational minimal model over `ℚ_v`
  (`exists_isMinimal_map`); it is integral with unit discriminant, hence also over `𝓞_𝔭`, where it
  is therefore minimal (`isMinimal_baseChange_of_notMem`).
* Clause 1 (`localFactorK_clause_split`, `N𝔭 = p`, `𝔭² ∤ p`): now `K_𝔭 = ℚ + 𝓞_𝔭` too, so `E` has a
  rational minimal model over `K_𝔭`, which is minimal over `ℚ_v` as well
  (`isMinimal_map_of_isMinimal_map`: a better model over `ℚ_v` would come from a better rational
  model).

`LocalFactorInert` (GLUE; not needed for `ArtinFactorization`, see `ArtinUnconditional.lean`) is
the inert clause alone; `localFactorK_of_inert`,
`artinFactorization_of_inert` and `genusLower34_of_inert` are the reductions.
-/

noncomputable section

open NumberField IsDedekindDomain WeierstrassCurve Rat.HeightOneSpectrum

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open ZInQ.Contrib.CloudB3RC53.CST ZInQ.Manuscript.RC.PrintsAnalytic

section Place

variable {K : Type} [Field K] [NumberField K] {p : ℕ} {𝔭 : HeightOneSpectrum (𝓞 K)}

/-- Membership in `𝓞_𝔭` as a lift (PROVED). -/
theorem exists_lift_iff (x : 𝔭.adicCompletion K) :
    (∃ r : 𝔭.adicCompletionIntegers K, algebraMap _ (𝔭.adicCompletion K) r = x) ↔
      x ∈ 𝔭.adicCompletionIntegers K :=
  ⟨fun ⟨r, hr⟩ => hr ▸ r.2, fun h => ⟨⟨x, h⟩, rfl⟩⟩

/-- **(D1) at an unramified prime of norm `p`** (PROVED). -/
theorem decomp_D1 (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) (hN : Ideal.absNorm 𝔭.asIdeal = p)
    (hu : UnramifiedOver 𝔭 p) (ι : ℚ →+* 𝔭.adicCompletion K) :
    ∀ x : 𝔭.adicCompletion K, ∃ q : ℚ, ∃ r : 𝔭.adicCompletionIntegers K,
      x = ι q + algebraMap _ (𝔭.adicCompletion K) r := by
  intro x
  obtain ⟨q, hq⟩ := exists_rat_sub_mem_integers hp h𝔭 hN hu ι x
  exact ⟨q, ⟨_, hq⟩, by simp⟩

/-- **(D2) at an unramified prime** (PROVED). -/
theorem decomp_D2 (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) (hu : UnramifiedOver 𝔭 p)
    (ι : ℚ →+* 𝔭.adicCompletion K) :
    ∀ x : 𝔭.adicCompletion K, x ≠ 0 → ∃ q : ℚ, q ≠ 0 ∧ ∃ u : (𝔭.adicCompletionIntegers K)ˣ,
      x = ι q * algebraMap _ (𝔭.adicCompletion K) (u : 𝔭.adicCompletionIntegers K) := by
  intro x hx
  obtain ⟨q, hq0, h1, h2⟩ := exists_rat_associated hp h𝔭 hu ι hx
  have hιq : ι q ≠ 0 := (map_ne_zero ι).mpr hq0
  refine ⟨q, hq0, ⟨⟨x / ι q, h1⟩, ⟨ι q / x, h2⟩, ?_, ?_⟩, ?_⟩
  · apply Subtype.ext; simp only [MulMemClass.coe_mul, OneMemClass.coe_one]; field_simp
  · apply Subtype.ext; simp only [MulMemClass.coe_mul, OneMemClass.coe_one]; field_simp
  · show x = ι q * (x / ι q)
    field_simp

/-- **Integrality of rationals agrees at all primes above `p`** (PROVED). -/
theorem hint_rat (hp : p.Prime) (h𝔭 : 𝔭 ∈ primesAbove K p) {L : Type} [Field L] [NumberField L]
    {𝔮 : HeightOneSpectrum (𝓞 L)} (h𝔮 : 𝔮 ∈ primesAbove L p) (ι : ℚ →+* 𝔭.adicCompletion K)
    (ι' : ℚ →+* 𝔮.adicCompletion L) (q : ℚ) :
    (∃ r : 𝔭.adicCompletionIntegers K, algebraMap _ (𝔭.adicCompletion K) r = ι q) ↔
      (∃ r' : 𝔮.adicCompletionIntegers L, algebraMap _ (𝔮.adicCompletion L) r' = ι' q) := by
  rw [exists_lift_iff, exists_lift_iff, iota_mem_integers_iff hp h𝔭, iota_mem_integers_iff hp h𝔮]

end Place

section Valuation

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- For an integral `W`, good reduction makes the discriminant of the integral model a unit
(PROVED). -/
theorem isUnit_integralModel_Δ (W : WeierstrassCurve F) [W.HasGoodReduction R] :
    IsUnit (integralModel R W).Δ := by
  have h := (‹W.HasGoodReduction R›).goodReduction
  rw [← integralModel_Δ_eq R W] at h
  by_contra hu
  have hm : (integralModel R W).Δ ∈ IsLocalRing.maximalIdeal R := hu
  have := (IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem (K := F)
    (IsDiscreteValuationRing.maximalIdeal R) _).mpr hm
  exact this.ne h

end Valuation

variable {K : Type} [Field K] [NumberField K]

/-- `IsUnit` in `𝓞_𝔭` of a lift (PROVED). -/
theorem isUnit_lift_iff {𝔭 : HeightOneSpectrum (𝓞 K)} (r : 𝔭.adicCompletionIntegers K) :
    IsUnit r ↔ ((r : 𝔭.adicCompletion K) ≠ 0 ∧ (r : 𝔭.adicCompletion K) ∈ 𝔭.adicCompletionIntegers K ∧
      (r : 𝔭.adicCompletion K)⁻¹ ∈ 𝔭.adicCompletionIntegers K) := by
  constructor
  · rintro ⟨u, rfl⟩
    have h2 : (((u⁻¹ : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) :
        𝔭.adicCompletion K) * ((u : 𝔭.adicCompletionIntegers K) : 𝔭.adicCompletion K) = 1 := by
      rw [← MulMemClass.coe_mul, u.inv_mul]; rfl
    refine ⟨fun h => ?_, (u : 𝔭.adicCompletionIntegers K).2, ?_⟩
    · rw [h, mul_zero] at h2; exact zero_ne_one h2
    · rw [← eq_inv_of_mul_eq_one_left h2]; exact Subtype.prop _
  · rintro ⟨h0, -, hinv⟩
    refine ⟨⟨r, ⟨_, hinv⟩, ?_, ?_⟩, rfl⟩
    · apply Subtype.ext; simp [h0]
    · apply Subtype.ext; simp [h0]

/-- **The comparison of local polynomials through a common rational minimal model** (PROVED). -/
theorem localPoly_eq_of_rat_model (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : 𝔭 ∈ primesAbove K (natGenerator v)) (hN : Ideal.absNorm 𝔭.asIdeal = natGenerator v)
    (C₀ : VariableChange ℚ)
    [hv : IsMinimal (v.adicCompletionIntegers ℚ) ((C₀ • E).map (algebraMap ℚ (v.adicCompletion ℚ)))]
    [hk : IsMinimal (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))] :
    localPolyK E 𝔭 = localPolyQ E v := by
  have hp := prime_natGenerator v
  have : Fact (natGenerator v).Prime := ⟨hp⟩
  have hfinv := finite_residueField (𝔭 := v)
  have hfink := finite_residueField (𝔭 := 𝔭)
  have hcv : Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = natGenerator v := by
    rw [natCard_residueField', absNorm_rat]
  have hck : Nat.card (IsLocalRing.ResidueField (𝔭.adicCompletionIntegers K)) = natGenerator v := by
    rw [natCard_residueField', hN]
  have := charP_residueField hp (mem_primesAbove_rat v)
  have := charP_residueField hp h𝔭
  set ψ := ringEquivOfCard hp hcv hck
  rw [localPolyK_eq, localPolyQ_eq, ← localPolynomial_map_smul (iotaK 𝔭) E C₀,
    ← localPolynomial_map_smul (algebraMap ℚ (v.adicCompletion ℚ)) E C₀]
  have hΔ1 : ((C₀ • E).map (algebraMap ℚ (v.adicCompletion ℚ))).Δ ≠ 0 := by
    rw [map_Δ]; exact (map_ne_zero _).mpr (C₀ • E).isUnit_Δ.ne_zero
  have hΔ2 : ((C₀ • E).map (iotaK 𝔭)).Δ ≠ 0 := by
    rw [map_Δ]; exact (map_ne_zero _).mpr (C₀ • E).isUnit_Δ.ne_zero
  exact (localPolynomial_eq_of_reduction_map _ _ hΔ1 hΔ2 ψ
    (reduction_map_eq_of_rat (p := natGenerator v) ψ _ _ (C₀ • E))).symm

/-- **Clause 1 of `LocalFactorK`** (PROVED): `N𝔭 = p`, `𝔭² ∤ p` ⇒ `L_𝔭(E/K) = L_p(E)`. -/
theorem localFactorK_clause_split (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : 𝔭 ∈ primesAbove K (natGenerator v)) (hN : Ideal.absNorm 𝔭.asIdeal = natGenerator v)
    (hu : UnramifiedOver 𝔭 (natGenerator v)) : localPolyK E 𝔭 = localPolyQ E v := by
  have hp := prime_natGenerator v
  obtain ⟨C₀, hC₀⟩ := exists_isMinimal_map (𝔭.adicCompletionIntegers K) (iotaK 𝔭)
    (decomp_D1 hp h𝔭 hN hu _) (decomp_D2 hp h𝔭 hu _) E
  have hmin : IsMinimal (v.adicCompletionIntegers ℚ)
      ((C₀ • E).map (algebraMap ℚ (v.adicCompletion ℚ))) :=
    isMinimal_map_of_isMinimal_map (v.adicCompletionIntegers ℚ) _ (iotaK 𝔭)
      (decomp_D1 hp (mem_primesAbove_rat v) (absNorm_rat v) (unramifiedOver_rat v) _)
      (decomp_D2 hp (mem_primesAbove_rat v) (unramifiedOver_rat v) _)
      (hint_rat hp (mem_primesAbove_rat v) h𝔭 _ _) (C₀ • E) (C₀ • E).isUnit_Δ.ne_zero hC₀
  exact localPoly_eq_of_rat_model E 𝔭 v h𝔭 hN C₀

/-- **Clause 2 of `LocalFactorK`** (PROVED): `N𝔭 = p` and `E` good at `p` ⇒ `L_𝔭(E/K) = L_p(E)`. -/
theorem localFactorK_clause_good (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ))
    (h𝔭 : 𝔭 ∈ primesAbove K (natGenerator v)) (hN : Ideal.absNorm 𝔭.asIdeal = natGenerator v)
    (hgood : GoodAt E v) : localPolyK E 𝔭 = localPolyQ E v := by
  have hp := prime_natGenerator v
  set ιv := algebraMap ℚ (v.adicCompletion ℚ)
  obtain ⟨C₀, hC₀⟩ := exists_isMinimal_map (v.adicCompletionIntegers ℚ) ιv
    (decomp_D1 hp (mem_primesAbove_rat v) (absNorm_rat v) (unramifiedOver_rat v) _)
    (decomp_D2 hp (mem_primesAbove_rat v) (unramifiedOver_rat v) _) E
  -- good reduction of the rational model over `ℚ_v`
  have hEΔ : (E.map ιv).Δ ≠ 0 := by rw [map_Δ]; exact (map_ne_zero ιv).mpr E.isUnit_Δ.ne_zero
  have hgood₀ : ((C₀ • E).map ιv).HasGoodReduction (v.adicCompletionIntegers ℚ) := by
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
    have hg : ((E.map ιv).minimal (v.adicCompletionIntegers ℚ)).HasGoodReduction
        (v.adicCompletionIntegers ℚ) := hgood
    rw [h1]
    exact (ZInQ.Manuscript.RC.TwistDictionary.hasGoodReduction_smul_iff _ hm _).mpr hg
  -- the rational discriminant is a `p`-adic unit
  have hunit := isUnit_integralModel_Δ (R := v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)
  have hΔv : ιv (C₀ • E).Δ ≠ 0 ∧ ιv (C₀ • E).Δ ∈ v.adicCompletionIntegers ℚ ∧
      (ιv (C₀ • E).Δ)⁻¹ ∈ v.adicCompletionIntegers ℚ := by
    have := (isUnit_lift_iff _).mp hunit
    have e : ((integralModel (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)).Δ :
        v.adicCompletion ℚ) = ιv (C₀ • E).Δ := by
      have := integralModel_Δ_eq (v.adicCompletionIntegers ℚ) ((C₀ • E).map ιv)
      rw [map_Δ] at this
      exact this
    rwa [e] at this
  have hpΔ := (iota_unit_iff hp (mem_primesAbove_rat v) ιv _).mp hΔv
  have hΔk := (iota_unit_iff hp h𝔭 (iotaK 𝔭) _).mpr hpΔ
  -- integral over `𝓞_𝔭`, with unit discriminant: minimal
  have hint : IsIntegral (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭)) :=
    isIntegral_map_of_hint (𝔭.adicCompletionIntegers K) (iotaK 𝔭) ιv
      (hint_rat hp h𝔭 (mem_primesAbove_rat v) _ _) (C₀ • E) inferInstance
  have hmin : IsMinimal (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭)) := by
    have hI := integralModel_Δ_eq (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))
    rw [map_Δ] at hI
    have hu : IsUnit (integralModel (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))).Δ := by
      rw [isUnit_lift_iff]
      have e : ((integralModel (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))).Δ :
          𝔭.adicCompletion K) = iotaK 𝔭 (C₀ • E).Δ := hI
      rw [e]; exact hΔk
    have hnot : (integralModel (𝔭.adicCompletionIntegers K) ((C₀ • E).map (iotaK 𝔭))).Δ ∉
        IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K) ^ 12 := fun h =>
      (IsLocalRing.mem_maximalIdeal _).mp (Ideal.pow_le_self (by norm_num) h) hu
    have := ZInQ.Literature.isMinimal_baseChange_of_notMem (K := 𝔭.adicCompletion K) _ hnot
    rwa [baseChange_integralModel_eq] at this
  exact localPoly_eq_of_rat_model E 𝔭 v h𝔭 hN C₀

/-- **The inert clause of `LocalFactorK`** (GLUE; the one remaining local input: Frobenius
characteristic polynomial / unramified base change. For `N𝔭 = p²`, `𝔭² ∤ p` (`K_𝔭/ℚ_p` unramified
quadratic): `L_𝔭(T²) = L_p(T) L_p(−T)`, i.e. for good `p`, `|Ẽ(𝔽_{p²})| = p² + 1 − (a_p² − 2p)`;
split multiplicative stays split, non-split becomes split, additive stays additive). -/
def LocalFactorInert : Prop :=
  ∀ (E : WeierstrassCurve ℚ) [E.IsElliptic] (K : Type) [Field K] [NumberField K]
    (𝔭 : HeightOneSpectrum (𝓞 K)) (v : HeightOneSpectrum (𝓞 ℚ)),
    𝔭 ∈ primesAbove K (natGenerator v) →
      Ideal.absNorm 𝔭.asIdeal = natGenerator v ^ 2 → UnramifiedOver 𝔭 (natGenerator v) →
        Polynomial.expand ℤ 2 (localPolyK E 𝔭) =
          localPolyQ E v * (localPolyQ E v).comp (Polynomial.C (-1) * Polynomial.X)

/-- **`LocalFactorK` from its inert clause** (PROVED): clauses 1 and 2 are
`localFactorK_clause_split` and `localFactorK_clause_good`. -/
theorem localFactorK_of_inert (h : LocalFactorInert) : LocalFactorK :=
  fun E _ K _ _ 𝔭 v h𝔭 => ⟨fun hN hu => localFactorK_clause_split E 𝔭 v h𝔭 hN hu,
    fun hN hg => localFactorK_clause_good E 𝔭 v h𝔭 hN hg, h E K 𝔭 v h𝔭⟩

/-- **`ArtinFactorization` from the inert clause** (PROVED reduction): from `HasseConvergence`
(`RC/PrintsAnalytic`), `GoodReductionOffLevel` and `LocalFactorInert`. -/
theorem artinFactorization_of_inert (hH : HasseConvergence) (hG : GoodReductionOffLevel)
    (h : LocalFactorInert) : ArtinFactorization :=
  artinFactorization_of_local hH hG (localFactorK_of_inert h)

/-- **(3.4) from the printed leaves and the inert clause** (PROVED reduction). -/
theorem genusLower34_of_inert (P : Prints) (hH : HasseConvergence) (hG : GoodReductionOffLevel)
    (h : LocalFactorInert) : GenusLower34 :=
  genusLower34_of_local P hH hG (localFactorK_of_inert h)

end ZInQ.Contrib.CloudB3RC53.GenusOdd
