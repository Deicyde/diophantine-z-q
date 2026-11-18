import Mathlib.AlgebraicGeometry.EllipticCurve.Reduction
import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Invariance
import ZInQKernel.RouteK.Rank.LFunctionCd

/-!
# GenusOdd: rational minimal models over a discretely valued field (PROVED)

Generic setting: `R` a discrete valuation ring with fraction field `F`, `k` a field and
`ι : k →+* F`, satisfying the decomposition hypotheses

* (D1) every `x ∈ F` is `ι q + r` with `q ∈ k`, `r ∈ R`;
* (D2) every `x ≠ 0` in `F` is `ι q · u` with `q ∈ k^×`, `u ∈ R^×`.

(For `k = ℚ` and `F = ℚ_p`, or `F = K_𝔭` with `e = f = 1`, these hold.)

* `exists_factor` (Q1): every change of variables over `F` is `D * C₀.map ι` with `D` integral
  (`IsIntegralVC`: it comes from a change of variables over `R`) and `C₀` over `k`;
* `isIntegral_smul_iff`, `isMinimal_smul` (Q2): integral changes of variables preserve
  integrality and minimality;
* `exists_isMinimal_map` (Q3): every curve over `k` has a change of variables over `k` after which
  it is minimal over `R`;
* `isIntegral_map_of_hint`, `isMinimal_map_of_isMinimal_map` (Q4): if two such settings over the
  same `k` have the same integral elements of `k`, a `k`-model minimal for the second is minimal
  for the first (the first satisfying (D1), (D2)).
-/

noncomputable section

open WeierstrassCurve IsDiscreteValuationRing IsDedekindDomain.HeightOneSpectrum

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

section Generic

variable (R : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- An integral change of variables over `F`: one coming from a change of variables over `R`
(so `u` is a unit of `R` and `r, s, t ∈ R`). -/
def IsIntegralVC (D : VariableChange F) : Prop :=
  ∃ CR : VariableChange R, CR.baseChange F = D

variable {R}

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- The inverse of an integral change of variables is integral (PROVED). -/
theorem IsIntegralVC.inv {D : VariableChange F} (h : IsIntegralVC R D) : IsIntegralVC R D⁻¹ := by
  obtain ⟨CR, rfl⟩ := h
  exact ⟨CR⁻¹, (VariableChange.mapHom (algebraMap R F)).map_inv CR⟩

variable (R)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- An integral change of variables preserves integrality (PROVED). -/
theorem isIntegral_smul {D : VariableChange F} (h : IsIntegralVC R D) (W : WeierstrassCurve F)
    [hW : IsIntegral R W] : IsIntegral R (D • W) := by
  obtain ⟨CR, rfl⟩ := h
  obtain ⟨Wi, hWi⟩ := hW.integral
  refine ⟨⟨CR • Wi, ?_⟩⟩
  rw [hWi]
  exact map_variableChange Wi CR (algebraMap R F)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- **Integral changes of variables preserve integrality both ways** (PROVED). -/
theorem isIntegral_smul_iff {D : VariableChange F} (h : IsIntegralVC R D) (W : WeierstrassCurve F) :
    IsIntegral R (D • W) ↔ IsIntegral R W := by
  refine ⟨fun h' => ?_, fun h' => isIntegral_smul R h W⟩
  have := isIntegral_smul R h.inv (D • W)
  rwa [inv_smul_smul] at this

/-- A unit of `R` has valuation one (PROVED). -/
theorem valuation_algebraMap_unit (a : Rˣ) :
    valuation F (maximalIdeal R) (algebraMap R F (a : R)) = 1 := by
  rw [valuation_of_algebraMap, intValuation_eq_one_iff]
  exact fun h => (maximalIdeal R).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h a.isUnit)

/-- An integral change of variables does not change the valuation of the discriminant
(PROVED). -/
theorem valuation_Δ_smul {D : VariableChange F} (h : IsIntegralVC R D) (W : WeierstrassCurve F) :
    valuation F (maximalIdeal R) (D • W).Δ = valuation F (maximalIdeal R) W.Δ := by
  obtain ⟨CR, rfl⟩ := h
  have hu : (((CR.baseChange F).u⁻¹ : Fˣ) : F) = algebraMap R F ((CR.u⁻¹ : Rˣ) : R) := rfl
  rw [variableChange_Δ, map_mul, map_pow, hu, valuation_algebraMap_unit, one_pow, one_mul]

/-- **Minimality through the valuation of the discriminant** (PROVED): `W` is minimal iff it is
integral and no integral model has a discriminant of larger valuation. -/
theorem isMinimal_iff_forall (W : WeierstrassCurve F) :
    IsMinimal R W ↔ IsIntegral R W ∧ ∀ C : VariableChange F, IsIntegral R (C • W) →
      valuation F (maximalIdeal R) (C • W).Δ ≤ valuation F (maximalIdeal R) W.Δ := by
  rw [isMinimal_iff]
  constructor
  · rintro ⟨h1, H⟩
    have h1' : IsIntegral R ((1 : VariableChange F) • W) := h1
    rw [one_smul] at h1'
    refine ⟨h1', fun C hC => ?_⟩
    have key : valuation_Δ_aux R (C • W) ≤ valuation_Δ_aux R ((1 : VariableChange F) • W) := by
      rcases le_total (valuation_Δ_aux R (C • W)) (valuation_Δ_aux R ((1 : VariableChange F) • W))
        with h | h
      · exact h
      · exact H hC h
    rw [one_smul] at key
    rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral,
      valuation_Δ_aux_eq_of_isIntegral] at key
    exact key
  · rintro ⟨h1, H⟩
    refine ⟨show IsIntegral R ((1 : VariableChange F) • W) by rw [one_smul]; exact h1,
      fun C hC _ => ?_⟩
    have hC' : IsIntegral R (C • W) := hC
    show valuation_Δ_aux R (C • W) ≤ valuation_Δ_aux R ((1 : VariableChange F) • W)
    rw [one_smul, ← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral,
      valuation_Δ_aux_eq_of_isIntegral]
    exact H C hC'

/-- **Integral changes of variables preserve minimality** (PROVED). -/
theorem isMinimal_smul {D : VariableChange F} (h : IsIntegralVC R D) (W : WeierstrassCurve F)
    (hW : IsMinimal R W) : IsMinimal R (D • W) := by
  have hW' := (isMinimal_iff_forall R W).mp hW
  have : IsIntegral R W := hW'.1
  refine (isMinimal_iff_forall R _).mpr ⟨isIntegral_smul R h W, fun C hC => ?_⟩
  rw [smul_smul] at hC ⊢
  rw [valuation_Δ_smul R h]
  exact hW'.2 _ hC

variable {k : Type*} [Field k] (ι : k →+* F)

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
/-- **(Q1) Factorization of a change of variables** (PROVED): under (D1), (D2), every change of
variables over `F` is an integral one times one coming from `k`. -/
theorem exists_factor
    (hD1 : ∀ x : F, ∃ q : k, ∃ r : R, x = ι q + algebraMap R F r)
    (hD2 : ∀ x : F, x ≠ 0 → ∃ q : k, q ≠ 0 ∧ ∃ u : Rˣ, x = ι q * algebraMap R F (u : R))
    (C : VariableChange F) :
    ∃ D : VariableChange F, IsIntegralVC R D ∧ ∃ C₀ : VariableChange k, C = D * C₀.map ι := by
  obtain ⟨q, hq, a, hu⟩ := hD2 C.u C.u.ne_zero
  have hιq : ι q ≠ 0 := (map_ne_zero ι).mpr hq
  obtain ⟨q₁, ρ, h1⟩ := hD1 (C.r / ι q ^ 2)
  obtain ⟨q₂, σ, h2⟩ := hD1 (C.s / ι q)
  obtain ⟨q₃, τ, h3⟩ := hD1 ((C.t - algebraMap R F ρ * ι (q₂ * q) * ι q ^ 2) / ι q ^ 3)
  refine ⟨(⟨a, ρ, σ, τ⟩ : VariableChange R).baseChange F, ⟨_, rfl⟩,
    ⟨Units.mk0 q hq, q₁ * q ^ 2, q₂ * q, q₃ * q ^ 3⟩, ?_⟩
  rw [div_eq_iff (pow_ne_zero 2 hιq)] at h1
  rw [div_eq_iff hιq] at h2
  rw [div_eq_iff (pow_ne_zero 3 hιq)] at h3
  ext
  · simp only [VariableChange.mul_def, VariableChange.baseChange, VariableChange.map,
      Units.val_mul, Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0]
    rw [hu, mul_comm]
  · simp only [VariableChange.mul_def, VariableChange.baseChange, VariableChange.map,
      Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, map_mul, map_pow]
    linear_combination h1
  · simp only [VariableChange.mul_def, VariableChange.baseChange, VariableChange.map,
      Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, map_mul]
    linear_combination h2
  · simp only [VariableChange.mul_def, VariableChange.baseChange, VariableChange.map,
      Units.coe_map, MonoidHom.coe_ofClass, Units.val_mk0, map_mul, map_pow] at h3 ⊢
    linear_combination h3

/-- **(Q3) A minimal model defined over `k`** (PROVED): under (D1), (D2), some change of variables
over `k` makes `W₀` minimal over `R`. -/
theorem exists_isMinimal_map
    (hD1 : ∀ x : F, ∃ q : k, ∃ r : R, x = ι q + algebraMap R F r)
    (hD2 : ∀ x : F, x ≠ 0 → ∃ q : k, q ≠ 0 ∧ ∃ u : Rˣ, x = ι q * algebraMap R F (u : R))
    (W₀ : WeierstrassCurve k) : ∃ C₀ : VariableChange k, IsMinimal R ((C₀ • W₀).map ι) := by
  obtain ⟨C, hC⟩ := (W₀.map ι).exists_isMinimal R
  obtain ⟨D, hD, C₀, rfl⟩ := exists_factor R ι hD1 hD2 C
  refine ⟨C₀, ?_⟩
  have h : (C₀ • W₀).map ι = D⁻¹ • ((D * C₀.map ι) • W₀.map ι) := by
    rw [mul_smul, inv_smul_smul, map_variableChange]
  rw [h]
  exact isMinimal_smul R hD.inv _ hC

variable {R' : Type*} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
  {F' : Type*} [Field F'] [Algebra R' F'] [IsFractionRing R' F'] (ι' : k →+* F')

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] [IsDomain R']
  [IsDiscreteValuationRing R'] [IsFractionRing R' F'] in
/-- **Integrality of a `k`-model transfers** (PROVED) between two settings with the same
integral elements of `k`. -/
theorem isIntegral_map_of_hint
    (hint : ∀ q : k, (∃ r : R, algebraMap R F r = ι q) ↔ (∃ r' : R', algebraMap R' F' r' = ι' q))
    (W₀ : WeierstrassCurve k) (h : IsIntegral R' (W₀.map ι')) : IsIntegral R (W₀.map ι) := by
  apply isIntegral_of_exists_lift R
  · exact (hint W₀.a₁).mpr ⟨_, (integralModel_a₁_eq R' (W₀.map ι')).trans (by simp)⟩
  · exact (hint W₀.a₂).mpr ⟨_, (integralModel_a₂_eq R' (W₀.map ι')).trans (by simp)⟩
  · exact (hint W₀.a₃).mpr ⟨_, (integralModel_a₃_eq R' (W₀.map ι')).trans (by simp)⟩
  · exact (hint W₀.a₄).mpr ⟨_, (integralModel_a₄_eq R' (W₀.map ι')).trans (by simp)⟩
  · exact (hint W₀.a₆).mpr ⟨_, (integralModel_a₆_eq R' (W₀.map ι')).trans (by simp)⟩

/-- **(Q4) Minimality descends** (PROVED): if `(R, F, ι)` satisfies (D1), (D2) and both settings
have the same integral elements of `k`, a `k`-model minimal over `R'` is minimal over `R`. -/
theorem isMinimal_map_of_isMinimal_map
    (hD1 : ∀ x : F, ∃ q : k, ∃ r : R, x = ι q + algebraMap R F r)
    (hD2 : ∀ x : F, x ≠ 0 → ∃ q : k, q ≠ 0 ∧ ∃ u : Rˣ, x = ι q * algebraMap R F (u : R))
    (hint : ∀ q : k, (∃ r : R, algebraMap R F r = ι q) ↔ (∃ r' : R', algebraMap R' F' r' = ι' q))
    (W₀ : WeierstrassCurve k) (hΔ : W₀.Δ ≠ 0) (h' : IsMinimal R' (W₀.map ι')) :
    IsMinimal R (W₀.map ι) := by
  obtain ⟨C₀, hM⟩ := exists_isMinimal_map R ι hD1 hD2 W₀
  have hmin' := (isMinimal_iff_forall R' _).mp h'
  have hminM := (isMinimal_iff_forall R _).mp hM
  have hV : IsIntegral R (W₀.map ι) := isIntegral_map_of_hint R ι ι' hint W₀ hmin'.1
  have hMint' : IsIntegral R' ((C₀ • W₀).map ι') :=
    isIntegral_map_of_hint R' ι' ι (fun q => (hint q).symm) _ hminM.1
  -- the comparison in the second setting: `v'(u₀⁻¹) ≤ 1`
  have key' := hmin'.2 (C₀.map ι') (by rw [map_variableChange]; exact hMint')
  have hu' : (((C₀.map ι').u⁻¹ : F'ˣ) : F') = ι' ((C₀.u⁻¹ : kˣ) : k) := rfl
  have hu : (((C₀.map ι).u⁻¹ : Fˣ) : F) = ι ((C₀.u⁻¹ : kˣ) : k) := rfl
  rw [variableChange_Δ, map_mul, map_pow, hu'] at key'
  have hΔ' : valuation F' (maximalIdeal R') (W₀.map ι').Δ ≠ 0 := by
    rw [Ne, map_eq_zero, map_Δ]
    exact (map_ne_zero ι').mpr hΔ
  have hle' : valuation F' (maximalIdeal R') (ι' ((C₀.u⁻¹ : kˣ) : k)) ≤ 1 := by
    have h2 := (mul_le_iff_le_one_left (zero_lt_iff.mpr hΔ')).mp key'
    exact (pow_le_one_iff (by norm_num : (12 : ℕ) ≠ 0)).mp h2
  obtain ⟨r', hr'⟩ := exists_lift_of_le_one hle'
  obtain ⟨r, hr⟩ := (hint _).mpr ⟨r', hr'⟩
  have hle : valuation F (maximalIdeal R) (ι ((C₀.u⁻¹ : kˣ) : k)) ≤ 1 := by
    rw [← hr]; exact valuation_le_one _ r
  -- `v(Δ V) = v(Δ M)`
  have hMV : (C₀ • W₀).map ι = C₀.map ι • W₀.map ι := (map_variableChange W₀ C₀ ι).symm
  have h1 : valuation F (maximalIdeal R) ((C₀ • W₀).map ι).Δ ≤
      valuation F (maximalIdeal R) (W₀.map ι).Δ := by
    rw [hMV, variableChange_Δ, map_mul, map_pow, hu]
    exact mul_le_of_le_one_left' (pow_le_one' hle 12)
  have h2 : valuation F (maximalIdeal R) (W₀.map ι).Δ ≤
      valuation F (maximalIdeal R) ((C₀ • W₀).map ι).Δ := by
    have := hminM.2 (C₀.map ι)⁻¹ (by rw [hMV, inv_smul_smul]; exact hV)
    rw [hMV, inv_smul_smul] at this
    rw [hMV]
    exact this
  refine (isMinimal_iff_forall R _).mpr ⟨hV, fun C hC => ?_⟩
  have hCV : C • W₀.map ι = (C * (C₀.map ι)⁻¹) • (C₀ • W₀).map ι := by
    rw [hMV, mul_smul, inv_smul_smul]
  have := hminM.2 (C * (C₀.map ι)⁻¹) (by rw [← hCV]; exact hC)
  rw [← hCV] at this
  exact this.trans h1

end Generic

end ZInQ.Contrib.CloudB3RC53.GenusOdd
