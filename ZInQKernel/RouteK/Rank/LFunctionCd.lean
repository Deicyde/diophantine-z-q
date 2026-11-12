import ZInQKernel.Model.Field.ShortWeierstrass

/-!
# Mathlib's L-function of the congruent number curves `C_d`

The CR₃ literature Props (`ZInQKernel/Hypotheses/CR3Literature.lean`) are stated over Mathlib's
`WeierstrassCurve.LSeries` of `C_d : y² = x³ − d² x`, i.e. `shortCurve (-(d : ℚ) ^ 2)`. Mathlib
defines it as the Euler product over the places `v` of `ℚ` of the local factors of the minimal
model of `C_d` over the completion `ℚ_v` (chosen by `Classical.choice`). This file computes it,
for odd squarefree `d` (this covers `d ≡ 5 (mod 8)`).

## Main results

* Generic, over a discrete valuation ring `R` with fraction field `K`:
  `isMinimal_baseChange_of_notMem` (an integral model with `Δ ∉ 𝔪 ^ 12` is minimal),
  `localPolynomial_of_hasGoodReduction` and `localPolynomial_of_hasAdditiveReduction`
  (`localPolynomial` is computed from any minimal model, not only Mathlib's chosen one).
* At `v` with `p = natGenerator v` (the completion `𝓞_v ≃ ℤ_p`, residue field `ZMod p`):
  `isMinimal_cdLocal` (the model `y² = x³ − d² x` is minimal at every `p`),
  `hasGoodReduction_cdLocal` (`p ∤ 2d`), `hasAdditiveReduction_cdLocal` (`p ∣ 2d`),
  `localPolynomial_cdLocal_of_not_dvd` (`1 − a_p T + p T²`, `a_p = p + 1 − #C_d(𝔽_p)`) and
  `localPolynomial_cdLocal_of_dvd` (`1`).
* Global: `LFunction_cd_apply_prime` (coefficient `a_p` at `p ∤ 2d`, `0` at `p ∣ 2d`),
  `LFunction_cd_apply_prime_eq_sub_card` (`a_p = p − #{(x, y) ∈ 𝔽_p² : y² = x³ − d² x}`),
  `LFunction_cd_apply_prime_pow`, `LFunction_cd_apply` (every coefficient) and `LSeries_cd_eq`
  (`L(C_d, s)` is the Dirichlet series of the standard Euler product).
-/

namespace ZInQ.Literature

open WeierstrassCurve IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "vK" => valuation K (IsDiscreteValuationRing.maximalIdeal R)

theorem vK_algebraMap_lt_one_iff (r : R) :
    vK (algebraMap R K r) < 1 ↔ r ∈ IsLocalRing.maximalIdeal R := by
  rw [valuation_of_algebraMap, intValuation_lt_one_iff_mem]; rfl

/-- An integral model whose discriminant is not in `m ^ 12` is minimal. -/
theorem isMinimal_baseChange_of_notMem (W : WeierstrassCurve R)
    (hΔ : W.Δ ∉ IsLocalRing.maximalIdeal R ^ 12) : IsMinimal R (W⁄K) := by
  have hI : IsIntegral R (W⁄K) := ⟨W, rfl⟩
  refine ⟨⟨by simpa using hI, fun C hC _ => ?_⟩⟩
  simp only [one_smul]
  have := hC
  rw [← Subtype.coe_le_coe, valuation_Δ_aux_eq_of_isIntegral, valuation_Δ_aux_eq_of_isIntegral,
    variableChange_Δ, map_mul, map_pow]
  by_cases h : vK (↑C.u⁻¹ : K) ≤ 1
  · exact mul_le_of_le_one_left zero_le (pow_le_one₀ zero_le h)
  · exfalso
    replace h := not_le.mp h
    have hu : vK (C.u : K) < 1 := by
      have : (C.u : K) = (↑C.u⁻¹ : K)⁻¹ := by simp
      rw [this, map_inv₀]
      exact inv_lt_one_of_one_lt₀ h
    obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hu.le
    rw [← hr, vK_algebraMap_lt_one_iff] at hu
    obtain ⟨δ, hδ⟩ := Δ_integral_of_isIntegral R (C • W⁄K)
    apply hΔ
    have key : algebraMap R K W.Δ = algebraMap R K (r ^ 12 * δ) := by
      rw [map_mul, map_pow, hr, hδ, variableChange_Δ, ← mul_assoc, ← mul_pow]
      simp [baseChange, map_Δ]
    rw [IsFractionRing.injective R K key]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hu 12)


theorem pow_twelve_eq_one {x : WithZero (Multiplicative ℤ)} (h : x ^ 12 = 1) : x = 1 := by
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exact absurd h (pow_lt_one₀ zero_le hx (by norm_num)).ne
  · exact hx
  · exact absurd h (one_lt_pow₀ hx (by norm_num)).ne'

/-- Two minimal models differ by a change of variables with `v(u) = 1`. -/
theorem vK_u_eq_one {W : WeierstrassCurve K} (hΔ : W.Δ ≠ 0) (C : VariableChange K)
    [hW : IsMinimal R W] [hCW : IsMinimal R (C • W)] : vK (C.u : K) = 1 := by
  have hI : IsIntegral R (C • W) := inferInstance
  have hI' : IsIntegral R W := inferInstance
  have h1 := hW.val_Δ_maximal.2 (j := C) hI
  have h2 := hCW.val_Δ_maximal.2 (j := C⁻¹) (by simpa using hI')
  simp only [one_smul, inv_smul_smul, ← Subtype.coe_le_coe,
    valuation_Δ_aux_eq_of_isIntegral] at h1 h2
  have hab : vK W.Δ = vK (C • W).Δ := by
    rcases le_total (vK W.Δ) (vK (C • W).Δ) with h | h
    · exact le_antisymm h (h1 h)
    · exact le_antisymm (h2 h) h
  rw [variableChange_Δ, map_mul, map_pow] at hab
  have ha : vK W.Δ ≠ 0 := (Valuation.ne_zero_iff _).mpr hΔ
  have h12 : vK (↑C.u⁻¹ : K) ^ 12 = 1 := by
    have := mul_right_cancel₀ ha (hab.symm.trans (one_mul _).symm)
    exact this
  have h3 := pow_twelve_eq_one h12
  have : (C.u : K) = (↑C.u⁻¹ : K)⁻¹ := by simp
  rw [this, map_inv₀, h3, inv_one]

/-- A change of variables with `v(u) = 1` between minimal models descends to the reductions. -/
theorem exists_reduction_variableChange (W : WeierstrassCurve K) (C : VariableChange K)
    [IsMinimal R W] [IsMinimal R (C • W)] (hu : vK (C.u : K) = 1) :
    ∃ C' : VariableChange (IsLocalRing.ResidueField R),
      (C • W).reduction R = C' • W.reduction R := by
  obtain ⟨r, hr⟩ := IsDiscreteValuationRing.exists_lift_of_le_one hu.le
  have hr1 : IsUnit r := by
    rw [← hr, valuation_of_algebraMap, intValuation_eq_one_iff] at hu
    exact IsLocalRing.notMem_maximalIdeal.mp hu
  obtain ⟨CR, hCR⟩ := variableChange_integral_of_u_integral (W := W) (W' := C • W) rfl
    (u := hr1.unit) hr
  have hI : integralModel R (C • W) = CR • integralModel R W := by
    apply WeierstrassCurve.map_injective (IsFractionRing.injective R K)
    show (integralModel R (C • W)).map _ = (CR • integralModel R W).map _
    rw [← map_variableChange]
    change (integralModel R (C • W))⁄K = CR.baseChange K • (integralModel R W)⁄K
    rw [baseChange_integralModel_eq, baseChange_integralModel_eq, hCR]
  refine ⟨CR.map (IsLocalRing.residue R), ?_⟩
  simp only [reduction, hI, map_variableChange]

end Generic

section Points

variable {F : Type*} [Field F]

theorem equation_variableChange_iff (E : WeierstrassCurve F) (C : VariableChange F) (x y : F) :
    (C • E).toAffine.Equation x y ↔
      E.toAffine.Equation (C.u ^ 2 * x + C.r) (C.u ^ 3 * y + C.s * C.u ^ 2 * x + C.t) := by
  have hu : (C.u : F) ≠ 0 := C.u.ne_zero
  rw [Affine.equation_iff, Affine.equation_iff]
  simp only [variableChange_a₁, variableChange_a₂, variableChange_a₃, variableChange_a₄,
    variableChange_a₆, Units.val_inv_eq_inv_val]
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    field_simp
    linear_combination h

set_option linter.unnecessarySeqFocus false in
set_option linter.unusedTactic false in
/-- The affine solutions of `C • E` and of `E` correspond. -/
noncomputable def solutionsVariableChangeEquiv (E : WeierstrassCurve F) (C : VariableChange F) :
    {xy : F × F // (C • E).toAffine.Equation xy.1 xy.2} ≃
      {xy : F × F // E.toAffine.Equation xy.1 xy.2} where
  toFun P := ⟨(C.u ^ 2 * P.1.1 + C.r, C.u ^ 3 * P.1.2 + C.s * C.u ^ 2 * P.1.1 + C.t),
    (equation_variableChange_iff E C _ _).mp P.2⟩
  invFun P := ⟨((P.1.1 - C.r) / C.u ^ 2, (P.1.2 - C.s * (P.1.1 - C.r) - C.t) / C.u ^ 3), by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    rw [equation_variableChange_iff]
    convert P.2 using 1 <;> field_simp <;> ring⟩
  left_inv P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> simp <;> field_simp <;> ring
  right_inv P := by
    have hu : (C.u : F) ≠ 0 := C.u.ne_zero
    ext <;> simp <;> field_simp <;> ring

/-- The points of an elliptic curve are the affine solutions and the point at infinity. -/
noncomputable def pointEquivOption (E : WeierstrassCurve F) [E.IsElliptic] :
    E.toAffine.Point ≃ Option {xy : F × F // E.toAffine.Equation xy.1 xy.2} :=
  (Equiv.subtypeUnivEquiv (p := fun _ : E.toAffine.Point => True) fun _ => trivial).symm.trans
    ((Affine.pointEquivSubtype (W' := E.toAffine) trivial).trans
      (Equiv.optionCongr
        (Equiv.subtypeEquivRight fun _ => ⟨fun ⟨h, _⟩ => h, fun h => ⟨h, trivial⟩⟩)))

theorem natCard_point_variableChange (E : WeierstrassCurve F) [E.IsElliptic]
    (C : VariableChange F) :
    Nat.card (C • E).toAffine.Point = Nat.card E.toAffine.Point :=
  Nat.card_congr ((pointEquivOption _).trans
    ((Equiv.optionCongr (solutionsVariableChangeEquiv E C)).trans (pointEquivOption E).symm))

end Points

section LocalPolynomial

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

local notation "vK" => valuation K (IsDiscreteValuationRing.maximalIdeal R)

theorem minimal_eq_smul (W : WeierstrassCurve K) :
    W.minimal R = (W.exists_isMinimal R).choose • W := rfl

theorem vK_minimal_Δ (W : WeierstrassCurve K) [IsMinimal R W] (hΔ : W.Δ ≠ 0) :
    vK (W.minimal R).Δ = vK W.Δ := by
  have : IsMinimal R ((W.exists_isMinimal R).choose • W) := (W.exists_isMinimal R).choose_spec
  rw [minimal_eq_smul, variableChange_Δ, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
    vK_u_eq_one hΔ, inv_one, one_pow, one_mul]

theorem vK_minimal_c₄ (W : WeierstrassCurve K) [IsMinimal R W] (hΔ : W.Δ ≠ 0) :
    vK (W.minimal R).c₄ = vK W.c₄ := by
  have : IsMinimal R ((W.exists_isMinimal R).choose • W) := (W.exists_isMinimal R).choose_spec
  rw [minimal_eq_smul, variableChange_c₄, map_mul, map_pow, Units.val_inv_eq_inv_val, map_inv₀,
    vK_u_eq_one hΔ, inv_one, one_pow, one_mul]

open Polynomial in
/-- The local polynomial at a place of additive reduction of a minimal model is `1`. -/
theorem localPolynomial_of_hasAdditiveReduction (W : WeierstrassCurve K) (hΔ : W.Δ ≠ 0)
    [h : HasAdditiveReduction R W] : W.localPolynomial R = 1 := by
  have hΔ' : vK (W.minimal R).Δ < 1 := by rw [vK_minimal_Δ W hΔ]; exact h.badReduction
  have hc' : vK (W.minimal R).c₄ < 1 := by rw [vK_minimal_c₄ W hΔ]; exact h.additiveReduction
  have h1 : ¬(W.minimal R).HasGoodReduction R := fun hg => hΔ'.ne hg.goodReduction
  have h2 : ¬(W.minimal R).HasSplitMultiplicativeReduction R := fun hs =>
    hc'.ne hs.toHasMultiplicativeReduction.multiplicativeReduction
  have h3 : ¬(W.minimal R).HasMultiplicativeReduction R := fun hm =>
    hc'.ne hm.multiplicativeReduction
  unfold localPolynomial
  simp only [h1, h2, h3, ↓reduceIte]

theorem natCard_point_reduction_minimal (W : WeierstrassCurve K) [h : HasGoodReduction R W] :
    Nat.card ((W.minimal R).reduction R).toAffine.Point =
      Nat.card (W.reduction R).toAffine.Point := by
  have hΔ : W.Δ ≠ 0 := fun h0 => by simpa [h0] using h.goodReduction
  have : IsMinimal R ((W.exists_isMinimal R).choose • W) := (W.exists_isMinimal R).choose_spec
  obtain ⟨C', hC'⟩ := exists_reduction_variableChange W _ (vK_u_eq_one hΔ (R := R)
    (W.exists_isMinimal R).choose)
  have : (W.reduction R).IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp h
  change Nat.card (((W.exists_isMinimal R).choose • W).reduction R).toAffine.Point = _
  rw [hC', natCard_point_variableChange]

open Polynomial in
/-- The local polynomial at a place of good reduction of a minimal model `W` is
`1 - a T + q T ^ 2` with `a = q + 1 - #W̃(κ)`, computed from `W` itself. -/
theorem localPolynomial_of_hasGoodReduction (W : WeierstrassCurve K)
    [h : HasGoodReduction R W] : W.localPolynomial R =
      1 - C ((Nat.card (IsLocalRing.ResidueField R) : ℤ) + 1 -
        Nat.card (W.reduction R).toAffine.Point) * X +
      C (Nat.card (IsLocalRing.ResidueField R) : ℤ) * X ^ 2 := by
  have hΔ : W.Δ ≠ 0 := fun h0 => by simpa [h0] using h.goodReduction
  have hg : (W.minimal R).HasGoodReduction R :=
    ⟨by rw [vK_minimal_Δ W hΔ]; exact h.goodReduction⟩
  unfold localPolynomial
  simp only [hg, ↓reduceIte, natCard_point_reduction_minimal]

end LocalPolynomial

section FieldIso

variable {F F' : Type*} [Field F] [Field F']

theorem natCard_point_map_ringEquiv (E : WeierstrassCurve F) [E.IsElliptic] (f : F ≃+* F') :
    Nat.card (E.map (f : F →+* F')).toAffine.Point = Nat.card E.toAffine.Point := by
  refine Nat.card_congr ((pointEquivOption _).trans
    ((Equiv.optionCongr ?_).trans (pointEquivOption E).symm))
  exact (Equiv.subtypeEquiv (f.toEquiv.prodCongr f.toEquiv) fun xy =>
    (Affine.map_equation (W := E.toAffine) (f := (f : F →+* F')) f.injective xy.1 xy.2).symm).symm

end FieldIso

section Cd

/-- The integral model `y² = x³ − d² x` over any commutative ring. -/
def cdModel (S : Type*) [CommRing S] (d : ℕ) : WeierstrassCurve S where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -(d : S) ^ 2
  a₆ := 0

variable {S : Type*} [CommRing S] (d : ℕ)

theorem cdModel_Δ : (cdModel S d).Δ = ((2 * d : ℕ) : S) ^ 6 := by
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, cdModel]
  push_cast; ring

theorem cdModel_c₄ : (cdModel S d).c₄ = ((48 * d ^ 2 : ℕ) : S) := by
  simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄, cdModel]
  push_cast; ring

theorem cdModel_map {T : Type*} [CommRing T] (f : S →+* T) : (cdModel S d).map f = cdModel T d := by
  ext <;> simp [cdModel]

theorem cdModel_eq_shortCurve (F : Type*) [Field F] : cdModel F d = shortCurve (-(d : F) ^ 2) :=
  rfl

end Cd

section Completion

open Rat.HeightOneSpectrum

local instance (q : Nat.Primes) : Fact q.1.Prime := ⟨q.2⟩

instance factNatGenerator (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Fact (natGenerator v).Prime := ⟨prime_natGenerator v⟩

variable (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))

/-- The ring isomorphism `𝓞_v ≃ ℤ_p`. -/
noncomputable abbrev ePadic : v.adicCompletionIntegers ℚ ≃+* ℤ_[primesEquiv v] :=
  (adicCompletionIntegers.padicIntEquiv v).toRingEquiv

theorem isUnit_intCast_iff (n : ℤ) :
    IsUnit (n : v.adicCompletionIntegers ℚ) ↔ ¬ (natGenerator v : ℤ) ∣ n := by
  rw [← isUnit_map_iff (ePadic v), map_intCast, PadicInt.isUnit_iff,
    PadicInt.norm_intCast_eq_one_iff, isCoprime_comm]
  exact Irreducible.coprime_iff_not_dvd
    (Nat.prime_iff_prime_int.mp (prime_natGenerator v)).irreducible

theorem irreducible_natGenerator :
    Irreducible ((natGenerator v : ℕ) : v.adicCompletionIntegers ℚ) := by
  rw [← MulEquiv.irreducible_iff (ePadic v), map_natCast]
  exact PadicInt.irreducible_p

theorem maximalIdeal_eq_span :
    IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) =
      Ideal.span {((natGenerator v : ℕ) : v.adicCompletionIntegers ℚ)} :=
  (IsDiscreteValuationRing.irreducible_iff_uniformizer _).mp (irreducible_natGenerator v)

theorem intCast_mem_maximalIdeal_pow_iff (n : ℤ) (k : ℕ) :
    (n : v.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal _ ^ k ↔
      (natGenerator v : ℤ) ^ k ∣ n := by
  rw [maximalIdeal_eq_span, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← map_dvd_iff (ePadic v), map_pow, map_natCast, map_intCast]
  exact PadicInt.pow_p_dvd_int_iff k n

theorem natCast_mem_maximalIdeal_iff (n : ℕ) :
    (n : v.adicCompletionIntegers ℚ) ∈ IsLocalRing.maximalIdeal _ ↔ natGenerator v ∣ n := by
  have := intCast_mem_maximalIdeal_pow_iff v n 1
  simp only [pow_one, Int.cast_natCast] at this
  rw [this]; exact Int.natCast_dvd_natCast

/-- The residue field of `𝓞_v` is `ZMod p`. -/
noncomputable abbrev residueEquiv :
    IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ) ≃+* ZMod (natGenerator v) :=
  (IsLocalRing.ResidueField.mapEquiv (ePadic v)).trans PadicInt.residueField

theorem natCard_residueField :
    Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) = natGenerator v := by
  rw [Nat.card_congr (residueEquiv v).toEquiv, Nat.card_zmod]

/-- `C_d` over the completion `ℚ_v`. -/
noncomputable abbrev cdLocal (d : ℕ) : WeierstrassCurve (v.adicCompletion ℚ) :=
  (shortCurve (-(d : ℚ) ^ 2)).baseChange (v.adicCompletion ℚ)

theorem cdLocal_eq (d : ℕ) : cdLocal v d = cdModel (v.adicCompletion ℚ) d := by
  rw [cdLocal, ← cdModel_eq_shortCurve]; exact cdModel_map d _

theorem cdModel_baseChange (d : ℕ) :
    (cdModel (v.adicCompletionIntegers ℚ) d)⁄(v.adicCompletion ℚ) = cdLocal v d := by
  rw [cdLocal_eq]; exact cdModel_map d _

theorem not_dvd_two_mul_pow_six {p d : ℕ} (hp : p.Prime) (hd : Odd d) (hsq : Squarefree d) :
    ¬ (p : ℤ) ^ 12 ∣ (((2 * d : ℕ) ^ 6 : ℕ) : ℤ) := by
  intro h
  have h' : (p ^ 2) ^ 6 ∣ (2 * d) ^ 6 := by
    rw [← pow_mul]; exact_mod_cast h
  rw [Nat.pow_dvd_pow_iff (by norm_num)] at h'
  have h2d : Squarefree (2 * d) :=
    Nat.squarefree_mul_iff.mpr ⟨Nat.coprime_two_left.mpr hd, Nat.prime_two.squarefree, hsq⟩
  have := h2d p (by rw [← pow_two]; exact h')
  exact hp.one_lt.ne' (Nat.isUnit_iff.mp this)

theorem isMinimal_cdLocal {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    IsMinimal (v.adicCompletionIntegers ℚ) (cdLocal v d) := by
  rw [← cdModel_baseChange]
  apply isMinimal_baseChange_of_notMem
  rw [cdModel_Δ, ← Nat.cast_pow, ← Int.cast_natCast, intCast_mem_maximalIdeal_pow_iff]
  exact not_dvd_two_mul_pow_six (prime_natGenerator v) hd hsq

theorem cdLocal_Δ_eq (d : ℕ) :
    (cdLocal v d).Δ = algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      (((2 * d : ℕ) : v.adicCompletionIntegers ℚ) ^ 6) := by
  rw [← cdModel_baseChange, baseChange, map_Δ, cdModel_Δ]

theorem cdLocal_c₄_eq (d : ℕ) :
    (cdLocal v d).c₄ = algebraMap (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ)
      ((48 * d ^ 2 : ℕ) : v.adicCompletionIntegers ℚ) := by
  rw [← cdModel_baseChange, baseChange, map_c₄, cdModel_c₄]

theorem cdLocal_Δ_ne_zero {d : ℕ} (hd : d ≠ 0) : (cdLocal v d).Δ ≠ 0 := by
  rw [cdLocal_eq, cdModel_Δ, ← map_natCast (algebraMap ℚ (v.adicCompletion ℚ))]
  exact pow_ne_zero _ ((map_ne_zero _).mpr (Nat.cast_ne_zero.mpr (by omega)))

/-- Good reduction at `v ∤ 2d`. -/
theorem hasGoodReduction_cdLocal {d : ℕ} (hp : ¬ natGenerator v ∣ 2 * d) :
    HasGoodReduction (v.adicCompletionIntegers ℚ) (cdLocal v d) := by
  have hm : ((2 * d : ℕ) : v.adicCompletionIntegers ℚ) ^ 6 ∉
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers ℚ) := fun h =>
    hp ((natCast_mem_maximalIdeal_iff v _).mp ((Ideal.IsPrime.mem_of_pow_mem inferInstance 6 h)))
  have hmin : IsMinimal (v.adicCompletionIntegers ℚ) (cdLocal v d) := by
    rw [← cdModel_baseChange]
    apply isMinimal_baseChange_of_notMem
    rw [cdModel_Δ]
    exact fun h => hm (Ideal.pow_le_self (by norm_num) h)
  refine (hasGoodReduction_iff _ _).mpr ⟨hmin, ?_⟩
  rw [cdLocal_Δ_eq, valuation_of_algebraMap, intValuation_eq_one_iff]
  exact hm

/-- Additive reduction at `v ∣ 2d`. -/
theorem hasAdditiveReduction_cdLocal {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (hp : natGenerator v ∣ 2 * d) :
    HasAdditiveReduction (v.adicCompletionIntegers ℚ) (cdLocal v d) := by
  refine (hasAdditiveReduction_iff _ _).mpr ⟨isMinimal_cdLocal v hd hsq, ?_, ?_⟩
  · rw [cdLocal_Δ_eq, valuation_of_algebraMap, intValuation_lt_one_iff_mem]
    exact Ideal.pow_mem_of_mem _ ((natCast_mem_maximalIdeal_iff v _).mpr hp) 6 (by norm_num)
  · rw [cdLocal_c₄_eq, valuation_of_algebraMap, intValuation_lt_one_iff_mem]
    exact (natCast_mem_maximalIdeal_iff v _).mpr (hp.trans ⟨24 * d, by ring⟩)

theorem reduction_cdLocal (d : ℕ) [IsMinimal (v.adicCompletionIntegers ℚ) (cdLocal v d)] :
    (cdLocal v d).reduction (v.adicCompletionIntegers ℚ) =
      cdModel (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) d := by
  have hI : integralModel (v.adicCompletionIntegers ℚ) (cdLocal v d) =
      cdModel (v.adicCompletionIntegers ℚ) d := by
    apply WeierstrassCurve.map_injective (IsFractionRing.injective _ (v.adicCompletion ℚ))
    change (integralModel _ (cdLocal v d))⁄(v.adicCompletion ℚ) = (cdModel _ d)⁄_
    rw [baseChange_integralModel_eq, cdModel_baseChange]
  rw [reduction, hI, cdModel_map]

theorem natCard_point_reduction_cdLocal {d : ℕ} (hp : ¬ natGenerator v ∣ 2 * d)
    [IsMinimal (v.adicCompletionIntegers ℚ) (cdLocal v d)] :
    Nat.card ((cdLocal v d).reduction (v.adicCompletionIntegers ℚ)).toAffine.Point =
      Nat.card (shortCurve (-(d : ZMod (natGenerator v)) ^ 2)).toAffine.Point := by
  rw [reduction_cdLocal]
  have hE : (cdModel (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) d).IsElliptic := by
    refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
    rw [cdModel_Δ, ← map_natCast (IsLocalRing.residue _), ← map_pow, Ne,
      IsLocalRing.residue_eq_zero_iff]
    exact fun h => hp ((natCast_mem_maximalIdeal_iff v _).mp
      ((Ideal.IsPrime.mem_of_pow_mem inferInstance 6 h)))
  rw [← natCard_point_map_ringEquiv _ (residueEquiv v), cdModel_map, cdModel_eq_shortCurve]

open Polynomial in
/-- **The local polynomial of `C_d` at a good place** `v ∤ 2d`, `p = natGenerator v`:
`1 − a_p T + p T²` with `a_p = p + 1 − #C_d(𝔽_p)`. -/
theorem localPolynomial_cdLocal_of_not_dvd {d : ℕ} (hp : ¬ natGenerator v ∣ 2 * d) :
    (cdLocal v d).localPolynomial (v.adicCompletionIntegers ℚ) =
      1 - C ((natGenerator v : ℤ) + 1 -
        Nat.card (shortCurve (-(d : ZMod (natGenerator v)) ^ 2)).toAffine.Point) * X +
      C (natGenerator v : ℤ) * X ^ 2 := by
  have := hasGoodReduction_cdLocal v hp
  rw [localPolynomial_of_hasGoodReduction, natCard_residueField,
    natCard_point_reduction_cdLocal v hp]

/-- **The local polynomial of `C_d` at a bad place** `v ∣ 2d` is `1` (additive reduction). -/
theorem localPolynomial_cdLocal_of_dvd {d : ℕ} (hd : Odd d) (hsq : Squarefree d)
    (hp : natGenerator v ∣ 2 * d) :
    (cdLocal v d).localPolynomial (v.adicCompletionIntegers ℚ) = 1 := by
  have := hasAdditiveReduction_cdLocal v hd hsq hp
  exact localPolynomial_of_hasAdditiveReduction _ (cdLocal_Δ_ne_zero v (by rintro rfl; simp at hd))

end Completion

section Coefficients

open ArithmeticFunction

theorem mul_apply_prime {f g : ArithmeticFunction ℤ} {p : ℕ} (hp : p.Prime) :
    (f * g) p = f p * g 1 + f 1 * g p := by
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun i j => f i * g j), hp.divisors,
    Finset.sum_pair hp.one_lt.ne, Nat.div_one, Nat.div_self hp.pos]
  ring

theorem prod_apply_one {ι : Type*} (f : ι → ArithmeticFunction ℤ) (hf : ∀ i, f i 1 = 1)
    (s : Finset ι) : (∏ i ∈ s, f i) 1 = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, mul_apply_one, hf, ih, one_mul]

theorem prod_apply_prime {ι : Type*} (f : ι → ArithmeticFunction ℤ) (hf : ∀ i, f i 1 = 1)
    (s : Finset ι) {p : ℕ} (hp : p.Prime) : (∏ i ∈ s, f i) p = ∑ i ∈ s, f i p := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [one_apply_ne hp.one_lt.ne']
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, mul_apply_prime hp, ih, hf,
      prod_apply_one f hf, mul_one, one_mul]

theorem coeff_one_invOfUnit (P : Polynomial ℤ) (hP : P.coeff 0 = 1) :
    PowerSeries.coeff 1 (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) = -P.coeff 1 := by
  have h0 : PowerSeries.constantCoeff (P : PowerSeries ℤ) = ((1 : ℤˣ) : ℤ) := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, Polynomial.coeff_coe, hP]; rfl
  have h := congrArg (PowerSeries.coeff 1) (PowerSeries.mul_invOfUnit _ _ h0)
  rw [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] at h
  simp only [Finset.Nat.antidiagonal_zero, Finset.map_singleton, Finset.sum_cons,
    Finset.sum_singleton, Polynomial.coeff_coe, hP, PowerSeries.coeff_one] at h
  have hc : PowerSeries.coeff 0 (PowerSeries.invOfUnit (P : PowerSeries ℤ) 1) = 1 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_invOfUnit]
    simp
  simp [hc] at h
  linarith

end Coefficients

section LFunction

open ArithmeticFunction Rat.HeightOneSpectrum

theorem natGenerator_injective :
    Function.Injective (natGenerator : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) → ℕ) :=
  fun _ _ h => primesEquiv.injective (Subtype.ext h)

instance northcott_natCard_residueField :
    Northcott (fun v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
      Nat.card (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ))) := by
  refine ⟨fun b => ?_⟩
  simp only [natCard_residueField]
  exact Set.Finite.preimage natGenerator_injective.injOn (Set.finite_Iic b)

/-- The Euler polynomial of `C_d` at `p`: `1 − a_p T + p T²` with `a_p = p + 1 − #C_d(𝔽_p)` if
`p ∤ 2d`, and `1` if `p ∣ 2d`. -/
noncomputable def cdEulerPoly (d p : ℕ) : Polynomial ℤ :=
  if p ∣ 2 * d then 1
  else 1 - Polynomial.C ((p : ℤ) + 1 - Nat.card (cdModel (ZMod p) d).toAffine.Point) *
    Polynomial.X + Polynomial.C (p : ℤ) * Polynomial.X ^ 2

theorem cdEulerPoly_coeff_zero (d p : ℕ) : (cdEulerPoly d p).coeff 0 = 1 := by
  unfold cdEulerPoly; split_ifs <;> simp

theorem localPolynomial_cdLocal_eq (v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    {d : ℕ} (hd : Odd d) (hsq : Squarefree d) :
    (cdLocal v d).localPolynomial (v.adicCompletionIntegers ℚ) =
      cdEulerPoly d (natGenerator v) := by
  unfold cdEulerPoly
  split_ifs with h
  · exact localPolynomial_cdLocal_of_dvd v hd hsq h
  · exact localPolynomial_cdLocal_of_not_dvd v h

theorem mul_apply_of_vanish {f g : ArithmeticFunction ℤ} {n : ℕ} (hf1 : f 1 = 1)
    (hf : ∀ m, m ∣ n → m ≠ 1 → f m = 0) : (f * g) n = g n := by
  rw [mul_apply, Finset.sum_eq_single (1, n)]
  · simp [hf1]
  · rintro ⟨a, b⟩ hab hne
    have h := Nat.mem_divisorsAntidiagonal.mp hab
    by_cases ha : a = 1
    · subst ha; simp only [one_mul] at h; exact absurd (by rw [h.1]) hne
    · rw [hf a ⟨b, h.1.symm⟩ ha, zero_mul]
  · intro h
    have hn : n = 0 := by
      by_contra hn; exact h (Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, hn⟩)
    simp [hn]

theorem prod_vanish {ι : Type*} (f : ι → ArithmeticFunction ℤ) (n : ℕ) (s : Finset ι)
    (hf : ∀ i ∈ s, f i 1 = 1 ∧ ∀ m, m ∣ n → m ≠ 1 → f i m = 0) :
    (∏ i ∈ s, f i) 1 = 1 ∧ ∀ m, m ∣ n → m ≠ 1 → (∏ i ∈ s, f i) m = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨by simp, fun m _ hm => by simp [one_apply_ne hm]⟩
  | insert a s ha ih =>
    have ih' := ih fun i hi => hf i (Finset.mem_insert_of_mem hi)
    have hfa := hf a (Finset.mem_insert_self a s)
    rw [Finset.prod_insert ha]
    refine ⟨by rw [mul_apply_one, hfa.1, ih'.1, one_mul], fun m hm hm1 => ?_⟩
    rw [mul_apply_of_vanish hfa.1 fun m' hm' hm'1 => hfa.2 m' (hm'.trans hm) hm'1]
    exact ih'.2 m hm hm1

theorem exists_natGenerator_eq (p : ℕ) [hp : Fact p.Prime] :
    ∃ v : HeightOneSpectrum (NumberField.RingOfIntegers ℚ), natGenerator v = p :=
  ⟨primesEquiv.symm ⟨p, hp.out⟩, congrArg Subtype.val (primesEquiv.apply_symm_apply ⟨p, hp.out⟩)⟩

/-- **The Dirichlet coefficient of `L(C_d, s)` at a prime power `p ^ k`**, for odd squarefree
`d`: the coefficient of `T ^ k` in `1 / cdEulerPoly d p`. -/
theorem LFunction_cd_apply_prime_pow {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (p : ℕ)
    [hp' : Fact p.Prime] (k : ℕ) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction (p ^ k) =
      PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) := by
  classical
  have hp := hp'.out
  obtain ⟨v, rfl⟩ := exists_natGenerator_eq p
  set q := fun w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    Nat.card (IsLocalRing.ResidueField (w.adicCompletionIntegers ℚ)) with hq_def
  set F := fun w : HeightOneSpectrum (NumberField.RingOfIntegers ℚ) =>
    (cdLocal w d).localPowerSeries (w.adicCompletionIntegers ℚ) with hF_def
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
  rw [localPolynomial_cdLocal_eq v hd hsq]

/-- **The Dirichlet coefficient of `L(C_d, s)` at a prime `p`**, for odd squarefree `d`:
`a_p = p + 1 − #C_d(𝔽_p)` (point at infinity included) if `p ∤ 2d`, and `0` if `p ∣ 2d`. -/
theorem LFunction_cd_apply_prime {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (p : ℕ)
    [Fact p.Prime] :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      if p ∣ 2 * d then 0
      else (p : ℤ) + 1 - Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point := by
  have h := LFunction_cd_apply_prime_pow hd hsq p 1
  rw [pow_one] at h
  rw [h, coeff_one_invOfUnit _ (cdEulerPoly_coeff_zero d p), ← cdModel_eq_shortCurve]
  unfold cdEulerPoly
  split_ifs <;> simp [Polynomial.coeff_one, Polynomial.coeff_X_pow]

/-- Mathlib's L-function of an elliptic curve over `ℚ` is multiplicative. -/
theorem isMultiplicative_LFunction (W : WeierstrassCurve ℚ) : W.LFunction.IsMultiplicative :=
  isMultiplicative_eulerProduct _ fun v =>
    isMultiplicative_ofPowerSeries_of_isPrimePow _
      (by rw [natCard_residueField]; exact (prime_natGenerator v).isPrimePow) _
      (by simp [localPowerSeries, PowerSeries.constantCoeff_invOfUnit])

/-- **`L(C_d, s)` in full**, for odd squarefree `d`: the coefficient at `n ≠ 0` is
`∏_{p^k ∥ n} [T^k] (1 / cdEulerPoly d p)`. So Mathlib's `L(C_d, s)` is the Euler product
`∏_{p ∤ 2d} (1 − a_p p^{−s} + p^{1−2s})^{−1}` with `a_p = p + 1 − #C_d(𝔽_p)`. -/
theorem LFunction_cd_apply {d : ℕ} (hd : Odd d) (hsq : Squarefree d) {n : ℕ} (hn : n ≠ 0) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction n = n.factorization.prod fun p k =>
      PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1) := by
  rw [(isMultiplicative_LFunction _).multiplicative_factorization _ hn]
  refine Finsupp.prod_congr fun p hp => ?_
  have : Fact p.Prime := ⟨Nat.prime_of_mem_primeFactors (Nat.support_factorization n ▸ hp)⟩
  exact LFunction_cd_apply_prime_pow hd hsq p _

/-- `#C_d(𝔽_p)` is the number of affine solutions plus one, for `p ∤ 2d`. -/
theorem natCard_point_shortCurve_zmod {d : ℕ} (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 2 * d) :
    Nat.card (shortCurve (-(d : ZMod p) ^ 2)).toAffine.Point =
      Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} + 1 := by
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : p ∣ 2 := by exact_mod_cast (ZMod.natCast_eq_zero_iff 2 p).mp (by exact_mod_cast h)
    exact hp (this.trans (dvd_mul_right 2 d))
  have hd : (d : ZMod p) ≠ 0 := by
    intro h
    exact hp (((ZMod.natCast_eq_zero_iff d p).mp h).trans (dvd_mul_left d 2))
  have : NeZero (2 : ZMod p) := ⟨h2⟩
  have hE := shortCurve_isElliptic (F := ZMod p) (neg_ne_zero.mpr (pow_ne_zero 2 hd))
  rw [Nat.card_congr (pointEquivOption _), Finite.card_option]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight fun xy => by
    rw [shortCurve_equation_iff]; ring_nf)

/-- **`a_p(C_d)` as a point count**: for odd squarefree `d` and a prime `p ∤ 2d`, the Dirichlet
coefficient of `L(C_d, s)` at `p` is `p − #{(x, y) ∈ 𝔽_p² : y² = x³ − d² x}`. -/
theorem LFunction_cd_apply_prime_eq_sub_card {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (p : ℕ)
    [Fact p.Prime] (hp : ¬ p ∣ 2 * d) :
    (shortCurve (-(d : ℚ) ^ 2)).LFunction p =
      p - Nat.card {xy : ZMod p × ZMod p // xy.2 ^ 2 = xy.1 ^ 3 - (d : ZMod p) ^ 2 * xy.1} := by
  rw [LFunction_cd_apply_prime hd hsq p]
  simp only [hp, ↓reduceIte]
  rw [natCard_point_shortCurve_zmod p hp]
  push_cast; ring

/-- **Bad primes**: for odd squarefree `d` and a prime `p ∣ 2d`, the coefficient is `0`. -/
theorem LFunction_cd_apply_prime_of_dvd {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (p : ℕ)
    [Fact p.Prime] (hp : p ∣ 2 * d) : (shortCurve (-(d : ℚ) ^ 2)).LFunction p = 0 := by
  rw [LFunction_cd_apply_prime hd hsq p]
  simp only [hp, ↓reduceIte]

/-- The Dirichlet coefficients of `L(C_d, s)`, from the Euler polynomials `cdEulerPoly d p`. -/
noncomputable def cdCoeff (d n : ℕ) : ℤ :=
  if n = 0 then 0 else n.factorization.prod fun p k =>
    PowerSeries.coeff k (PowerSeries.invOfUnit (cdEulerPoly d p : PowerSeries ℤ) 1)

/-- **Mathlib's `L(C_d, s)` is the standard Euler product** (odd squarefree `d`): the L-series in
the CR₃ literature Props equals the Dirichlet series of `cdCoeff d`. -/
theorem LSeries_cd_eq {d : ℕ} (hd : Odd d) (hsq : Squarefree d) (s : ℂ) :
    (shortCurve (-(d : ℚ) ^ 2)).LSeries s = LSeries (fun n => (cdCoeff d n : ℂ)) s := by
  refine LSeries_congr (fun {n} hn => ?_) s
  simp only [Function.comp_apply, cdCoeff, hn, ↓reduceIte, LFunction_cd_apply hd hsq hn]

/-- The case of the CR₃ Props: squarefree `d ≡ 5 (mod 8)`. -/
theorem LSeries_cd_eq_of_mod_eight {d : ℕ} (hd : d % 8 = 5) (hsq : Squarefree d) (s : ℂ) :
    (shortCurve (-(d : ℚ) ^ 2)).LSeries s = LSeries (fun n => (cdCoeff d n : ℂ)) s :=
  LSeries_cd_eq (Nat.odd_iff.mpr (by omega)) hsq s

end LFunction

end ZInQ.Literature
