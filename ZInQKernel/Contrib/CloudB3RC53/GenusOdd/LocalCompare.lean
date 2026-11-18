import ZInQKernel.Contrib.OneProof.RC.TwistDictionary.Invariance

/-!
# GenusOdd: comparing Mathlib's local polynomials through the reductions (PROVED)

For a minimal Weierstrass equation over the fraction field of a DVR, the reduction type is read off
the reduction: good iff `Δ̃ ≠ 0`, multiplicative iff `Δ̃ = 0 ≠ c̃₄`, split iff moreover `splitPoly`
of the reduction splits. Hence (`localPolynomial_eq_of_reduction_map`) two minimal equations over
two DVRs whose reductions correspond under a ring isomorphism of the residue fields have the same
local polynomial; and (`reduction_map_eq_of_rat`) the reductions of one Weierstrass curve with
rational coefficients, minimal over both, correspond under any isomorphism of residue fields of the
same prime characteristic.
-/

namespace ZInQ.Contrib.CloudB3RC53.GenusOdd

open WeierstrassCurve IsLocalRing Polynomial

section Generic

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

omit [IsDomain R] [IsDiscreteValuationRing R] [IsFractionRing R F] in
variable (R) in
/-- `c₄` of the integral model (PROVED). -/
theorem algebraMap_integralModel_c₄ (W : WeierstrassCurve F) [IsIntegral R W] :
    algebraMap R F (integralModel R W).c₄ = W.c₄ := by
  conv_rhs => rw [← baseChange_integralModel_eq R W]
  simp [baseChange]

/-- **Good reduction through the reduction** (PROVED). -/
theorem hasGoodReduction_iff_reduction_Δ (W : WeierstrassCurve F) [IsMinimal R W] :
    W.HasGoodReduction R ↔ (W.reduction R).Δ ≠ 0 :=
  (hasGoodReduction_iff_isElliptic_reduction R).trans
    ((W.reduction R).isElliptic_iff.trans isUnit_iff_ne_zero)

/-- **Multiplicative reduction through the reduction** (PROVED). -/
theorem hasMultiplicativeReduction_iff_reduction (W : WeierstrassCurve F) [hW : IsMinimal R W] :
    W.HasMultiplicativeReduction R ↔ (W.reduction R).Δ = 0 ∧ (W.reduction R).c₄ ≠ 0 := by
  have h1 : ∀ r : R, IsDedekindDomain.HeightOneSpectrum.valuation F
      (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R F r) < 1 ↔ r ∈ maximalIdeal R :=
    fun r => IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem _ r
  have h2 : ∀ r : R, IsDedekindDomain.HeightOneSpectrum.valuation F
      (IsDiscreteValuationRing.maximalIdeal R) (algebraMap R F r) = 1 ↔ r ∉ maximalIdeal R := by
    intro r
    rw [← h1, not_lt]
    exact (IsDedekindDomain.HeightOneSpectrum.valuation_le_one (R := R) (K := F) _ _).ge_iff_eq.symm
  rw [hasMultiplicativeReduction_iff, ← integralModel_Δ_eq R W, ← algebraMap_integralModel_c₄ R W,
    h1, h2]
  simp only [reduction, map_Δ, map_c₄, residue_eq_zero_iff, ne_eq, hW, true_and]

end Generic

section Compare

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  {R' : Type*} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
  {F' : Type*} [Field F'] [Algebra R' F'] [IsFractionRing R' F']

open scoped Classical in
/-- **Local polynomials agree when the reductions correspond** (PROVED): if `W` (over `F`) and
`W'` (over `F'`) are minimal and `W̃' = ψ(W̃)` for a ring isomorphism `ψ` of the residue fields,
then `W.localPolynomial R = W'.localPolynomial R'`. -/
theorem localPolynomial_eq_of_reduction_map (W : WeierstrassCurve F) (W' : WeierstrassCurve F')
    (hΔ : W.Δ ≠ 0) (hΔ' : W'.Δ ≠ 0) [IsMinimal R W] [IsMinimal R' W']
    (ψ : ResidueField R ≃+* ResidueField R')
    (hψ : W'.reduction R' = (W.reduction R).map (ψ : ResidueField R →+* ResidueField R')) :
    W.localPolynomial R = W'.localPolynomial R' := by
  rw [ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_of_isMinimal W hΔ,
    ZInQ.Manuscript.RC.TwistDictionary.localPolynomial_of_isMinimal W' hΔ']
  have hcard : Nat.card (ResidueField R) = Nat.card (ResidueField R') := Nat.card_congr ψ.toEquiv
  have hΔr : (W'.reduction R').Δ = ψ (W.reduction R).Δ := by rw [hψ, map_Δ]; rfl
  have hcr : (W'.reduction R').c₄ = ψ (W.reduction R).c₄ := by rw [hψ, map_c₄]; rfl
  have hgood : W'.HasGoodReduction R' ↔ W.HasGoodReduction R := by
    rw [hasGoodReduction_iff_reduction_Δ, hasGoodReduction_iff_reduction_Δ, hΔr,
      map_ne_zero_iff _ ψ.injective]
  have hmult : W'.HasMultiplicativeReduction R' ↔ W.HasMultiplicativeReduction R := by
    rw [hasMultiplicativeReduction_iff_reduction, hasMultiplicativeReduction_iff_reduction, hΔr, hcr,
      map_eq_zero_iff _ ψ.injective, map_ne_zero_iff _ ψ.injective]
  have hsplitpoly : ZInQ.Manuscript.RC.TwistDictionary.splitPoly (W'.reduction R') =
      (ZInQ.Manuscript.RC.TwistDictionary.splitPoly (W.reduction R)).map
        (ψ : ResidueField R →+* ResidueField R') := by
    rw [hψ, ZInQ.Manuscript.RC.TwistDictionary.splitPoly_map]
  have hsplits : Splits (ZInQ.Manuscript.RC.TwistDictionary.splitPoly (W'.reduction R')) ↔
      Splits (ZInQ.Manuscript.RC.TwistDictionary.splitPoly (W.reduction R)) := by
    rw [hsplitpoly]
    constructor
    · intro h
      have := h.map (ψ.symm : ResidueField R' →+* ResidueField R)
      rwa [Polynomial.map_map, show ((ψ.symm : ResidueField R' →+* ResidueField R).comp
        (ψ : ResidueField R →+* ResidueField R')) = RingHom.id _ by ext; simp,
        Polynomial.map_id] at this
    · intro h
      exact h.map _
  have hsplit : W'.HasSplitMultiplicativeReduction R' ↔ W.HasSplitMultiplicativeReduction R := by
    rw [ZInQ.Manuscript.RC.TwistDictionary.hasSplitMultiplicativeReduction_iff,
      ZInQ.Manuscript.RC.TwistDictionary.hasSplitMultiplicativeReduction_iff, hmult, hsplits]
  by_cases hg : W.HasGoodReduction R
  · have hg' : W'.HasGoodReduction R' := hgood.mpr hg
    rw [if_pos hg, if_pos hg', hcard]
    have : (W.reduction R).IsElliptic := (hasGoodReduction_iff_isElliptic_reduction R).mp hg
    have hpts : Nat.card (W'.reduction R').toAffine.Point = Nat.card (W.reduction R).toAffine.Point := by
      rw [hψ]
      exact ZInQ.Literature.natCard_point_map_ringEquiv _ ψ
    rw [hpts]
  · rw [if_neg hg, if_neg (mt hgood.mp hg)]
    by_cases hs : W.HasSplitMultiplicativeReduction R
    · rw [if_pos hs, if_pos (hsplit.mpr hs)]
    · rw [if_neg hs, if_neg (mt hsplit.mp hs)]
      by_cases hm : W.HasMultiplicativeReduction R
      · rw [if_pos hm, if_pos (hmult.mpr hm)]
      · rw [if_neg hm, if_neg (mt hmult.mp hm)]

end Compare

section Rat

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]

/-- The residue of an integral lift of a rational number `x`: `r̃ · den = num` (PROVED). -/
theorem residue_mul_den {ι : ℚ →+* F} {x : ℚ} {r : R} (hr : algebraMap R F r = ι x) :
    residue R r * (x.den : ResidueField R) = (x.num : ResidueField R) := by
  have h : r * (x.den : R) = (x.num : R) := by
    apply IsFractionRing.injective R F
    rw [map_mul, hr, map_natCast, map_intCast, ← map_natCast ι, ← map_intCast ι, ← map_mul,
      Rat.mul_den_eq_num]
  have := congrArg (residue R) h
  rwa [map_mul, map_natCast, map_intCast] at this

/-- In a residue field of characteristic `p`, the denominator of an integral rational is a unit
(PROVED). -/
theorem den_ne_zero_of_lift {p : ℕ} [Fact p.Prime] [CharP (ResidueField R) p] {ι : ℚ →+* F}
    {x : ℚ} {r : R} (hr : algebraMap R F r = ι x) : (x.den : ResidueField R) ≠ 0 := by
  intro h0
  have h := residue_mul_den hr
  rw [h0, mul_zero, eq_comm, CharP.intCast_eq_zero_iff (ResidueField R) p] at h
  rw [CharP.cast_eq_zero_iff (ResidueField R) p] at h0
  have hcop := x.reduced
  have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.mp h
  have := Nat.dvd_gcd h1 h0
  rw [hcop] at this
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.mp this)

end Rat

section RatCompare

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  {F : Type*} [Field F] [Algebra R F] [IsFractionRing R F]
  {R' : Type*} [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
  {F' : Type*} [Field F'] [Algebra R' F'] [IsFractionRing R' F']

/-- An isomorphism of residue fields of characteristic `p` identifies the residues of integral lifts
of the same rational number (PROVED). -/
theorem residue_lift_compat {p : ℕ} [Fact p.Prime] [CharP (ResidueField R) p]
    [CharP (ResidueField R') p] (ψ : ResidueField R ≃+* ResidueField R') {ι : ℚ →+* F}
    {ι' : ℚ →+* F'} {x : ℚ} {r : R} {r' : R'} (hr : algebraMap R F r = ι x)
    (hr' : algebraMap R' F' r' = ι' x) : ψ (residue R r) = residue R' r' := by
  have h := residue_mul_den hr
  have h' := residue_mul_den hr'
  have hd := den_ne_zero_of_lift (p := p) hr
  have hd' := den_ne_zero_of_lift (p := p) hr'
  have e1 : residue R r = (x.num : ResidueField R) / (x.den : ResidueField R) := by
    rw [eq_div_iff hd, h]
  have e2 : residue R' r' = (x.num : ResidueField R') / (x.den : ResidueField R') := by
    rw [eq_div_iff hd', h']
  rw [e1, e2, map_div₀, map_intCast, map_natCast]

/-- **The reductions of a rational Weierstrass curve over two DVRs correspond** (PROVED): if
`W₀ : WeierstrassCurve ℚ` is minimal over `R` (through `ι`) and over `R'` (through `ι'`), whose
residue fields have the same prime characteristic `p`, then for every ring isomorphism `ψ` of the
residue fields, the reduction over `R'` is `ψ` of the reduction over `R`. -/
theorem reduction_map_eq_of_rat {p : ℕ} [Fact p.Prime] [CharP (ResidueField R) p]
    [CharP (ResidueField R') p] (ψ : ResidueField R ≃+* ResidueField R') (ι : ℚ →+* F)
    (ι' : ℚ →+* F') (W₀ : WeierstrassCurve ℚ) [IsMinimal R (W₀.map ι)]
    [IsMinimal R' (W₀.map ι')] :
    (W₀.map ι').reduction R' = ((W₀.map ι).reduction R).map (ψ : ResidueField R →+* ResidueField R') := by
  have c := fun {x : ℚ} {r : R} {r' : R'} (hr : algebraMap R F r = ι x)
    (hr' : algebraMap R' F' r' = ι' x) => residue_lift_compat (p := p) ψ hr hr'
  ext
  · exact (c (integralModel_a₁_eq R (W₀.map ι)) (integralModel_a₁_eq R' (W₀.map ι'))).symm
  · exact (c (integralModel_a₂_eq R (W₀.map ι)) (integralModel_a₂_eq R' (W₀.map ι'))).symm
  · exact (c (integralModel_a₃_eq R (W₀.map ι)) (integralModel_a₃_eq R' (W₀.map ι'))).symm
  · exact (c (integralModel_a₄_eq R (W₀.map ι)) (integralModel_a₄_eq R' (W₀.map ι'))).symm
  · exact (c (integralModel_a₆_eq R (W₀.map ι)) (integralModel_a₆_eq R' (W₀.map ι'))).symm

end RatCompare

end ZInQ.Contrib.CloudB3RC53.GenusOdd
