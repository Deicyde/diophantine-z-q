import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.RationalResidues
import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.TraceSelector
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Place.Extension.Degree

/-!
# Canonical normalization of the Kähler–Weil comparison

Residual trace selectors isolate one place of a finite fiber. The rational
logarithmic residue calculation and the local logarithmic order rule determine
the uniformizer residue, hence remove the separating-parameter choice.

Locators: Stichtenoth, *Algebraic Function Fields and Codes*, second edition,
Sections I.7 and III.4; Silverman, *The Arithmetic of Elliptic Curves*, II, §§4–5.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs.CanonicalResidues

open Module TauCeti Polynomial KaehlerDifferential TauCeti.AlgebraicGeometry
open scoped IntermediateField WithZero

/-- THEOREM. The rational divisor -2 at infinity is canonical.
Locator: Stichtenoth I.5 and the normalization in `RegularComparison.lean`. -/
private theorem rational_canonical (k : Type*) [Field k] :
    (Place.orderSystem (IsFunctionField.ratFunc k)).divisorClass
        ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) =
      canonicalClass (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc := by
  rw [divisorClass_eq_canonicalClass_iff, genus_ratFunc]
  refine ⟨?_, Nat.zero_le _⟩
  rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infty]
  norm_num

/-- THEOREM. The normalized rational differential exists with its prescribed
canonical divisor and value -1 on X inverse at infinity.
Locator: the rational normalization in `RegularComparison.lean`; Stichtenoth I.7. -/
private theorem exists_normalized_rational (k : Type*) [Field k] :
    ∃ ω : Module.Dual k ↥(repartitionSpace k (RatFunc k)),
      ω ∈ weilDifferentialSpace k (RatFunc k) ∧
      IsGreatest {D : Divisor k (RatFunc k) | ω ∈ weilDifferentialFiltration D}
        ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) ∧
      repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1 := by
  obtain ⟨ω, hmem, hω0, hgreat⟩ := exists_isGreatest_of_divisorClass_eq_canonicalClass
    (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc (rational_canonical k)
  have hord : weilDifferentialOrder (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
      hmem hω0 (Place.infty k) = -2 := by
    rw [← coeff_weilDifferentialDivisor,
      (isGreatest_weilDifferentialDivisor _ _ hmem hω0).unique hgreat,
      WeilDivisor.coeff_zsmul, WeilDivisor.coeff_ofPoint_self, mul_one]
  have hne := repartitionDualComponent_uniformizer_zpow_ne_zero (IsFunctionField.ratFunc k)
    isIntegrallyClosedIn_ratFunc hmem hω0 (Place.degree_infty k) Place.isUniformizer_infty
  rw [hord] at hne
  norm_num only [zpow_one] at hne
  set v := repartitionDualComponent ω (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ with hv
  refine ⟨repartitionDualMul (IsFunctionField.ratFunc k) (algebraMap k (RatFunc k) (-v⁻¹)) ω,
    repartitionDualMul_mem_weilDifferentialSpace _ _ hmem, ?_, ?_⟩
  · have hc0 : algebraMap k (RatFunc k) (-v⁻¹) ≠ 0 := by
      simpa using inv_ne_zero hne
    obtain ⟨z, hz⟩ : ∃ z : (RatFunc k)ˣ, (z : RatFunc k) = algebraMap k (RatFunc k) (-v⁻¹) :=
      ⟨Units.mk0 _ hc0, rfl⟩
    have hprincipal : Divisor.principal (IsFunctionField.ratFunc k) z = 0 :=
      Divisor.principal_eq_zero_of_isAlgebraic _ (hz ▸ isAlgebraic_algebraMap _)
    have hgreat' := isGreatest_weilDifferentialDivisor (IsFunctionField.ratFunc k)
      isIntegrallyClosedIn_ratFunc
      (repartitionDualMul_mem_weilDifferentialSpace (IsFunctionField.ratFunc k) (z : RatFunc k)
        hmem)
      (repartitionDualMul_ne_zero (IsFunctionField.ratFunc k) (Units.ne_zero z) hω0)
    rw [weilDifferentialDivisor_repartitionDualMul _ _ hmem hω0 z, hprincipal, zero_add,
      (isGreatest_weilDifferentialDivisor _ _ hmem hω0).unique hgreat, hz] at hgreat'
    exact hgreat'
  · rw [repartitionDualComponent_repartitionDualMul_algebraMap, ← hv, smul_eq_mul, neg_mul,
      inv_mul_cancel₀ hne]

/-- DEFINITION. The same normalized rational source used by the separating
comparison. Locator: the preceding existence theorem and `RegularComparison.lean`. -/
private def rationalForm (k : Type*) [Field k] :
    Module.Dual k ↥(repartitionSpace k (RatFunc k)) := (exists_normalized_rational k).choose

/-- THEOREM. The rational source is a Weil differential.
Locator: the normalized rational existence theorem. -/
private theorem rationalForm_mem (k : Type*) [Field k] :
    rationalForm k ∈ weilDifferentialSpace k (RatFunc k) :=
  (exists_normalized_rational k).choose_spec.1

/-- THEOREM. The rational source is bounded by -2 at infinity.
Locator: the normalized rational existence theorem. -/
private theorem rationalForm_bound (k : Type*) [Field k] :
    rationalForm k ∈ weilDifferentialFiltration
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) :=
  (exists_normalized_rational k).choose_spec.2.1.1

/-- THEOREM. The rational source has the prescribed normalization at infinity.
Locator: the normalized rational existence theorem. -/
private theorem rationalForm_normalization (k : Type*) [Field k] :
    repartitionDualComponent (rationalForm k) (Place.infty k) (RatFunc.X : RatFunc k)⁻¹ = -1 :=
  (exists_normalized_rational k).choose_spec.2.2

/-- THEOREM. The separating differential is literally the cotrace of this
normalized rational source, with no change of scalar.
Locator: `AbelianCurveInputs.differentialOfSeparating`, by definitional equality. -/
theorem differentialOfSeparating_eq_cotrace {k F : Type} [Field k] [Field F] [Algebra k F]
    (hF : IsFunctionField k F) {x : F} (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] :
    letI := ratFuncAlgebraOfTranscendental hx
    letI := isScalarTower_ratFuncAlgebraOfTranscendental hx
    letI := isFunctionField_iff_functionField.mp hF
    letI := isSeparable_ratFuncAlgebraOfTranscendental hx
    differentialOfSeparating hF hx = weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
      ⟨rationalForm k, rationalForm_mem k⟩ := by
  rfl

/-- THEOREM. Separating differentiation commutes with the specified rational
function embedding. Locator: `Derivation.apply_eq_derivativeOfSeparating_smul`
and the image X = x. -/
theorem derivative_rational_algebraMap {k F : Type} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) {x : F} (hx : Transcendental k x) (r : RatFunc k) :
    letI := hF.finiteDimensional_adjoin hx
    letI := ratFuncAlgebraOfTranscendental hx
    letI := isScalarTower_ratFuncAlgebraOfTranscendental hx
    letI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin
      (RatFunc.transcendental_X (K := k))
    derivativeOfSeparating hx (algebraMap (RatFunc k) F r) =
      algebraMap (RatFunc k) F (derivativeOfSeparating (RatFunc.transcendental_X (K := k)) r) := by
  haveI := hF.finiteDimensional_adjoin hx
  letI := ratFuncAlgebraOfTranscendental hx
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hx
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin (RatFunc.transcendental_X (K := k))
  let d := derivativeOfSeparating hx
  let dR := derivativeOfSeparating (RatFunc.transcendental_X (K := k))
  have h := (d.compAlgebraMap (RatFunc k)).apply_eq_derivativeOfSeparating_smul
    (RatFunc.transcendental_X (K := k)) r
  change d (algebraMap (RatFunc k) F r) =
    dR r • d (algebraMap (RatFunc k) F RatFunc.X) at h
  rw [algebraMap_ratFuncAlgebraOfTranscendental_X hx] at h
  have hd : d x = 1 := derivativeOfSeparating_self hx
  simpa only [hd, Algebra.smul_def, mul_one] using h

/-- THEOREM. The actual comparison has logarithmic uniformizer residue equal
to the place degree. Locator: Stichtenoth I.7 and III.4; the rational residue
calculation, residual trace selector, and local logarithmic order rule. -/
theorem uniformizer_logarithmic_normalization {k F : Type} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {x : F} (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (P : Place k F) {t : F} (ht : P.valuation.IsUniformizer t) :
    letI := weilDifferentialSpaceModule hF
    repartitionDualComponent (comparison hF hex hx (D k F t) :
      Module.Dual k ↥(repartitionSpace k F)) P t⁻¹ = (P.degree : k) := by
  haveI := hF.finiteDimensional_adjoin hx
  letI := ratFuncAlgebraOfTranscendental hx
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hx
  haveI := isFunctionField_iff_functionField.mp hF
  haveI := isSeparable_ratFuncAlgebraOfTranscendental hx
  haveI := (IsFunctionField.ratFunc k).finiteDimensional_adjoin (RatFunc.transcendental_X (K := k))
  letI := weilDifferentialSpaceModule hF
  let Q := P.restrict k (RatFunc k)
  let w : ↥(weilDifferentialSpace k (RatFunc k)) := ⟨rationalForm k, rationalForm_mem k⟩
  let ω := weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF w
  obtain ⟨r, hr, hkill, hres⟩ := RationalResidues.exists_uniformizer_residue_data
    (rationalForm k) (rationalForm_bound k) (rationalForm_normalization k) Q
  let s : F := algebraMap (RatFunc k) F r
  have hs : s ≠ 0 :=
    (map_ne_zero_iff (algebraMap (RatFunc k) F) (algebraMap (RatFunc k) F).injective).mpr hr.ne_zero
  let dR := derivativeOfSeparating (RatFunc.transcendental_X (K := k))
  let a : RatFunc k := dR r / r
  obtain ⟨b, hbP, hbothers, hbtrace⟩ := TraceSelector.exists_residual_trace_selector
    (F := RatFunc k) P
  have hcoef : derivativeOfSeparating hx s * s⁻¹ = algebraMap (RatFunc k) F a := by
    rw [derivative_rational_algebraMap hF hx, ← div_eq_mul_inv, ← map_div₀]
  have hcomp (P' : Place k F) (z : F) :
      repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P'
        (algebraMap (RatFunc k) F a * z) =
      repartitionDualComponent (comparison hF hex hx (D k F s) :
        Module.Dual k ↥(repartitionSpace k F)) P' (s⁻¹ * z) := by
    rw [← derivativeOfSeparating_smul_D hx s, map_smul,
      coe_weilDifferentialSpaceModule_smul, repartitionDualComponent_repartitionDualMul,
      comparison_D_self]
    have heq : derivativeOfSeparating hx s * (s⁻¹ * z) =
        algebraMap (RatFunc k) F a * z := by rw [← mul_assoc, hcoef]
    rw [heq]
    rfl
  have hPone : repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P
      (algebraMap (RatFunc k) F a * b) =
      repartitionDualComponent (comparison hF hex hx (D k F s) :
        Module.Dual k ↥(repartitionSpace k F)) P s⁻¹ := by
    rw [hcomp]
    have h := ResidueNormalization.logarithmicComparison_kills_maximal hF hex hx P hs hbP
    rw [mul_sub, mul_one, map_sub, sub_eq_zero] at h
    exact h
  have houtside (P' : Place k F) (hQ : P'.restrict k (RatFunc k) = Q) (hne : P' ≠ P) :
      repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P'
        (algebraMap (RatFunc k) F a * b) = 0 := by
    rw [hcomp]
    exact ResidueNormalization.logarithmicComparison_kills_maximal hF hex hx P' hs
      (hbothers P' hQ hne)
  have hsum : (∑ᶠ (P' : Place k F) (_ : P'.restrict k (RatFunc k) = Q),
      repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P'
        (algebraMap (RatFunc k) F a * b)) =
      repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P
        (algebraMap (RatFunc k) F a * b) := by
    rw [finsum_eq_single _ P]
    · simp [Q]
    · intro P' hne
      by_cases hQ : P'.restrict k (RatFunc k) = Q
      · simp [hQ, houtside P' hQ hne]
      · simp [hQ]
  have htrace := trace_finsum_repartitionDualComponent_weilDifferentialCotrace
    (IsFunctionField.ratFunc k) hF w Q (algebraMap (RatFunc k) F a * b)
  rw [Algebra.trace_self_apply, hsum, hPone] at htrace
  have htrcoef : Algebra.trace (RatFunc k) F (algebraMap (RatFunc k) F a * b) =
      a * Algebra.trace (RatFunc k) F b := by
    change Algebra.trace (RatFunc k) F (a • b) = a • Algebra.trace (RatFunc k) F b
    exact map_smul _ _ _
  rw [htrcoef] at htrace
  let n : ℕ := Place.ramificationIdx (RatFunc k) P * Place.relativeDegree k (RatFunc k) P
  have htrres : repartitionDualComponent (rationalForm k) Q
      (a * Algebra.trace (RatFunc k) F b) = (n : k) * (Q.degree : k) := by
    have h := hkill (Algebra.trace (RatFunc k) F b - algebraMap k (RatFunc k) (n : k)) hbtrace
    rw [mul_sub, map_sub, sub_eq_zero] at h
    rw [h, mul_comm a, ← Algebra.smul_def, map_smul, smul_eq_mul]
    exact congrArg (fun c : k => (n : k) * c) hres
  change repartitionDualComponent (comparison hF hex hx (D k F s) :
    Module.Dual k ↥(repartitionSpace k F)) P s⁻¹ =
      repartitionDualComponent (rationalForm k) Q (a * Algebra.trace (RatFunc k) F b) at htrace
  rw [htrres] at htrace
  have hscale := ResidueNormalization.logarithmicResidue_eq_order_mul hF hex hx P ht hs
  have hord : P.ord s = (Place.ramificationIdx (RatFunc k) P : ℤ) := by
    rw [P.ord_algebraMap_restrict k (RatFunc k), Q.isUniformizer_iff_ord_eq_one.mp hr,
      mul_one]
  rw [hord, Int.cast_natCast] at hscale
  rw [htrace] at hscale
  have he0 : (Place.ramificationIdx (RatFunc k) P : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (P.ramificationIdx_pos (RatFunc k)).ne'
  have hdeg : P.degree = Q.degree * Place.relativeDegree k (RatFunc k) P :=
    P.degree_eq_degree_restrict_mul_relativeDegree k (RatFunc k)
  apply mul_left_cancel₀ he0
  rw [← hscale, hdeg]
  dsimp only [n]
  push_cast
  ring

/-- THEOREM. The remaining local logarithmic normalization proposition is closed.
Locator: `uniformizer_logarithmic_normalization` above. -/
theorem localLogarithmicNormalization : LocalFacts.LocalLogarithmicNormalization := by
  intro k F _ _ _ _ hF hex x hx _ P t ht
  exact uniformizer_logarithmic_normalization hF hex hx P ht

/-- THEOREM. The normalized separating cotraces obey the parameter chain rule.
Locator: the proved local logarithmic normalization and
`LocalFacts.separatingCotraceChainRule_of_logarithmicNormalization`. -/
theorem separatingCotraceChainRule : SeparatingCotraceChainRule :=
  LocalFacts.separatingCotraceChainRule_of_logarithmicNormalization localLogarithmicNormalization

/-- THEOREM. The actual generic-restriction comparison is injective, has the
exact holomorphic image, is parameter independent, and is natural for curve
isomorphisms. Locator: `regularDifferentialComparisonCanonical_of_local_inputs`
and the three closed local facts. -/
theorem regularDifferentialComparisonCanonical : RegularDifferentialComparisonCanonical :=
  regularDifferentialComparisonCanonical_of_local_inputs LocalFacts.localUniformizerBasis
    LocalFacts.uniformizerResidueOrder separatingCotraceChainRule

/-- THEOREM. The comparison commutes with an actual field isomorphism with
arbitrary separating parameters on both sides. No transported-parameter choice
remains in the square. Locator: the closed chain rule and
`comparison_fieldTransport`. -/
theorem comparison_fieldTransport_parameter_free {k F F' : Type}
    [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F'] [CharZero k]
    (σ : F ≃ₐ[k] F') (hF : IsFunctionField k F) (hF' : IsFunctionField k F')
    (hex : IsIntegrallyClosedIn k F) (hex' : IsIntegrallyClosedIn k F')
    {x : F} {y : F'} (hx : Transcendental k x) (hy : Transcendental k y)
    (η : KaehlerDifferential k F) :
    letI := hF.finiteDimensional_adjoin hx
    letI := hF'.finiteDimensional_adjoin hy
    letI := weilDifferentialSpaceModule hF
    letI := weilDifferentialSpaceModule hF'
    comparison hF' hex' hy (kaehlerFieldTransport σ η) =
      weilFieldTransport σ hF hF' (comparison hF hex hx η) := by
  have hx' : Transcendental k (σ x) := hx.algHom σ σ.injective
  haveI := hF.finiteDimensional_adjoin hx
  haveI := hF'.finiteDimensional_adjoin hx'
  haveI := hF'.finiteDimensional_adjoin hy
  letI := weilDifferentialSpaceModule hF
  letI := weilDifferentialSpaceModule hF'
  have heq := comparison_parameter_independent separatingCotraceChainRule
    k F' hF' hex' y (σ x) hy hx'
  rw [heq]
  exact (comparison_fieldTransport σ hF hF' hex hex' hx η).symm

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs.CanonicalResidues
