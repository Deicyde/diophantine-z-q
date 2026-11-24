/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.DifferentialLine
import TauCeti.FieldTheory.FunctionField.Differential.Cotrace
import TauCeti.FieldTheory.FunctionField.Differential.LocalOrder
import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc
import TauCeti.FieldTheory.FunctionField.Different.Complementary
import TauCeti.RingTheory.DedekindDomain.Different.Derivative
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.GeneratedByY
import Mathlib.Tactic.LinearCombination

/-!
# The invariant differential has divisor zero

For a nonsingular Weierstrass curve over any field, the Kähler differential
`dx / (2y + a₁x + a₃)` corresponds to a nonzero Weil differential with divisor zero.
Consequently it spans the holomorphic Weil differentials over the constant field.

The comparison is not an arbitrary isomorphism of one-dimensional spaces. It sends `dx`
to the cotrace of the rational-function differential normalized by
`div(dX) = -2[∞]` and `res_∞(X⁻¹ dX) = -1`.

The proof bounds the different by the derivative of the equation for `y` on the affine
chart and by the derivative of the equation for `y/x²` on the other chart. These bounds
make the differential divisor nonpositive; its degree is `2g - 2 = 0`, so it vanishes.

Mathematical locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition,
Proposition III.1.5. No printed theorem is assumed.

The missing comparison and local-bound proofs are adapted from the public Tau Ceti
repository, revision `5a01f5fe3621`, Apache-2.0:
* `FieldTheory/FunctionField/Differential/RatFunc/Basic.lean`;
* `FieldTheory/FunctionField/Differential/Comparison.lean`;
* `FieldTheory/FunctionField/Different/Derivative.lean`;
* `AlgebraicGeometry/EllipticCurve/Affine/FunctionField/Divisor/InvariantDifferential.lean`.
Only the declarations needed here are included. The holomorphic-line corollaries are
proved from the divisor computation and the existing dimension theorem.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace ZInQ.Contrib.RC53Assist.InvariantDifferential

open TauCeti AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField

/-! ## The normalized differential of the rational function field -/

/-- THEOREM (proved). The divisor `-2[∞]` is canonical for the rational function field.
Locator: Tau Ceti, `Differential/RatFunc/Basic.lean`,
`divisorClass_neg_two_zsmul_ofPoint_infty`. -/
private theorem rational_canonical (k : Type*) [Field k] :
    (Place.orderSystem (IsFunctionField.ratFunc k)).divisorClass
        ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) =
      canonicalClass (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc := by
  rw [divisorClass_eq_canonicalClass_iff, genus_ratFunc]
  refine ⟨?_, Nat.zero_le _⟩
  rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infty]
  norm_num

/-- THEOREM (proved). A rational-function Weil differential exists with divisor `-2[∞]`
and local value `-1` on `X⁻¹` at infinity.
Locator: Tau Ceti, `Differential/RatFunc/Basic.lean`,
`exists_isGreatest_ratFuncWeilDifferential`. -/
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

/-- DEFINITION. The normalized rational-function Weil differential `dX`.
Locator: Tau Ceti, `Differential/RatFunc/Basic.lean`, `ratFuncWeilDifferential`. -/
private def rationalDifferential (k : Type*) [Field k] :
    Module.Dual k ↥(repartitionSpace k (RatFunc k)) :=
  (exists_normalized_rational k).choose

/-- THEOREM (proved). The normalized rational differential belongs to the Weil space.
Locator: Tau Ceti, `Differential/RatFunc/Basic.lean`, `ratFuncWeilDifferential_mem`. -/
private theorem rationalDifferential_mem (k : Type*) [Field k] :
    rationalDifferential k ∈ weilDifferentialSpace k (RatFunc k) :=
  (exists_normalized_rational k).choose_spec.1

/-- THEOREM (proved). The divisor `-2[∞]` is the greatest divisor bounding `dX`.
Locator: Tau Ceti, `Differential/RatFunc/Basic.lean`, `isGreatest_ratFuncWeilDifferential`. -/
private theorem rationalDifferential_greatest (k : Type*) [Field k] :
    IsGreatest {D : Divisor k (RatFunc k) |
        rationalDifferential k ∈ weilDifferentialFiltration D}
      ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) :=
  (exists_normalized_rational k).choose_spec.2.1

/-- THEOREM (proved). The local component of `dX` sends `X⁻¹` to `-1` at infinity.
Locator: Tau Ceti, `Differential/RatFunc/Basic.lean`,
`repartitionDualComponent_ratFuncWeilDifferential_inv_X`. -/
private theorem rationalDifferential_normalization (k : Type*) [Field k] :
    repartitionDualComponent (rationalDifferential k) (Place.infty k)
      (RatFunc.X : RatFunc k)⁻¹ = -1 :=
  (exists_normalized_rational k).choose_spec.2.2

/-- THEOREM (proved). The normalization makes `dX` nonzero.
Locator: Tau Ceti, `Differential/RatFunc/Basic.lean`, `ratFuncWeilDifferential_ne_zero`. -/
private theorem rationalDifferential_ne_zero (k : Type*) [Field k] :
    rationalDifferential k ≠ 0 := by
  intro h
  have := rationalDifferential_normalization k
  rw [h, repartitionDualComponent_apply, LinearMap.zero_apply, eq_comm, neg_eq_zero] at this
  exact one_ne_zero this

/-- THEOREM (proved). The divisor of the normalized rational differential is `-2[∞]`.
Locator: Tau Ceti, `Differential/RatFunc/Basic.lean`,
`weilDifferentialDivisor_ratFuncWeilDifferential`. -/
private theorem rationalDifferential_divisor (k : Type*) [Field k] :
    weilDifferentialDivisor (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc
        (rationalDifferential_mem k) (rationalDifferential_ne_zero k) =
      (-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k) :=
  (isGreatest_weilDifferentialDivisor _ _ (rationalDifferential_mem k)
    (rationalDifferential_ne_zero k)).unique (rationalDifferential_greatest k)

/-! ## The comparison determined by a separating element -/

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}

/-- DEFINITION. The Weil differential `dx` is the cotrace of the normalized `dX` along
`k(X) → F`, `X ↦ x`. This fixes the comparison independently of any choice of a
holomorphic differential. Locator: Tau Ceti, `Differential/Comparison.lean`,
`weilDifferentialOfSeparating`. -/
def differentialOfSeparating (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    ↥(weilDifferentialSpace k F) :=
  letI := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
    ⟨rationalDifferential k, rationalDifferential_mem k⟩

/-- THEOREM (proved). The cotrace attached to a separating element is nonzero.
Locator: Tau Ceti, `Differential/Comparison.lean`, `weilDifferentialOfSeparating_ne_zero`. -/
theorem differentialOfSeparating_ne_zero (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    differentialOfSeparating hF hx ≠ 0 := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  rw [differentialOfSeparating, ne_eq, weilDifferentialCotrace_eq_zero_iff,
    Submodule.mk_eq_zero]
  exact rationalDifferential_ne_zero k

/-- DEFINITION. A basis of the Weil differentials on the nonzero cotrace `dx`.
Locator: Tau Ceti, `Differential/Comparison.lean`, `weilDifferentialBasisOfSeparating`. -/
private def differentialBasis (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    Basis Unit F ↥(weilDifferentialSpace k F) :=
  let _ := weilDifferentialSpaceModule hF
  FiniteDimensional.basisSingleton Unit (finrank_weilDifferentialSpace hF hex)
    (differentialOfSeparating hF hx) (differentialOfSeparating_ne_zero hF hx)

/-- THEOREM (proved). The single basis vector is the cotrace `dx`.
Locator: Tau Ceti, `Differential/Comparison.lean`, `weilDifferentialBasisOfSeparating_apply`. -/
private theorem differentialBasis_apply (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (i : Unit) :
    letI := weilDifferentialSpaceModule hF
    differentialBasis hF hex hx i = differentialOfSeparating hF hx := by
  let _ := weilDifferentialSpaceModule hF
  rw [differentialBasis]
  exact FiniteDimensional.basisSingleton_apply _ _ _ _ i

/-- DEFINITION. The function-field-linear Kähler–Weil comparison sends the universal `dx`
to its normalized cotrace. Locator: Tau Ceti, `Differential/Comparison.lean`,
`kaehlerDifferentialEquivWeilDifferentialOfSeparating`. -/
def comparison (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    KaehlerDifferential k F ≃ₗ[F] ↥(weilDifferentialSpace k F) :=
  letI := weilDifferentialSpaceModule hF
  (kaehlerBasisOfSeparating hx).equiv (differentialBasis hF hex hx) (Equiv.refl Unit)

/-- THEOREM (proved). The comparison takes the universal differential of `x` to its cotrace.
Locator: Tau Ceti, `Differential/Comparison.lean`,
`kaehlerDifferentialEquivWeilDifferentialOfSeparating_D_self`. -/
theorem comparison_D_self (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    comparison hF hex hx (D k F x) = differentialOfSeparating hF hx := by
  let _ := weilDifferentialSpaceModule hF
  rw [← kaehlerBasisOfSeparating_apply hx (), comparison, Basis.equiv_apply]
  exact differentialBasis_apply hF hex hx ()

/-- THEOREM (proved). For every function `y`, the comparison sends `dy` to `(dy/dx) dx`.
Locator: Tau Ceti, `Differential/Comparison.lean`,
`kaehlerDifferentialEquivWeilDifferentialOfSeparating_D`. -/
theorem comparison_D (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (y : F) :
    letI := weilDifferentialSpaceModule hF
    comparison hF hex hx (D k F y) =
      derivativeOfSeparating hx y • differentialOfSeparating hF hx := by
  let _ := weilDifferentialSpaceModule hF
  rw [← derivativeOfSeparating_smul_D hx y, map_smul, comparison_D_self]

/-- THEOREM (proved). The divisor of a separating differential is the different minus twice
the pole divisor of the parameter. Locator: Tau Ceti, `Differential/Comparison.lean`,
`weilDifferentialDivisor_weilDifferentialOfSeparating`. -/
theorem differentialOfSeparating_divisor (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] :
    letI := ratFuncAlgebraOfTranscendental hx
    letI := isScalarTower_ratFuncAlgebraOfTranscendental hx
    letI := isFunctionField_iff_functionField.mp hF
    letI := isSeparable_ratFuncAlgebraOfTranscendental hx
    weilDifferentialDivisor hF hex (differentialOfSeparating hF hx).2
        (by simpa using differentialOfSeparating_ne_zero hF hx) =
      (-2 : ℤ) • Divisor.poles hF (Units.mk0 x hx.ne_zero) +
        Divisor.different k F (IsFunctionField.ratFunc k) := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  have hX : Units.map (algebraMap (RatFunc k) F : RatFunc k →* F)
      (Units.mk0 RatFunc.X RatFunc.X_ne_zero) = Units.mk0 x hx.ne_zero :=
    Units.ext (algebraMap_ratFuncAlgebraOfTranscendental_X hx)
  dsimp only [differentialOfSeparating]
  rw [weilDifferentialDivisor_weilDifferentialCotrace (IsFunctionField.ratFunc k) hF
      isIntegrallyClosedIn_ratFunc hex _ (by simpa using rationalDifferential_ne_zero k),
    rationalDifferential_divisor, map_zsmul, ← Divisor.poles_X,
    Divisor.conorm_poles k F (IsFunctionField.ratFunc k) hF, hX]

/-! ## A local bound for the different -/

section DifferentBounds

attribute [local instance 10] Place.algebraIntegersExtension
  Place.isScalarTowerIntegersExtension

/-- THEOREM (proved). A monic generating equation bounds the different exponent by the
order of its derivative. Locator: Tau Ceti, `Different/Derivative.lean`,
`differentExponent_le_ord_aeval_derivative`. -/
private theorem different_le_derivative
    {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k' F']
    [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    {P' : Place k' F'} {y : F'} (hgen : F⟮y⟯ = ⊤) {ψ : F[X]}
    (hψ : ψ.Monic) (hcoeff : ∀ i, ψ.coeff i ∈ (P'.restrict k F).integers)
    (hy : aeval y ψ = 0) (hψ' : aeval y (derivative ψ) ≠ 0) :
    (Place.differentExponent k F P' : ℤ) ≤ P'.ord (aeval y (derivative ψ)) := by
  set A := (P'.restrict k F).integers
  obtain ⟨q, hq, -, hqm⟩ := lifts_and_degree_eq_and_monic
    ((lifts_iff_coeff_lifts (f := algebraMap A F) ψ).mpr fun i ↦ ⟨⟨_, hcoeff i⟩, rfl⟩) hψ
  have hqy : aeval y q = 0 := by rw [← aeval_map_algebraMap F, hq, hy]
  have hint : IsIntegral A y := ⟨q, hqm, by rwa [← aeval_def]⟩
  set z : integralClosure A F' := ⟨y, hint⟩
  have hz : algebraMap (integralClosure A F') F' z = y := rfl
  have hgen' : Algebra.adjoin F {algebraMap (integralClosure A F') F' z} = ⊤ := by
    rw [hz, ← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic y), hgen, IntermediateField.top_toSubalgebra]
  have hinj : Function.Injective (algebraMap (integralClosure A F') F') :=
    FaithfulSMul.algebraMap_injective _ _
  have hqz : aeval z q = 0 := hinj (by rw [← aeval_algebraMap_apply, hz, hqy, map_zero])
  have hmem : aeval z (derivative q) ∈ differentIdeal A (integralClosure A F') :=
    aeval_derivative_mem_differentIdeal_of_aeval_eq_zero (K := F) (L := F') hgen' hqz
  have hval : algebraMap (integralClosure A F') F' (aeval z (derivative q)) =
      aeval y (derivative ψ) := by
    rw [← aeval_algebraMap_apply, hz, ← hq, derivative_map, aeval_map_algebraMap]
  have hne : aeval z (derivative q) ≠ 0 := by
    rintro h0
    rw [h0, map_zero] at hval
    exact hψ' hval.symm
  rw [← hval]
  exact Place.differentExponent_le_ord_of_mem_differentIdeal k F P' hmem hne

/-- THEOREM (proved). For a quadratic generator `z² + uz = v`, the different exponent is
at most the order of `2z + u`. Locator: Tau Ceti, `Different/Derivative.lean`,
`differentExponent_le_ord_two_mul_add`. -/
private theorem different_le_quadratic
    {k' F' : Type*} [Field k'] [Field F'] [Algebra k k'] [Algebra k' F']
    [Algebra F F'] [Algebra k F'] [IsScalarTower k k' F'] [IsScalarTower k F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    {P' : Place k' F'} {u v : F} (hu : algebraMap F F' u ∈ P'.integers)
    (hv : algebraMap F F' v ∈ P'.integers) {z : F'} (hgen : F⟮z⟯ = ⊤)
    (hz : z ^ 2 + algebraMap F F' u * z - algebraMap F F' v = 0)
    (hne : 2 * z + algebraMap F F' u ≠ 0) :
    (Place.differentExponent k F P' : ℤ) ≤ P'.ord (2 * z + algebraMap F F' u) := by
  have hψ : (X ^ 2 + C u * X - C v : F[X]).Monic := by monicity!
  have hderiv : aeval z (derivative (X ^ 2 + C u * X - C v : F[X])) =
      2 * z + algebraMap F F' u := by
    simp only [derivative_sub, derivative_X_pow, derivative_C_mul_X, derivative_C, sub_zero,
      map_add, map_mul, aeval_C, Nat.cast_ofNat, map_ofNat]
    norm_num
  rw [← hderiv]
  refine different_le_derivative hgen hψ (fun i ↦ ?_)
    (by simpa using hz) (by rwa [hderiv])
  rw [Place.mem_integers_restrict_iff]
  rcases i with _ | _ | _ | i <;>
    simp [coeff_X, coeff_C, coeff_X_pow, neg_mem_iff, hu, hv]

end DifferentBounds

/-! ## The two Weierstrass charts -/

variable (W : WeierstrassCurve.Affine k)

open WeierstrassCurve.Affine

/-- THEOREM (proved). The rational-function action through `x` extends the existing
polynomial action. Locator: Tau Ceti,
`Affine/FunctionField/Divisor/InvariantDifferential.lean`, `isScalarTower_polynomial_ratFunc`. -/
private theorem polynomial_ratFunc_tower :
    letI := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    IsScalarTower k[X] (RatFunc k) W.FunctionField := by
  let _ := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
  refine .of_algebraMap_eq fun p ↦ ?_
  rw [algebraMap_ratFuncAlgebraOfTranscendental_apply,
    RatFunc.algEquivOfTranscendental_algebraMap, algebraMap_eq_aeval_genericX]
  simp

/-- THEOREM (proved). The coordinate functions satisfy the Weierstrass equation.
Locator: Tau Ceti, `Affine/FunctionField/Divisor/InvariantDifferential.lean`,
`genericY_sq_add_eq`. -/
private theorem coordinate_equation :
    genericY W ^ 2 + algebraMap k W.FunctionField W.a₁ * genericX W * genericY W +
        algebraMap k W.FunctionField W.a₃ * genericY W =
      genericX W ^ 3 + algebraMap k W.FunctionField W.a₂ * genericX W ^ 2 +
        algebraMap k W.FunctionField W.a₄ * genericX W + algebraMap k W.FunctionField W.a₆ := by
  have h := (equation_iff _ _).mp (equation_genericX_genericY W)
  simpa [WeierstrassCurve.baseChange] using h

variable [W.IsElliptic]

/-- THEOREM (proved). At every place, the different exponent is bounded by the order of
`2y + a₁x + a₃` plus twice the pole order of `x`.
Locator: Tau Ceti, `Affine/FunctionField/Divisor/InvariantDifferential.lean`,
`differentExponent_le`; Silverman, Proposition III.1.5. -/
private theorem weierstrass_different_bound (P : Place k W.FunctionField) :
    letI := ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    letI := isScalarTower_ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    letI := isFunctionField_iff_functionField.mp W.isFunctionField
    letI := isSeparable_ratFuncAlgebraOfTranscendental (transcendental_genericX W)
    (Place.differentExponent k (RatFunc k) P : ℤ) ≤
      P.ord (invariantDifferentialDenom W) + 2 * (-P.ord (genericX W) ⊔ 0) := by
  let hx := transcendental_genericX W
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp W.isFunctionField
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  let _ := polynomial_ratFunc_tower W
  have heq := coordinate_equation W
  set x := genericX W
  set y := genericY W
  have hX : algebraMap (RatFunc k) W.FunctionField RatFunc.X = x :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hx
  have hC (c : k) : algebraMap (RatFunc k) W.FunctionField (algebraMap k (RatFunc k) c) =
      algebraMap k W.FunctionField c :=
    (IsScalarTower.algebraMap_apply k (RatFunc k) W.FunctionField c).symm
  have hc (c : k) : algebraMap k W.FunctionField c ∈ P.integers := P.algebraMap_mem_integers c
  have hden : invariantDifferentialDenom W =
      2 * y + algebraMap k W.FunctionField W.a₁ * x + algebraMap k W.FunctionField W.a₃ :=
    invariantDifferentialDenom_def W
  have hxx : P.ord (genericX W) = P.ord x := rfl
  rcases le_or_gt 0 (P.ord x) with hxP | hxP
  · have hxi : x ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr hxP
    have hu : 2 * y + algebraMap (RatFunc k) W.FunctionField
        (algebraMap k (RatFunc k) W.a₁ * RatFunc.X + algebraMap k (RatFunc k) W.a₃) =
        invariantDifferentialDenom W := by
      simp only [map_add, map_mul, hX, hC, hden]
      ring
    have h := different_le_quadratic (k := k) (F := RatFunc k) (P' := P)
      (u := algebraMap k (RatFunc k) W.a₁ * RatFunc.X + algebraMap k (RatFunc k) W.a₃)
      (v := RatFunc.X ^ 3 + algebraMap k (RatFunc k) W.a₂ * RatFunc.X ^ 2 +
        algebraMap k (RatFunc k) W.a₄ * RatFunc.X + algebraMap k (RatFunc k) W.a₆) (z := y)
      (by simp only [map_add, map_mul, hX, hC]; exact add_mem (mul_mem (hc _) hxi) (hc _))
      (by
        simp only [map_add, map_mul, map_pow, hX, hC]
        exact add_mem (add_mem (add_mem (pow_mem hxi _) (mul_mem (hc _) (pow_mem hxi _)))
          (mul_mem (hc _) hxi)) (hc _))
      (adjoin_genericY_eq_top W (RatFunc k))
      (by simp only [map_add, map_mul, map_pow, hX, hC]; linear_combination heq)
      (by rw [hu]; exact invariantDifferentialDenom_ne_zero W)
    rw [hu] at h
    omega
  · have hx0 : x ≠ 0 := hx.ne_zero
    have hti : x⁻¹ ∈ P.integers := by
      rw [P.mem_integers_iff_ord_nonneg, P.ord_inv]
      omega
    have hgen : (RatFunc k)⟮y * x⁻¹ ^ 2⟯ = ⊤ := by
      refine top_le_iff.mp ((adjoin_genericY_eq_top W (RatFunc k)).symm.le.trans ?_)
      rw [IntermediateField.adjoin_simple_le_iff]
      have hy : y = algebraMap (RatFunc k) W.FunctionField (RatFunc.X ^ 2) * (y * x⁻¹ ^ 2) := by
        rw [map_pow, hX]
        field_simp
      have hmem := mul_mem
        (IntermediateField.algebraMap_mem (RatFunc k)⟮y * x⁻¹ ^ 2⟯ (RatFunc.X ^ 2))
        (IntermediateField.mem_adjoin_simple_self (RatFunc k) (y * x⁻¹ ^ 2))
      rwa [← hy] at hmem
    have hu : 2 * (y * x⁻¹ ^ 2) + algebraMap (RatFunc k) W.FunctionField
        (algebraMap k (RatFunc k) W.a₁ * RatFunc.X⁻¹ +
          algebraMap k (RatFunc k) W.a₃ * RatFunc.X⁻¹ ^ 2) =
        invariantDifferentialDenom W * (x ^ 2)⁻¹ := by
      simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC, hden]
      field_simp
      ring
    have hx2 : (x ^ 2)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hx0)
    have h := different_le_quadratic (k := k) (F := RatFunc k) (P' := P)
      (u := algebraMap k (RatFunc k) W.a₁ * RatFunc.X⁻¹ +
        algebraMap k (RatFunc k) W.a₃ * RatFunc.X⁻¹ ^ 2)
      (v := RatFunc.X⁻¹ + algebraMap k (RatFunc k) W.a₂ * RatFunc.X⁻¹ ^ 2 +
        algebraMap k (RatFunc k) W.a₄ * RatFunc.X⁻¹ ^ 3 +
        algebraMap k (RatFunc k) W.a₆ * RatFunc.X⁻¹ ^ 4) (z := y * x⁻¹ ^ 2)
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        exact add_mem (mul_mem (hc _) hti) (mul_mem (hc _) (pow_mem hti _)))
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        exact add_mem (add_mem (add_mem hti (mul_mem (hc _) (pow_mem hti _)))
          (mul_mem (hc _) (pow_mem hti _))) (mul_mem (hc _) (pow_mem hti _)))
      hgen
      (by
        simp only [map_add, map_mul, map_pow, map_inv₀, hX, hC]
        field_simp
        linear_combination heq)
      (by rw [hu]; exact mul_ne_zero (invariantDifferentialDenom_ne_zero W) hx2)
    rw [hu, P.ord_mul (invariantDifferentialDenom_ne_zero W) hx2, P.ord_inv, P.ord_pow] at h
    push_cast at h
    omega

/-! ## Divisor zero and the holomorphic line -/

/-- DEFINITION. The invariant Weil differential is the normalized comparison image of
`dx / (2y + a₁x + a₃)`. Locator: Silverman, Proposition III.1.5;
Tau Ceti, `Affine/FunctionField/Divisor/InvariantDifferential.lean`. -/
def invariantWeilDifferential : ↥(weilDifferentialSpace k W.FunctionField) :=
  letI := weilDifferentialSpaceModule W.isFunctionField
  comparison W.isFunctionField (isIntegrallyClosedIn_functionField W)
    (transcendental_genericX W) (invariantDifferential W)

/-- THEOREM (proved). The comparison image of the invariant differential is the inverse
denominator times the cotrace `dx`. Locator: Tau Ceti,
`Affine/FunctionField/Divisor/InvariantDifferential.lean`,
`kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential`. -/
theorem invariantWeilDifferential_formula :
    letI := weilDifferentialSpaceModule W.isFunctionField
    invariantWeilDifferential W =
      (invariantDifferentialDenom W)⁻¹ •
        differentialOfSeparating W.isFunctionField (transcendental_genericX W) := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  rw [invariantWeilDifferential, invariantDifferential_def, map_smul, comparison_D_self]

/-- THEOREM (proved). The invariant Weil differential is nonzero.
Locator: Tau Ceti, `Affine/FunctionField/Divisor/InvariantDifferential.lean`,
`kaehlerDifferentialEquivWeilDifferentialOfSeparating_invariantDifferential_ne_zero`. -/
theorem invariantWeilDifferential_ne_zero :
    (invariantWeilDifferential W : Module.Dual k ↥(repartitionSpace k W.FunctionField)) ≠ 0 := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  rw [invariantWeilDifferential, ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff]
  exact invariantDifferential_ne_zero W

/-- THEOREM (proved, S2c). The invariant differential has divisor zero, with no assumption
of holomorphy, no chosen regular generator, and no printed input.
Locator: Silverman, Proposition III.1.5; Tau Ceti,
`Affine/FunctionField/Divisor/InvariantDifferential.lean`,
`weilDifferentialDivisor_invariantDifferential`. -/
theorem invariantWeilDifferential_divisor :
    weilDifferentialDivisor W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (invariantWeilDifferential W).2 (invariantWeilDifferential_ne_zero W) = 0 := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  let hF := W.isFunctionField
  let hex := isIntegrallyClosedIn_functionField W
  let hx := transcendental_genericX W
  let z : W.FunctionFieldˣ := Units.mk0 (invariantDifferentialDenom W)⁻¹
    (inv_ne_zero (invariantDifferentialDenom_ne_zero W))
  have hD := weilDifferentialDivisor_repartitionDualMul hF hex
    (differentialOfSeparating hF hx).2
    (by simpa using differentialOfSeparating_ne_zero hF hx) z
  rw [differentialOfSeparating_divisor] at hD
  have hω : (invariantWeilDifferential W : Module.Dual k ↥(repartitionSpace k W.FunctionField)) =
      repartitionDualMul hF (z : W.FunctionField) (differentialOfSeparating hF hx) := by
    rw [invariantWeilDifferential_formula, coe_weilDifferentialSpaceModule_smul, Units.val_mk0]
  refine Divisor.eq_of_le_of_degree_eq hF ?_ ?_
  · rw [(weilDifferentialDivisor_congr hF hex hω _ _ _ _).trans hD, WeilDivisor.le_iff]
    intro P
    have h := weierstrass_different_bound W P
    simp only [WeilDivisor.coeff_add, WeilDivisor.coeff_zsmul, Divisor.coeff_principal,
      Divisor.coeff_poles, Divisor.coeff_different, WeilDivisor.coeff_zero, z, Units.val_mk0,
      P.ord_inv]
    omega
  · rw [degree_weilDifferentialDivisor, genus_functionField, map_zero]
    norm_num

/-- THEOREM (proved, S2c). The invariant Weil differential is holomorphic.
Locator: Silverman, Proposition III.1.5; the divisor-filtration characterization
`TauCeti.mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor`. -/
theorem invariantWeilDifferential_mem_holomorphic :
    (invariantWeilDifferential W : Module.Dual k ↥(repartitionSpace k W.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor k W.FunctionField) := by
  rw [mem_weilDifferentialFiltration_iff_le_weilDifferentialDivisor W.isFunctionField
    (isIntegrallyClosedIn_functionField W) (invariantWeilDifferential W).2
    (invariantWeilDifferential_ne_zero W), invariantWeilDifferential_divisor W]

/-- THEOREM (proved, S2c). The holomorphic Weil differentials are precisely the constant-field
span of the invariant differential. Locator: Silverman, Proposition III.1.5;
`ModularWeil/DifferentialLine.lean`, `finrank_holomorphicWeilDifferentials_eq_one`. -/
theorem holomorphicWeilDifferentials_eq_span :
    weilDifferentialFiltration (0 : Divisor k W.FunctionField) =
      Submodule.span k {(invariantWeilDifferential W :
        Module.Dual k ↥(repartitionSpace k W.FunctionField))} := by
  let V := weilDifferentialFiltration (0 : Divisor k W.FunctionField)
  let ω : V := ⟨invariantWeilDifferential W, invariantWeilDifferential_mem_holomorphic W⟩
  have hdim : Module.finrank k V = 1 :=
    ZInQ.Contrib.CloudB3RC53.ModularWeil.finrank_holomorphicWeilDifferentials_eq_one W
  have hω : ω ≠ 0 := fun h ↦ invariantWeilDifferential_ne_zero W (congrArg Subtype.val h)
  have hspan : Submodule.span k {ω} = ⊤ :=
    (span_singleton_eq_top_iff_ne_zero_of_finrank_eq_one hdim ω).mpr hω
  have h := congrArg (Submodule.map V.subtype) hspan
  simpa only [Submodule.map_span, Set.image_singleton, Submodule.map_top,
    Submodule.range_subtype, Submodule.subtype_apply, V, ω] using h.symm

/-- THEOREM (proved, S2c). Every holomorphic Weil differential is a unique constant multiple
of the invariant differential. Locator: Silverman, Proposition III.1.5;
`holomorphicWeilDifferentials_eq_span` in this file. -/
theorem existsUnique_smul_invariantWeilDifferential
    (η : ↥(weilDifferentialFiltration (0 : Divisor k W.FunctionField))) :
    ∃! c : k, c • (invariantWeilDifferential W :
      Module.Dual k ↥(repartitionSpace k W.FunctionField)) = η := by
  have hη : (η : Module.Dual k ↥(repartitionSpace k W.FunctionField)) ∈
      Submodule.span k {(invariantWeilDifferential W :
        Module.Dual k ↥(repartitionSpace k W.FunctionField))} := by
    rw [← holomorphicWeilDifferentials_eq_span W]
    exact η.2
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hη
  refine ⟨c, hc, fun d hd ↦ ?_⟩
  exact smul_left_injective k (invariantWeilDifferential_ne_zero W) (hd.trans hc.symm)

/-- THEOREM (proved, S2c). The invariant differential has order zero at every place.
Locator: Silverman, Proposition III.1.5; `invariantWeilDifferential_divisor` in this file. -/
theorem invariantWeilDifferential_order (P : Place k W.FunctionField) :
    weilDifferentialOrder W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (invariantWeilDifferential W).2 (invariantWeilDifferential_ne_zero W) P = 0 := by
  rw [weilDifferentialOrder, invariantWeilDifferential_divisor W, WeilDivisor.coeff_zero]

/-- THEOREM (proved, S2c). A Kähler differential has holomorphic comparison image exactly
when it is a unique constant multiple of the invariant differential.
Locator: Silverman, Proposition III.1.5; `existsUnique_smul_invariantWeilDifferential`
and `comparison` in this file. -/
theorem comparison_mem_holomorphic_iff (η : KaehlerDifferential k W.FunctionField) :
    letI := weilDifferentialSpaceModule W.isFunctionField
    (comparison W.isFunctionField (isIntegrallyClosedIn_functionField W)
        (transcendental_genericX W) η : Module.Dual k ↥(repartitionSpace k W.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor k W.FunctionField) ↔
        ∃! c : k, c • invariantDifferential W = η := by
  let _ := weilDifferentialSpaceModule W.isFunctionField
  let _ := isScalarTower_weilDifferentialSpace W.isFunctionField
  let φ := comparison W.isFunctionField (isIntegrallyClosedIn_functionField W)
    (transcendental_genericX W)
  let φk := φ.restrictScalars k
  have hφω : φk (invariantDifferential W) = invariantWeilDifferential W := rfl
  constructor
  · intro h
    obtain ⟨c, hc, _⟩ := existsUnique_smul_invariantWeilDifferential W ⟨φ η, h⟩
    have hcW : c • invariantWeilDifferential W = φk η := Subtype.ext hc
    have hcK : c • invariantDifferential W = η := by
      apply φk.injective
      rwa [map_smul, hφω]
    refine ⟨c, hcK, fun d hd ↦ ?_⟩
    exact smul_left_injective k (invariantDifferential_ne_zero W) (hd.trans hcK.symm)
  · rintro ⟨c, hc, _⟩
    change (φk η : Module.Dual k ↥(repartitionSpace k W.FunctionField)) ∈ _
    rw [← hc, map_smul, hφω, Submodule.coe_smul]
    exact (weilDifferentialFiltration (0 : Divisor k W.FunctionField)).smul_mem c
      (invariantWeilDifferential_mem_holomorphic W)

end ZInQ.Contrib.RC53Assist.InvariantDifferential
