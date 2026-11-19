import ZInQKernel.Contrib.CloudB3RC53.ModularWeil.IsogenyLattice
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Differential
import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Separability

/-!
# The algebraic glue G2alg reduced to the constancy of the pull-back coefficient

`IsogenyLattice.lean` reduces the isogeny–lattice glue G2 to an analytic glue (G2an) and an
algebraic glue `IsogenyScalarRationalGlue` (G2alg: every `ℚ`-isogeny has a pull-back scalar, a
nonzero rational number). This file proves the differential algebra of G2alg from Tau Ceti's
invariant differential and isolates its remaining content, the constancy of the pull-back
coefficient.

From Tau Ceti (vendored, Apache-2.0; library results used as infrastructure, not prints):
`invariantDifferential` (`ω = dx / (2y + a₁x + a₃)`), `existsUnique_smul_invariantDifferential`
(every Kähler differential of `K(E)` is `c • ω` for a unique `c ∈ K(E)`: `Ω[K(E)/F]` is the line
`K(E) · ω = K(E) · dx`), `Isogeny.pullbackDifferential` and the separability criterion
`isSeparable_iff_pullbackDifferential_ne_zero` (Silverman II.4.2(c)).

* `genericX_eq_coordX`, `invariantDifferentialDenom_eq_omegaDen` (PROVED): the coordinates and the
  denominator of `IsPullbackScalar` are Tau Ceti's generic point and `invariantDifferentialDenom`.
* `isPullbackScalar_iff` (PROVED): `IsPullbackScalar β r ↔ β^* ω₂ = r • ω₁`.
* `exists_unique_pullbackCoefficient` (PROVED, step 1): `β^* ω₂ = c • ω₁` for a unique `c ∈ K(E₁)`
  (the pull-back coefficient, a function).
* `pullbackCoefficient_ne_zero` (PROVED, step 2): in characteristic zero the coefficient is nonzero
  (every isogeny is separable; Tau Ceti's separability criterion).
* **`PullbackCoefficientConstantGlue` (GLUE, the remaining piece)**: for an isogeny over `ℚ` the
  pull-back coefficient is a constant, `c ∈ ℚ ⊆ ℚ(E₁)`. Classical proof (Silverman III.5.2):
  `ω₂` is translation-invariant and holomorphic without zeros, so `β^* ω₂` is holomorphic without
  zeros (the different of a separable isogeny vanishes); hence `c` has trivial divisor and is a
  constant of `ℚ(E₁)`, i.e. lies in `ℚ`. Tau Ceti proves the Weil-differential side of this
  (`weilDifferentialDivisor_weilDifferentialCotrace`, `Isogeny.different_eq_zero`, genus one,
  `isIntegrallyClosedIn_functionField`); what is missing is the comparison of Kähler differentials
  with Weil differentials (divisors of Kähler differentials) compatible with the pull-back. Not
  proved here.
* **`isogenyScalarRationalGlue_of_constant` (PROVED, step 3)**: `PullbackCoefficientConstantGlue →
  IsogenyScalarRationalGlue`.
* Non-vacuity: `pullbackCoefficient_id` (the identity isogeny has coefficient `1`, a constant).

Kinds: PROVED, and one GLUE.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.ModularWeil

open WeierstrassCurve.Affine Polynomial

section Bridge

variable {F : Type} [Field F]

/-- `coordX` is Tau Ceti's generic `x`-coordinate. PROVED. -/
theorem genericX_eq_coordX (W : WeierstrassCurve.Affine F) :
    algebraMap W.CoordinateRing W.FunctionField (coordX W) = genericX W := by
  rw [genericX_def, coordX, AdjoinRoot.mk_C]

/-- `coordY` is Tau Ceti's generic `y`-coordinate. PROVED. -/
theorem genericY_eq_coordY (W : WeierstrassCurve.Affine F) :
    algebraMap W.CoordinateRing W.FunctionField (coordY W) = genericY W := by
  rw [genericY_def, coordY]
  rfl

/-- The constant `a ∈ F` in the coordinate ring, mapped to the function field. PROVED. -/
theorem algebraMap_of_C (W : WeierstrassCurve.Affine F) (a : F) :
    algebraMap W.CoordinateRing W.FunctionField (AdjoinRoot.of W.polynomial (Polynomial.C a)) =
      algebraMap F W.FunctionField a := by
  rw [IsScalarTower.algebraMap_apply F W.CoordinateRing W.FunctionField]
  rfl

/-- `omegaDen` is Tau Ceti's `invariantDifferentialDenom`. PROVED. -/
theorem invariantDifferentialDenom_eq_omegaDen (W : WeierstrassCurve.Affine F) :
    algebraMap W.CoordinateRing W.FunctionField (omegaDen W) = invariantDifferentialDenom W := by
  rw [invariantDifferentialDenom_def, omegaDen, map_add, map_add, map_mul, map_mul, map_ofNat,
    genericX_eq_coordX, genericY_eq_coordY, algebraMap_of_C, algebraMap_of_C]

end Bridge

section Scalar

variable {F : Type} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- **`IsPullbackScalar` is Tau Ceti's pull-back of the invariant differential**:
`IsPullbackScalar β r ↔ β^* ω₂ = r • ω₁`. PROVED. -/
theorem isPullbackScalar_iff [W₁.IsElliptic] [W₂.IsElliptic] (β : TauCeti.Isogeny W₁ W₂) (r : F) :
    IsPullbackScalar β r ↔
      β.pullbackDifferential (invariantDifferential W₂) =
        algebraMap F W₁.FunctionField r • invariantDifferential W₁ := by
  have hd₁ : invariantDifferentialDenom W₁ ≠ 0 := invariantDifferentialDenom_ne_zero W₁
  have hu : β.fieldPullback (invariantDifferentialDenom W₂) ≠ 0 :=
    (map_ne_zero β.fieldPullback).2 (invariantDifferentialDenom_ne_zero W₂)
  have hpb : ∀ a : W₂.CoordinateRing,
      β.pullback a = β.fieldPullback (algebraMap W₂.CoordinateRing W₂.FunctionField a) :=
    fun a => (TauCeti.Isogeny.fieldPullback_algebraMap β a).symm
  unfold IsPullbackScalar
  rw [hpb, hpb, genericX_eq_coordX, genericX_eq_coordX, invariantDifferentialDenom_eq_omegaDen,
    invariantDifferentialDenom_eq_omegaDen, invariantDifferential_def, invariantDifferential_def,
    TauCeti.Isogeny.pullbackDifferential_smul, TauCeti.Isogeny.pullbackDifferential_D, map_inv₀]
  set u := β.fieldPullback (invariantDifferentialDenom W₂)
  set d := invariantDifferentialDenom W₁
  set X := KaehlerDifferential.D F W₁.FunctionField (β.fieldPullback (genericX W₂))
  set Y := KaehlerDifferential.D F W₁.FunctionField (genericX W₁)
  set a := algebraMap F W₁.FunctionField r
  constructor
  · intro h
    have hX : X = d⁻¹ • ((a * u) • Y) := by rw [← h, smul_smul, inv_mul_cancel₀ hd₁, one_smul]
    rw [hX, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  · intro h
    have hX : X = u • (a • (d⁻¹ • Y)) := by rw [← h, smul_smul, mul_inv_cancel₀ hu, one_smul]
    rw [hX, smul_smul, smul_smul, smul_smul]
    congr 1
    field_simp

/-- **Step 1: the pull-back coefficient exists and is unique** (Tau Ceti's
`existsUnique_smul_invariantDifferential`: `Ω[K(E₁)/F] = K(E₁) · ω₁`). PROVED. -/
theorem exists_unique_pullbackCoefficient [W₁.IsElliptic] (β : TauCeti.Isogeny W₁ W₂) :
    ∃! c : W₁.FunctionField,
      c • invariantDifferential W₁ = β.pullbackDifferential (invariantDifferential W₂) :=
  existsUnique_smul_invariantDifferential W₁ _

/-- **Step 2: in characteristic zero the pull-back coefficient is nonzero** (every isogeny is
separable; Tau Ceti's criterion `isSeparable_iff_pullbackDifferential_ne_zero`, Silverman
II.4.2(c)). PROVED. -/
theorem pullbackCoefficient_ne_zero [CharZero F] [W₁.IsElliptic] [W₂.IsElliptic]
    (β : TauCeti.Isogeny W₁ W₂) {c : W₁.FunctionField}
    (hc : c • invariantDifferential W₁ = β.pullbackDifferential (invariantDifferential W₂)) :
    c ≠ 0 := by
  have : CharZero W₁.FunctionField :=
    charZero_of_injective_algebraMap (algebraMap F W₁.FunctionField).injective
  have : CharZero β.fieldPullback.fieldRange :=
    charZero_of_injective_algebraMap (algebraMap F β.fieldPullback.fieldRange).injective
  have hne := (TauCeti.Isogeny.isSeparable_iff_pullbackDifferential_ne_zero β).mp inferInstance
  rintro rfl
  rw [zero_smul] at hc
  exact hne hc.symm

/-- **Non-vacuity**: the identity isogeny has pull-back coefficient `1`, a constant. PROVED. -/
theorem pullbackCoefficient_id (W : WeierstrassCurve.Affine F) :
    (1 : W.FunctionField) • invariantDifferential W =
      (TauCeti.Isogeny.id W).pullbackDifferential (invariantDifferential W) := by
  rw [TauCeti.Isogeny.pullbackDifferential_id, LinearMap.id_apply, one_smul]

end Scalar

/-! ### The remaining glue and the reduction -/

/-- **The pull-back coefficient of a `ℚ`-isogeny is a constant** (GLUE; Silverman III.5.2): if
`β : E₁ → E₂` is an isogeny over `ℚ` and `β^* ω₂ = c • ω₁` with `c ∈ ℚ(E₁)`, then `c ∈ ℚ`.
Classical proof in the file header. Not proved here. -/
def PullbackCoefficientConstantGlue : Prop :=
  ∀ (E₁ E₂ : WeierstrassCurve ℚ) [E₁.IsElliptic] [E₂.IsElliptic]
    (β : TauCeti.Isogeny E₁.toAffine E₂.toAffine) (c : E₁.toAffine.FunctionField),
    c • invariantDifferential E₁.toAffine =
        β.pullbackDifferential (invariantDifferential E₂.toAffine) →
      c ∈ Set.range (algebraMap ℚ E₁.toAffine.FunctionField)

/-- **Step 3: G2alg from the constancy of the pull-back coefficient**: the coefficient exists
(step 1), is a rational number (the glue), nonzero (step 2), and is a pull-back scalar
(`isPullbackScalar_iff`). Classification: PROVED (from `PullbackCoefficientConstantGlue`). -/
theorem isogenyScalarRationalGlue_of_constant (h : PullbackCoefficientConstantGlue) :
    IsogenyScalarRationalGlue := by
  intro E₁ E₂ h₁ h₂ β
  obtain ⟨c, hc, -⟩ := exists_unique_pullbackCoefficient β
  obtain ⟨r, rfl⟩ := h E₁ E₂ β c hc
  refine ⟨r, fun hr => pullbackCoefficient_ne_zero β hc (by rw [hr, map_zero]), ?_⟩
  exact (isPullbackScalar_iff β r).mpr hc.symm

end ZInQ.Contrib.CloudB3RC53.ModularWeil
