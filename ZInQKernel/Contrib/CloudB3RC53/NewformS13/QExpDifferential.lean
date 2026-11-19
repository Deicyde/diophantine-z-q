import ZInQKernel.Contrib.RC53Assist.NewformPeriods.RationalParametrization
import Mathlib.RingTheory.Kaehler.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Reading translation S3 at the function-field level: `q`-expansions of differentials

Translation S3 of the reduction of `NewformPeriodsRational` (`NewformPeriods/README.md`): "the
canonical map at `∞` and `ν` are defined over `ℚ`; with `δφ(μ(g)) = g(z)dz` and `dz = dq/(2πi q)`,
clause (iv) is `θx = c · ĝ · (2y + a₁x + a₃)`". This file proves the function-field core of that
reading, with the genuine Kähler differentials of `F = ℚ(j, j_M) = modularFunctionFieldQ M`:

* `eulerDer`: the Euler operator `θ = q d/dq` is a `ℚ`-derivation of `ℚ((q))` (Leibniz rule);
* `qExpDiff M : Ω[F⁄ℚ] →ₗ[F] ℚ((q))`: the `q`-expansion of differentials at the cusp `∞`,
  `ω = h · dq/q ↦ h`, the unique `F`-linear map with `d f ↦ θ f` (`qExpDiff_D`);
* `pointAlgHom`: a point `(x, y)` of `A` with coordinates in `F` is a `ℚ`-algebra map
  `φ : ℚ[A] → F` from the coordinate ring of `A` (`X ↦ x`, `Y ↦ y`); `pullback_dX`,
  `pullback_dY`: pulling back the differentials `dX`, `dY` of `ℚ[A]` along `φ` gives `dx`, `dy`;
* `omegaPull`: the pull-back `(2y + a₁x + a₃)⁻¹ dx` of the invariant differential
  `ω_A = dX/(2Y + a₁X + a₃)`; `omegaPull_eq_pullback`: it is the pulled-back `dX` divided by the
  pulled-back denominator;
* **`qExpDiff_omegaPull`**: the `q`-expansion of the pulled-back `ω_A` is `θx · (2y + a₁x + a₃)⁻¹`;
  **`pullbackIsMultiple_iff`**: for `2y + a₁x + a₃ ≠ 0`, the peer's `PullbackIsMultiple A x y ĝ c`
  holds iff the `q`-expansion of the pulled-back invariant differential is `c · ĝ` (times `dq/q`).

What remains of S1/S3: the scheme `X₀(M)` over `ℚ` and its cusp `∞`, the identification of `F` with
the function field of that scheme (and of `F` with the vendored `ModularCurve.modularFunctionField`,
which needs the formal identity `E₄³ − E₆² = 1728 q ∏ (1 − qⁿ)²⁴`), the passage from the coordinate
ring of `A` to its function field, and the analytic normalization `dq/q = 2πi dz`.

All statements are definitions or PROVED.
-/

noncomputable section

namespace ZInQ.Contrib.CloudB3RC53.NewformS13

open ZInQ.Contrib.RC53Assist.NewformPeriods
open HahnSeries

/-! ### The Euler operator is a derivation -/

theorem eulerOp_add (x y : LaurentSeries ℚ) : eulerOp (x + y) = eulerOp x + eulerOp y := by
  ext n
  simp [mul_add]

theorem eulerOp_smul (r : ℚ) (x : LaurentSeries ℚ) : eulerOp (r • x) = r • eulerOp x := by
  ext n
  simp only [eulerOp_coeff, HahnSeries.coeff_smul, smul_eq_mul]
  ring

theorem eulerOp_mul (x y : LaurentSeries ℚ) :
    eulerOp (x * y) = x * eulerOp y + y * eulerOp x := by
  ext n
  have hx : (eulerOp x).support ⊆ x.support := fun i hi => by
    rw [HahnSeries.mem_support, eulerOp_coeff] at hi
    exact (HahnSeries.mem_support _ _).2 (right_ne_zero_of_mul hi)
  have hy : (eulerOp y).support ⊆ y.support := fun i hi => by
    rw [HahnSeries.mem_support, eulerOp_coeff] at hi
    exact (HahnSeries.mem_support _ _).2 (right_ne_zero_of_mul hi)
  rw [eulerOp_coeff, HahnSeries.coeff_add, HahnSeries.coeff_mul,
    HahnSeries.coeff_mul_right' (x := x) y.isPWO_support hy,
    mul_comm y, HahnSeries.coeff_mul_left' (y := y) x.isPWO_support hx, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [Finset.mem_antidiagonal] at hij
  rw [eulerOp_coeff, eulerOp_coeff, ← hij.2.2]
  push_cast
  ring

/-- Coefficients of the `ℚ`-algebra scalar multiplication on `ℚ((q))`. -/
theorem algSmul_coeff (r : ℚ) (x : LaurentSeries ℚ) (n : ℤ) :
    (@HSMul.hSMul ℚ (LaurentSeries ℚ) (LaurentSeries ℚ)
      (@instHSMul ℚ (LaurentSeries ℚ) (HahnSeries.powerSeriesAlgebra ℤ ℚ).toSMul) r x).coeff n =
      r * x.coeff n := by
  rw [Algebra.smul_def, show algebraMap ℚ (LaurentSeries ℚ) r = HahnSeries.C r by simp,
    HahnSeries.C_mul_eq_smul, HahnSeries.coeff_smul, smul_eq_mul]

theorem eulerOp_algebraMap (r : ℚ) : eulerOp (algebraMap ℚ (LaurentSeries ℚ) r) = 0 := by
  ext n
  rw [eulerOp_coeff, HahnSeries.coeff_zero]
  by_cases h : n = 0
  · subst h; simp
  · have : (algebraMap ℚ (LaurentSeries ℚ) r).coeff n = 0 := by
      rw [show algebraMap ℚ (LaurentSeries ℚ) r = HahnSeries.C r by simp, HahnSeries.C_apply,
        HahnSeries.coeff_single_of_ne h]
    rw [this, mul_zero]

/-- **The Euler operator `θ = q d/dq` as a `ℚ`-derivation of `ℚ((q))`.** -/
def eulerDer : Derivation ℚ (LaurentSeries ℚ) (LaurentSeries ℚ) where
  toFun := eulerOp
  map_add' := eulerOp_add
  map_smul' r x := by
    ext n
    rw [RingHom.id_apply]
    erw [eulerOp_coeff, HahnSeries.coeff_smul, algSmul_coeff, eulerOp_coeff]
    simp only [smul_eq_mul]
    ring
  map_one_eq_zero' := by
    change eulerOp 1 = 0
    ext n
    rw [eulerOp_coeff, HahnSeries.coeff_one, HahnSeries.coeff_zero]
    split_ifs with h <;> simp [h]
  leibniz' x y := by
    change eulerOp (x * y) = x • eulerOp y + y • eulerOp x
    rw [eulerOp_mul, smul_eq_mul, smul_eq_mul]

@[simp]
theorem eulerDer_apply (x : LaurentSeries ℚ) : eulerDer x = eulerOp x := rfl

/-! ### The `q`-expansion of differentials of `ℚ(j, j_M)` -/

section QExp

variable (M : ℕ) [NeZero M]

/-- The function field `F = ℚ(j, j_M)` (as a field). -/
abbrev FQ : Type := ↥(modularFunctionFieldQ M)

/-- The scalar tower `ℚ → F → ℚ((q))` for the characteristic-zero `ℚ`-algebra structure of `F`. -/
instance isScalarTowerFQ :
    @IsScalarTower ℚ ↥(modularFunctionFieldQ M) (LaurentSeries ℚ)
      (@Algebra.toSMul ℚ ↥(modularFunctionFieldQ M) _ _ DivisionRing.toRatAlgebra) Algebra.toSMul
      Algebra.toSMul :=
  @IsScalarTower.of_algebraMap_eq ℚ ↥(modularFunctionFieldQ M) (LaurentSeries ℚ) _ _ _
    DivisionRing.toRatAlgebra _ _ fun r => by
      rw [eq_ratCast (algebraMap ℚ (LaurentSeries ℚ)) r,
        eq_ratCast (@algebraMap ℚ ↥(modularFunctionFieldQ M) _ _ DivisionRing.toRatAlgebra) r,
        map_ratCast]

/-- `θ` restricted to `F`, with values in `ℚ((q))` (an `F`-module). -/
def eulerDerF : Derivation ℚ (FQ M) (LaurentSeries ℚ) :=
  eulerDer.compAlgebraMap (FQ M)

/-- **The `q`-expansion of differentials at the cusp `∞`**: `Ω[F⁄ℚ] → ℚ((q))`, `h · dq/q ↦ h`;
the unique `F`-linear map with `d f ↦ θ f`. -/
def qExpDiff : Ω[FQ M⁄ℚ] →ₗ[FQ M] LaurentSeries ℚ :=
  (eulerDerF M).liftKaehlerDifferential

@[simp]
theorem qExpDiff_D (f : FQ M) :
    qExpDiff M (KaehlerDifferential.D ℚ (FQ M) f) = eulerOp (f : LaurentSeries ℚ) :=
  ((eulerDerF M).liftKaehlerDifferential_comp_D f).trans (by
    simp only [eulerDerF, Derivation.compAlgebraMap_apply, eulerDer_apply]
    rfl)

theorem qExpDiff_smul (a : FQ M) (ω : Ω[FQ M⁄ℚ]) :
    qExpDiff M (a • ω) = (a : LaurentSeries ℚ) * qExpDiff M ω := by
  rw [map_smul]
  rfl

end QExp

/-! ### Points of `A` over `F` and the pull-back of differentials -/

section Pullback

variable (M : ℕ) [NeZero M] (A : WeierstrassCurve ℚ)

/-- The Weierstrass equation of `A` at `(x, y) ∈ F²`. -/
def OnCurve (x y : FQ M) : Prop :=
  y ^ 2 + algebraMap ℚ (FQ M) A.a₁ * x * y + algebraMap ℚ (FQ M) A.a₃ * y =
    x ^ 3 + algebraMap ℚ (FQ M) A.a₂ * x ^ 2 + algebraMap ℚ (FQ M) A.a₄ * x +
      algebraMap ℚ (FQ M) A.a₆

variable {M A}

theorem eval_polynomial {x y : FQ M} (h : OnCurve M A x y) :
    Polynomial.eval₂ (Polynomial.aeval x).toRingHom y A.toAffine.polynomial = 0 := by
  rw [WeierstrassCurve.Affine.polynomial]
  simp only [Polynomial.eval₂_sub, Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, Polynomial.eval₂_mul, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.aeval_X, map_add, map_mul, Polynomial.aeval_C, map_pow]
  rw [sub_eq_zero]
  simp only [OnCurve] at h
  linear_combination h

/-- **A point of `A` with coordinates in `F` is a `ℚ`-algebra map from the coordinate ring of `A`
to `F`** (`X ↦ x`, `Y ↦ y`; the function-field form of a map from the modular curve to `A`). -/
def pointAlgHom {x y : FQ M} (h : OnCurve M A x y) : A.toAffine.CoordinateRing →ₐ[ℚ] FQ M :=
  (AdjoinRoot.lift (Polynomial.aeval x).toRingHom y (eval_polynomial h)).toRatAlgHom

theorem pointAlgHom_X {x y : FQ M} (h : OnCurve M A x y) :
    pointAlgHom h (AdjoinRoot.of _ Polynomial.X) = x := by
  simp [pointAlgHom]

theorem pointAlgHom_Y {x y : FQ M} (h : OnCurve M A x y) :
    pointAlgHom h (AdjoinRoot.root _) = y := by
  simp [pointAlgHom]

/-- The pull-back of differentials along `φ : ℚ[A] → F`. -/
def pullbackDiff (φ : A.toAffine.CoordinateRing →ₐ[ℚ] FQ M) :
    Ω[A.toAffine.CoordinateRing⁄ℚ] →ₗ[ℚ] Ω[FQ M⁄ℚ] :=
  letI : Algebra A.toAffine.CoordinateRing (FQ M) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ A.toAffine.CoordinateRing (FQ M) :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  (KaehlerDifferential.map ℚ ℚ A.toAffine.CoordinateRing (FQ M)).restrictScalars ℚ

theorem pullbackDiff_D (φ : A.toAffine.CoordinateRing →ₐ[ℚ] FQ M)
    (r : A.toAffine.CoordinateRing) :
    pullbackDiff φ (KaehlerDifferential.D ℚ _ r) = KaehlerDifferential.D ℚ (FQ M) (φ r) := by
  let _ : Algebra A.toAffine.CoordinateRing (FQ M) := φ.toRingHom.toAlgebra
  have : IsScalarTower ℚ A.toAffine.CoordinateRing (FQ M) :=
    IsScalarTower.of_algebraMap_eq fun r => (φ.commutes r).symm
  exact KaehlerDifferential.map_D ℚ ℚ A.toAffine.CoordinateRing (FQ M) r

/-- **Pulling back `dX` gives `dx`.** -/
theorem pullback_dX {x y : FQ M} (h : OnCurve M A x y) :
    pullbackDiff (pointAlgHom h) (KaehlerDifferential.D ℚ _ (AdjoinRoot.of _ Polynomial.X)) =
      KaehlerDifferential.D ℚ (FQ M) x := by
  rw [pullbackDiff_D, pointAlgHom_X]

/-- **Pulling back `dY` gives `dy`.** -/
theorem pullback_dY {x y : FQ M} (h : OnCurve M A x y) :
    pullbackDiff (pointAlgHom h) (KaehlerDifferential.D ℚ _ (AdjoinRoot.root _)) =
      KaehlerDifferential.D ℚ (FQ M) y := by
  rw [pullbackDiff_D, pointAlgHom_Y]

/-- The denominator `2y + a₁x + a₃` of `ω_A = dX/(2Y + a₁X + a₃)` at `(x, y)`. -/
def denomF (A : WeierstrassCurve ℚ) (x y : FQ M) : FQ M :=
  (y + y) + algebraMap ℚ (FQ M) A.a₁ * x + algebraMap ℚ (FQ M) A.a₃

/-- **The pull-back of the invariant differential** `ω_A = dX/(2Y + a₁X + a₃)` along `(x, y)`:
`(2y + a₁x + a₃)⁻¹ · dx` (the pull-back of `dX` divided by the pulled-back denominator). -/
def omegaPull (A : WeierstrassCurve ℚ) (x y : FQ M) : Ω[FQ M⁄ℚ] :=
  (denomF A x y)⁻¹ • KaehlerDifferential.D ℚ (FQ M) x

/-- The pulled-back invariant differential is the pull-back of `dX` along `φ`, divided by the
pulled-back denominator. -/
theorem omegaPull_eq_pullback {x y : FQ M} (h : OnCurve M A x y) :
    omegaPull A x y = (denomF A x y)⁻¹ •
      pullbackDiff (pointAlgHom h) (KaehlerDifferential.D ℚ _ (AdjoinRoot.of _ Polynomial.X)) := by
  rw [pullback_dX, omegaPull]

/-- **The `q`-expansion of the pulled-back invariant differential** is `θx · (2y + a₁x + a₃)⁻¹`. -/
theorem qExpDiff_omegaPull (x y : FQ M) :
    qExpDiff M (omegaPull A x y) =
      ((denomF A x y : LaurentSeries ℚ))⁻¹ * eulerOp (x : LaurentSeries ℚ) := by
  rw [omegaPull, qExpDiff_smul, qExpDiff_D, IntermediateField.coe_inv]

theorem coe_denomF (x y : FQ M) :
    ((denomF A x y : FQ M) : LaurentSeries ℚ) = omegaDenom A x y := by
  simp only [denomF, omegaDenom, cQ, IntermediateField.coe_add, IntermediateField.coe_mul]
  simp [two_mul]

/-- The coefficientwise inclusion `ℚ((q)) → ℂ((q))` as a ring map. -/
def toComplexHom : LaurentSeries ℚ →+* LaurentSeries ℂ where
  toFun := toComplexLaurent
  map_one' := by ext n; simp [HahnSeries.coeff_one]; split_ifs <;> simp
  map_mul' := toComplexLaurent_mul
  map_zero' := toComplexLaurent_zero
  map_add' x y := by ext n; simp

/-- **Clause (iv) of the print is the `q`-expansion of the pulled-back invariant differential**:
for `2y + a₁x + a₃ ≠ 0`, `PullbackIsMultiple A x y ĝ c` (i.e. `θx = c · ĝ · (2y + a₁x + a₃)`)
holds iff the `q`-expansion of the pull-back of `ω_A` along `(x, y)` is `c · ĝ` (times `dq/q`). -/
theorem pullbackIsMultiple_iff (x y : FQ M) (hden : denomF A x y ≠ 0) (ĝ : PowerSeries ℂ)
    (c : ℂ) :
    PullbackIsMultiple A x y ĝ c ↔
      toComplexLaurent (qExpDiff M (omegaPull A x y)) =
        HahnSeries.C c * HahnSeries.ofPowerSeries ℤ ℂ ĝ := by
  have hD : toComplexHom (omegaDenom A x y) ≠ 0 := by
    rw [← coe_denomF, map_ne_zero_iff _ toComplexLaurent_injective]
    exact_mod_cast hden
  have e : ∀ z, toComplexLaurent z = toComplexHom z := fun _ => rfl
  rw [qExpDiff_omegaPull, coe_denomF]
  unfold PullbackIsMultiple
  simp only [e, map_mul, map_inv₀]
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    rw [inv_mul_eq_iff_eq_mul₀ hD] at h
    rw [h]
    ring

end Pullback

end ZInQ.Contrib.CloudB3RC53.NewformS13
