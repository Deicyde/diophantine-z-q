import ZInQKernel.Contrib.TauCeti.AlgebraicGeometry.EllipticCurve.Affine.InvariantDifferential
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.FieldSimp

/-!
# The invariant differential in the parameter at infinity

Let `x, y` be elements of a field `F` over `k` satisfying a Weierstrass equation
`y² + a₁xy + a₃y = x³ + a₂x² + a₄x + a₆` with coefficients in `k`, with `y ≠ 0` and
`2y + a₁x + a₃ ≠ 0`. Put `z = -x/y`, `w = -1/y` and

`u = 1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²` (`localUnit`).

If `u ≠ 0`, then in `Ω[F/k]` (`invariant_eq_localUnit_inv_smul`)

`dx / (2y + a₁x + a₃) = u⁻¹ • dz`.

The proof differentiates the Weierstrass equation,
`(2y + a₁x + a₃) dy = (3x² + 2a₂x + a₄ - a₁y) dx`, and uses
`u y² = x(3x² + 2a₂x + a₄ - a₁y) - y(2y + a₁x + a₃)`, which is the equation itself.
Since `z` and `w` vanish at the point at infinity, `u` takes the value `1` there
(`localUnit_retraction`): the invariant differential is `dz` at the origin.

The file also defines Kähler functoriality of an isomorphism of algebras (`kaehlerTransport`) and
computes the transport of the invariant differential of a Weierstrass curve along an isomorphism
of its function field (`kaehlerTransport_invariantDifferential`).

Locator: Silverman, *The Arithmetic of Elliptic Curves*, second edition, III.1.5 and IV.1 (the
expansion `ω = (1 + a₁z + ⋯) dz` in the parameter `z = -x/y`).
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.HodgeLineBinding

open KaehlerDifferential

variable {k : Type*} [Field k]

/-- DEFINITION. The local unit `u(z, w) = 1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²` of a Weierstrass
curve, a polynomial in the parameters `z = -x/y`, `w = -1/y` at infinity, in any `k`-algebra.
Locator: Silverman, IV.1. -/
def localUnit (W : WeierstrassCurve k) {R : Type*} [CommRing R] [Algebra k R] (z w : R) : R :=
  1 - algebraMap k R W.a₁ * z - algebraMap k R W.a₂ * z ^ 2 - 2 * algebraMap k R W.a₃ * w -
    2 * algebraMap k R W.a₄ * (z * w) - 3 * algebraMap k R W.a₆ * w ^ 2

/-- THEOREM (proved). A ring homomorphism fixing the constants maps the local unit to the local
unit of the images. Locator: `localUnit`. -/
theorem map_localUnit (W : WeierstrassCurve k) {R S : Type*} [CommRing R] [CommRing S]
    [Algebra k R] [Algebra k S] (f : R →+* S)
    (hf : ∀ c : k, f (algebraMap k R c) = algebraMap k S c) (z w : R) :
    f (localUnit W z w) = localUnit W (f z) (f w) := by
  simp only [localUnit, map_sub, map_mul, map_pow, map_one, map_ofNat, hf]

/-- THEOREM (proved). If `z` and `w` have value `0` under a retraction of the constants, the
local unit has value `1`. Locator: `localUnit`. -/
theorem localUnit_retraction (W : WeierstrassCurve k) {R : Type*} [CommRing R] [Algebra k R]
    (ρ : R →+* k) (hρ : ∀ c : k, ρ (algebraMap k R c) = c) {z w : R} (hz : ρ z = 0)
    (hw : ρ w = 0) : ρ (localUnit W z w) = 1 := by
  simp only [localUnit, map_sub, map_mul, map_pow, map_one, map_ofNat, hρ, hz, hw]
  ring

/-- THEOREM (proved). Differentiating the Weierstrass equation:
`(2y + a₁x + a₃) dy = (3x² + 2a₂x + a₄ - a₁y) dx`. Locator: Silverman, III.1.5. -/
theorem kaehler_weierstrass_relation {F : Type*} [Field F] [Algebra k F] (W : WeierstrassCurve k)
    (x y : F)
    (heq : y ^ 2 + algebraMap k F W.a₁ * x * y + algebraMap k F W.a₃ * y =
      x ^ 3 + algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x + algebraMap k F W.a₆) :
    (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) • D k F y =
      (3 * x ^ 2 + 2 * algebraMap k F W.a₂ * x + algebraMap k F W.a₄ -
        algebraMap k F W.a₁ * y) • D k F x := by
  have h := congrArg (D k F) heq
  simp only [map_add, Derivation.leibniz, Derivation.leibniz_pow, Derivation.map_algebraMap,
    smul_zero, add_zero] at h
  linear_combination (norm := module) h

/-- THEOREM (proved). The local unit times `y²`: `u y² = y² + a₁xy - a₂x² + 2a₃y - 2a₄x - 3a₆`.
Locator: `localUnit`. -/
theorem localUnit_mul_sq {F : Type*} [Field F] [Algebra k F] (W : WeierstrassCurve k) (x y : F)
    (hy : y ≠ 0) :
    localUnit W (-x / y) (-1 / y) * y ^ 2 =
      y ^ 2 + algebraMap k F W.a₁ * x * y - algebraMap k F W.a₂ * x ^ 2 +
        2 * algebraMap k F W.a₃ * y - 2 * algebraMap k F W.a₄ * x - 3 * algebraMap k F W.a₆ := by
  unfold localUnit
  field_simp
  ring

/-- THEOREM (proved). **The invariant differential in the parameter at infinity**:
`dx / (2y + a₁x + a₃) = u⁻¹ • d(-x/y)` in `Ω[F/k]`. Locator: Silverman, IV.1; the relation
`kaehler_weierstrass_relation` and `localUnit_mul_sq`. -/
theorem invariant_eq_localUnit_inv_smul {F : Type*} [Field F] [Algebra k F]
    (W : WeierstrassCurve k) (x y : F)
    (heq : y ^ 2 + algebraMap k F W.a₁ * x * y + algebraMap k F W.a₃ * y =
      x ^ 3 + algebraMap k F W.a₂ * x ^ 2 + algebraMap k F W.a₄ * x + algebraMap k F W.a₆)
    (hy : y ≠ 0) (hP : 2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃ ≠ 0)
    (hu : localUnit W (-x / y) (-1 / y) ≠ 0) :
    (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃)⁻¹ • D k F x =
      (localUnit W (-x / y) (-1 / y))⁻¹ • D k F (-x / y) := by
  have hrel := kaehler_weierstrass_relation W x y heq
  have key : localUnit W (-x / y) (-1 / y) * y ^ 2 =
      x * (3 * x ^ 2 + 2 * algebraMap k F W.a₂ * x + algebraMap k F W.a₄ -
        algebraMap k F W.a₁ * y) - y * (2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃) := by
    rw [localUnit_mul_sq W x y hy]
    linear_combination 3 * heq
  generalize 2 * y + algebraMap k F W.a₁ * x + algebraMap k F W.a₃ = P at hrel hP key ⊢
  generalize 3 * x ^ 2 + 2 * algebraMap k F W.a₂ * x + algebraMap k F W.a₄ -
    algebraMap k F W.a₁ * y = Q at hrel key
  generalize localUnit W (-x / y) (-1 / y) = u at hu key ⊢
  have hDy : D k F y = (P⁻¹ * Q) • D k F x := by
    rw [mul_smul, ← hrel, smul_smul, inv_mul_cancel₀ hP, one_smul]
  have hDz : D k F (-x / y) = (-(y⁻¹ ^ 2) * (y - x * (P⁻¹ * Q))) • D k F x := by
    rw [neg_div, map_neg, Derivation.leibniz_div, hDy]
    module
  rw [hDz, smul_smul]
  congr 1
  have h2 : u⁻¹ * (-(y⁻¹ ^ 2) * (y - x * (P⁻¹ * Q))) - P⁻¹ =
      u⁻¹ * y⁻¹ ^ 2 * P⁻¹ * (x * Q - y * P - u * y ^ 2) := by
    field_simp
    ring
  rw [key, sub_self, mul_zero, sub_eq_zero] at h2
  exact h2.symm

section Transport

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- DEFINITION. Kähler functoriality of an isomorphism of `k`-algebras `e : A ≃ B`:
`Ω[A/k] → Ω[B/k]`, `a • D b ↦ e(a) • D (e b)`. Locator: Mathlib, `KaehlerDifferential.map`. -/
def kaehlerTransport (e : A ≃ₐ[k] B) : Ω[A⁄k] →ₗ[k] Ω[B⁄k] :=
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun c => (e.commutes c).symm
  (KaehlerDifferential.map k k A B).restrictScalars k

/-- THEOREM (proved). `kaehlerTransport e (D a) = D (e a)`. Locator: Mathlib,
`KaehlerDifferential.map_D`. -/
theorem kaehlerTransport_D (e : A ≃ₐ[k] B) (a : A) :
    kaehlerTransport e (D k A a) = D k B (e a) := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun c => (e.commutes c).symm
  exact KaehlerDifferential.map_D k k A B a

/-- THEOREM (proved). `kaehlerTransport e (a • η) = e a • kaehlerTransport e η`. Locator:
Mathlib, `KaehlerDifferential.map` is `A`-linear. -/
theorem kaehlerTransport_smul (e : A ≃ₐ[k] B) (a : A) (η : Ω[A⁄k]) :
    kaehlerTransport e (a • η) = e a • kaehlerTransport e η := by
  letI : Algebra A B := e.toRingHom.toAlgebra
  haveI : IsScalarTower k A B := IsScalarTower.of_algebraMap_eq fun c => (e.commutes c).symm
  change KaehlerDifferential.map k k A B (a • η) = e a • KaehlerDifferential.map k k A B η
  rw [map_smul]
  exact (algebraMap_smul B a _).symm

end Transport

/-- THEOREM (proved). The generic point of a Weierstrass curve satisfies its equation, written
with the constants of the function field. Locator: Tau Ceti,
`WeierstrassCurve.Affine.equation_genericX_genericY`. -/
theorem genericPoint_equation (W : WeierstrassCurve k) :
    W.toAffine.genericY ^ 2 +
        algebraMap k W.toAffine.FunctionField W.a₁ * W.toAffine.genericX * W.toAffine.genericY +
        algebraMap k W.toAffine.FunctionField W.a₃ * W.toAffine.genericY =
      W.toAffine.genericX ^ 3 +
        algebraMap k W.toAffine.FunctionField W.a₂ * W.toAffine.genericX ^ 2 +
        algebraMap k W.toAffine.FunctionField W.a₄ * W.toAffine.genericX +
        algebraMap k W.toAffine.FunctionField W.a₆ :=
  (WeierstrassCurve.Affine.equation_iff _ _).mp W.toAffine.equation_genericX_genericY

/-- THEOREM (proved). The images of the generic coordinates under a `k`-algebra map satisfy the
Weierstrass equation. Locator: `genericPoint_equation`. -/
theorem genericPoint_equation_map {F : Type*} [Field F] [Algebra k F] (W : WeierstrassCurve k)
    (e : W.toAffine.FunctionField →ₐ[k] F) :
    e W.toAffine.genericY ^ 2 +
        algebraMap k F W.a₁ * e W.toAffine.genericX * e W.toAffine.genericY +
        algebraMap k F W.a₃ * e W.toAffine.genericY =
      e W.toAffine.genericX ^ 3 + algebraMap k F W.a₂ * e W.toAffine.genericX ^ 2 +
        algebraMap k F W.a₄ * e W.toAffine.genericX + algebraMap k F W.a₆ := by
  have h := congrArg e (genericPoint_equation W)
  simpa only [map_add, map_mul, map_pow, AlgHom.commutes] using h

/-- THEOREM (proved). The transport of the invariant differential along an isomorphism `e` of
the function field is `dx' / (2y' + a₁x' + a₃)` for the transported coordinates `x' = e x`,
`y' = e y`. Locator: `WeierstrassCurve.Affine.invariantDifferential_def`, `kaehlerTransport_D`
and `kaehlerTransport_smul`. -/
theorem kaehlerTransport_invariantDifferential {F : Type*} [Field F] [Algebra k F]
    (W : WeierstrassCurve k) (e : W.toAffine.FunctionField ≃ₐ[k] F) :
    kaehlerTransport e (WeierstrassCurve.Affine.invariantDifferential W.toAffine) =
      (2 * e W.toAffine.genericY + algebraMap k F W.a₁ * e W.toAffine.genericX +
        algebraMap k F W.a₃)⁻¹ • D k F (e W.toAffine.genericX) := by
  rw [WeierstrassCurve.Affine.invariantDifferential_def, kaehlerTransport_smul,
    kaehlerTransport_D, map_inv₀, WeierstrassCurve.Affine.invariantDifferentialDenom_def]
  congr 2
  simp only [map_add, map_mul, map_ofNat, AlgEquiv.commutes]

end ZInQ.Contrib.RC53Assist.HodgeLineBinding
