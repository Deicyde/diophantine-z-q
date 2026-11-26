import ZInQKernel.Contrib.OneProof.RC.ModelGeneric4.QuotientFunctionField
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.P2M.Sol.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_veluQuotient2_Delta_ne_zero
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_exists_addMonoidHom_coe_eq_veluPointMap2
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_stepCurve_stepSubgroup_two_eq
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_veluGx_ne_zero_of_two_torsion
import ZInQKernel.Contrib.CloudB2X0Transitive.Vendor.AnthropicFLT.Theorems.Thm_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j

/-! # The order-two Vélu step as a map of function fields

The vendored order-two step `veluQuotient2` comes only with its point map `veluPointMap2`. Here the
same rational formulas `x ↦ x + G/(x - x₀)` and `y ↦ y - G(a₁(x - x₀) + y - y₀)/(x - x₀)²`
define a map of function fields, and its restriction of places is the vendored point map. This is
the missing ingredient for the composite at even level. -/

namespace WeierstrassCurve.ModelLevels.ModelGeneric4

open AlgebraicCurve Polynomial
open P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.WeierstrassCurve.Affine
open P2MW.S_WeierstrassCurve_exists_veluFunctionFieldHom_restrictAlong_placeOfPoint_eq_of_isAlgClosed.AlgebraicCurve.Place

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 400000
set_option linter.style.haveILetI false

attribute [-instance] WeierstrassCurve.Affine.CoordinateRing.moduleFinite
  WeierstrassCurve.Affine.instDecidableEqFunctionField WeierstrassCurve.Affine.CoordinateRing.isIntegral
  WeierstrassCurve.Affine.instIsScalarTowerPolynomialRatFuncFunctionField_definitions
  WeierstrassCurve.Affine.instAlgebraRatFuncFunctionField_definitions
  WeierstrassCurve.Affine.instIsScalarTowerRatFuncFunctionField_definitions

variable {F : Type} [Field F] [DecidableEq F] (W : WeierstrassCurve F) (x₀ y₀ : F)

/-- The generic first coordinate of the order-two Vélu map, `x + G/(x - x₀)`. -/
noncomputable def twoXFun : W.toAffine.FunctionField :=
  polyToFunctionField W.toAffine X +
    algebraMap F _ (W.veluGx x₀ y₀) / (polyToFunctionField W.toAffine X - algebraMap F _ x₀)

/-- The generic second coordinate of the order-two Vélu map,
`y - G(a₁(x - x₀) + y - y₀)/(x - x₀)²`. -/
noncomputable def twoYFun : W.toAffine.FunctionField :=
  yGen W.toAffine - algebraMap F _ (W.veluGx x₀ y₀) *
    (algebraMap F _ W.a₁ * (polyToFunctionField W.toAffine X - algebraMap F _ x₀) +
      yGen W.toAffine - algebraMap F _ y₀) /
    (polyToFunctionField W.toAffine X - algebraMap F _ x₀) ^ 2

omit [DecidableEq F] in
theorem veluQuotient2_map {K : Type} [Field K] (f : F →+* K) :
    (W.veluQuotient2 x₀ y₀).map f = (W.map f).veluQuotient2 (f x₀) (f y₀) := by
  ext <;> simp [veluQuotient2, veluGx, b₂, map_ofNat]

omit [DecidableEq F] in
theorem twoFun_equation (h2 : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    ((W.veluQuotient2 x₀ y₀).map (algebraMap F W.toAffine.FunctionField)).toAffine.Equation
      (twoXFun W x₀ y₀) (twoYFun W x₀ y₀) := by
  let φ := algebraMap F W.toAffine.FunctionField
  have hP := equation_map_polyToFunctionField_yGen (W := W.toAffine)
  have hQ' : (W.map φ).toAffine.Equation (φ x₀) (φ y₀) :=
    (W.toAffine.map_equation φ.injective x₀ y₀).mpr hQ
  have hgy' : (W.map φ).veluGy (φ x₀) (φ y₀) = 0 := by
    have : (W.map φ).veluGy (φ x₀) (φ y₀) = φ (W.veluGy x₀ y₀) := by
      simp [veluGy, map_ofNat]
    rw [this, hgy, map_zero]
  have hx : polyToFunctionField W.toAffine X ≠ φ x₀ := polyToFunctionField_X_ne_algebraMap x₀
  have h2' : (2 : W.toAffine.FunctionField) ≠ 0 := by
    rw [show (2 : W.toAffine.FunctionField) = φ 2 by simp [map_ofNat]]
    exact (map_ne_zero φ).mpr h2
  have key := (W.map φ).velu2_map_equation h2' hP hQ' hgy' hx
  rw [veluQuotient2_map]
  have hG : (W.map φ).veluGx (φ x₀) (φ y₀) = φ (W.veluGx x₀ y₀) := by
    simp [veluGx, map_ofNat]
  simp only [velu2X, velu2Y, hG, map_a₁] at key
  exact key

omit [DecidableEq F] in
theorem twoFun_eval₂_polynomial (h2 : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀)
    (hgy : W.veluGy x₀ y₀ = 0) :
    ((W.veluQuotient2 x₀ y₀).toAffine.polynomial).eval₂
        (Polynomial.aeval (twoXFun W x₀ y₀) : F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
        (twoYFun W x₀ y₀) = 0 := by
  have heq := twoFun_equation W x₀ y₀ h2 hQ hgy
  rw [WeierstrassCurve.Affine.equation_iff'] at heq
  simp only [map_a₁, map_a₂, map_a₃, map_a₄, map_a₆] at heq
  simp only [WeierstrassCurve.Affine.polynomial, eval₂_add, eval₂_sub, eval₂_mul, eval₂_pow,
    eval₂_X, eval₂_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_add, map_mul, map_pow,
    Polynomial.aeval_C, Polynomial.aeval_X]
  linear_combination heq

omit [DecidableEq F] in
/-- The generic first coordinate is transcendental: the generic abscissa is a root of a monic
quadratic over the algebra it generates. -/
theorem transcendental_twoXFun : Transcendental F (twoXFun W x₀ y₀) := by
  intro halg
  apply transcendental_polyToFunctionField_X (W := W.toAffine)
  have hint : _root_.IsIntegral F (twoXFun W x₀ y₀) := halg.isIntegral
  let S := Algebra.adjoin F ({twoXFun W x₀ y₀} : Set W.toAffine.FunctionField)
  have hS : Algebra.IsIntegral F S :=
    ⟨fun s => by
      have := adjoin_le_integralClosure hint s.2
      exact (isIntegral_algHom_iff S.val Subtype.val_injective).mp this⟩
  have hu : twoXFun W x₀ y₀ ∈ S := Algebra.subset_adjoin rfl
  have hd : polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField x₀ ≠ 0 :=
    sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap x₀)
  let p : S[X] := X ^ 2 + (C (-(⟨twoXFun W x₀ y₀, hu⟩ + algebraMap F S x₀)) * X +
    C (⟨twoXFun W x₀ y₀, hu⟩ * algebraMap F S x₀ + algebraMap F S (W.veluGx x₀ y₀)))
  have hmonic : p.Monic := monic_X_pow_add (by exact_mod_cast degree_linear_lt)
  have hroot : aeval (polyToFunctionField W.toAffine X) p = 0 := by
    simp only [p, map_add, map_mul, map_pow, aeval_X, aeval_C]
    change polyToFunctionField W.toAffine X ^ 2 + (-(twoXFun W x₀ y₀ +
      algebraMap F W.toAffine.FunctionField x₀) * polyToFunctionField W.toAffine X +
      (twoXFun W x₀ y₀ * algebraMap F W.toAffine.FunctionField x₀ +
      algebraMap F W.toAffine.FunctionField (W.veluGx x₀ y₀))) = 0
    simp only [twoXFun]
    field_simp
    ring
  have hxS : _root_.IsIntegral S (polyToFunctionField W.toAffine X) := ⟨p, hmonic, hroot⟩
  exact (isIntegral_trans _ hxS).isAlgebraic

variable {W x₀ y₀}
variable (h2 : (2 : F) ≠ 0) (hQ : W.toAffine.Equation x₀ y₀) (hgy : W.veluGy x₀ y₀ = 0)

omit [DecidableEq F] in
include h2 hQ hgy in
/-- The order-two Vélu map on coordinate rings. -/
noncomputable def twoCoordHom :
    (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing →ₐ[F] W.toAffine.FunctionField where
  __ := AdjoinRoot.lift
    (Polynomial.aeval (twoXFun W x₀ y₀) : F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
    (twoYFun W x₀ y₀) (twoFun_eval₂_polynomial W x₀ y₀ h2 hQ hgy)
  commutes' c := by
    show AdjoinRoot.lift _ _ (twoFun_eval₂_polynomial W x₀ y₀ h2 hQ hgy)
      (algebraMap F _ c) = algebraMap F W.toAffine.FunctionField c
    rw [CoordinateRing.algebraMap_eq_mk_C_C, AdjoinRoot.lift_mk, eval₂_C]
    exact Polynomial.aeval_C _ c

omit [DecidableEq F] in
theorem twoCoordHom_mk (g : Polynomial (Polynomial F)) :
    twoCoordHom h2 hQ hgy (WeierstrassCurve.Affine.CoordinateRing.mk
        (W.veluQuotient2 x₀ y₀).toAffine g) =
      g.eval₂ (Polynomial.aeval (twoXFun W x₀ y₀) : F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom
        (twoYFun W x₀ y₀) :=
  AdjoinRoot.lift_mk (twoFun_eval₂_polynomial W x₀ y₀ h2 hQ hgy) g

omit [DecidableEq F] in
theorem twoCoordHom_comp_algebraMap :
    (twoCoordHom h2 hQ hgy).toRingHom.comp
        (algebraMap F[X] (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing) =
      (Polynomial.aeval (twoXFun W x₀ y₀) : F[X] →ₐ[F] W.toAffine.FunctionField).toRingHom := by
  refine RingHom.ext fun q => ?_
  show twoCoordHom h2 hQ hgy (algebraMap F[X] _ q) = _
  rw [algebraMap_polynomial_eq_mk_C, twoCoordHom_mk, eval₂_C]

omit [DecidableEq F] in
theorem twoCoordHom_injective : Function.Injective (twoCoordHom h2 hQ hgy) := by
  have hker : RingHom.ker (twoCoordHom h2 hQ hgy).toRingHom = ⊥ := by
    haveI : Module.Finite F[X] (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing :=
      Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis
        (W.veluQuotient2 x₀ y₀).toAffine)
    refine Ideal.eq_bot_of_under_eq_bot (R := F[X]) ?_
    rw [Ideal.under_def, RingHom.comap_ker, twoCoordHom_comp_algebraMap,
      ← RingHom.injective_iff_ker_eq_bot]
    exact (injective_iff_map_eq_zero _).mpr fun q hq =>
      transcendental_iff.mp (transcendental_twoXFun W x₀ y₀) q hq
  exact (RingHom.injective_iff_ker_eq_bot (twoCoordHom h2 hQ hgy).toRingHom).mpr hker

/-- The order-two Vélu map on function fields. -/
noncomputable def twoFFHom :
    (W.veluQuotient2 x₀ y₀).toAffine.FunctionField →ₐ[F] W.toAffine.FunctionField :=
  IsFractionRing.liftAlgHom (twoCoordHom_injective h2 hQ hgy)

omit [DecidableEq F] in
theorem twoFFHom_algebraMap (r : (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing) :
    twoFFHom h2 hQ hgy (algebraMap _ (W.veluQuotient2 x₀ y₀).toAffine.FunctionField r) =
      twoCoordHom h2 hQ hgy r :=
  IsFractionRing.lift_algebraMap (twoCoordHom_injective h2 hQ hgy) r

omit [DecidableEq F] in
theorem twoFFHom_X :
    twoFFHom h2 hQ hgy (polyToFunctionField (W.veluQuotient2 x₀ y₀).toAffine X) =
      twoXFun W x₀ y₀ := by
  rw [polyToFunctionField_apply, twoFFHom_algebraMap, algebraMap_polynomial_eq_mk_C,
    twoCoordHom_mk, eval₂_C]
  exact Polynomial.aeval_X _

omit [DecidableEq F] in
theorem twoFFHom_Y :
    twoFFHom h2 hQ hgy (yGen (W.veluQuotient2 x₀ y₀).toAffine) = twoYFun W x₀ y₀ := by
  show twoFFHom h2 hQ hgy (algebraMap _ _ (WeierstrassCurve.Affine.CoordinateRing.mk
    (W.veluQuotient2 x₀ y₀).toAffine (Polynomial.X : Polynomial (Polynomial F)))) = _
  rw [twoFFHom_algebraMap, twoCoordHom_mk]
  exact eval₂_X _ _

omit [DecidableEq F] in
theorem isIntegral_X_twoFFHom :
    letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
      (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
    _root_.IsIntegral (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
      (polyToFunctionField W.toAffine X) := by
  letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
  let V := (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
  let u : V := polyToFunctionField (W.veluQuotient2 x₀ y₀).toAffine X
  have hd : polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField x₀ ≠ 0 :=
    sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap x₀)
  let p : V[X] := X ^ 2 + (C (-(u + algebraMap F V x₀)) * X +
    C (u * algebraMap F V x₀ + algebraMap F V (W.veluGx x₀ y₀)))
  have hu : algebraMap V W.toAffine.FunctionField u = twoXFun W x₀ y₀ := twoFFHom_X h2 hQ hgy
  have hc : ∀ c : F, algebraMap V W.toAffine.FunctionField (algebraMap F V c) =
      algebraMap F W.toAffine.FunctionField c := fun c => (twoFFHom h2 hQ hgy).commutes c
  have e1 : algebraMap V W.toAffine.FunctionField (-(u + algebraMap F V x₀)) =
      -(twoXFun W x₀ y₀ + algebraMap F W.toAffine.FunctionField x₀) := by
    change twoFFHom h2 hQ hgy _ = _
    rw [map_neg, map_add, twoFFHom_X, AlgHom.commutes]
  have e2 : algebraMap V W.toAffine.FunctionField
      (u * algebraMap F V x₀ + algebraMap F V (W.veluGx x₀ y₀)) =
      twoXFun W x₀ y₀ * algebraMap F W.toAffine.FunctionField x₀ +
        algebraMap F W.toAffine.FunctionField (W.veluGx x₀ y₀) := by
    change twoFFHom h2 hQ hgy _ = _
    rw [map_add, map_mul, twoFFHom_X, AlgHom.commutes, AlgHom.commutes]
  have hroot : aeval (polyToFunctionField W.toAffine X) p = 0 := by
    simp only [p, map_add, map_mul, map_pow, aeval_X, aeval_C, e1]
    rw [hu, hc, hc]
    simp only [twoXFun]
    field_simp
    ring
  exact ⟨p, monic_X_pow_add (by exact_mod_cast degree_linear_lt), hroot⟩

omit [DecidableEq F] in
theorem adjoin_X_yGen_eq_top_twoFFHom :
    letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
      (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
    IntermediateField.adjoin (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
        ({polyToFunctionField W.toAffine X, yGen W.toAffine} : Set W.toAffine.FunctionField) =
      ⊤ := by
  letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
  rw [eq_top_iff]
  rintro z -
  set L := IntermediateField.adjoin (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
    ({polyToFunctionField W.toAffine X, yGen W.toAffine} : Set W.toAffine.FunctionField)
  have hconst : ∀ c : F, algebraMap F W.toAffine.FunctionField c ∈ L := fun c => by
    rw [← (twoFFHom h2 hQ hgy).commutes c]; exact L.algebraMap_mem _
  have hxmem : polyToFunctionField W.toAffine X ∈ L :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)
  have hymem : yGen W.toAffine ∈ L :=
    IntermediateField.subset_adjoin _ _ (Set.mem_insert_of_mem _ rfl)
  have hpoly : ∀ q : F[X], polyToFunctionField W.toAffine q ∈ L := fun q => by
    induction q using Polynomial.induction_on' with
    | add f g hf hg => rw [map_add]; exact add_mem hf hg
    | monomial n c =>
        rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow, polyToFunctionField_C]
        exact mul_mem (hconst c) (pow_mem hxmem n)
  have hcr : ∀ r : W.toAffine.CoordinateRing,
      algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField r ∈ L := fun r => by
    obtain ⟨a, b, rfl⟩ := WeierstrassCurve.Affine.CoordinateRing.exists_smul_basis_eq r
    rw [algebraMap_smul_basis]
    exact add_mem (hpoly a) (mul_mem (hpoly b) hymem)
  obtain ⟨a, b, _, hab⟩ := IsFractionRing.div_surjective (A := W.toAffine.CoordinateRing) z
  rw [← hab]; exact div_mem (hcr a) (hcr b)

omit [DecidableEq F] in
theorem twoFFHom_finiteAlong : FiniteAlong F (twoFFHom h2 hQ hgy) := by
  letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
  show Module.Finite (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField
  have hxint := isIntegral_X_twoFFHom h2 hQ hgy
  set Lx := IntermediateField.adjoin (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
    ({polyToFunctionField W.toAffine X} : Set W.toAffine.FunctionField) with hLx
  haveI hxfd : FiniteDimensional (W.veluQuotient2 x₀ y₀).toAffine.FunctionField Lx :=
    IntermediateField.adjoin.finiteDimensional hxint
  have hyint : _root_.IsIntegral Lx (yGen W.toAffine) := by
    have hyFx : _root_.IsIntegral F[X] (yGen W.toAffine) := by
      haveI : Module.Finite F[X] W.toAffine.CoordinateRing :=
        Module.Finite.of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
      show _root_.IsIntegral F[X]
        (algebraMap W.toAffine.CoordinateRing W.toAffine.FunctionField
          (WeierstrassCurve.Affine.CoordinateRing.mk W.toAffine
            (Polynomial.X : Polynomial (Polynomial F))))
      exact ((Algebra.IsIntegral.of_finite F[X] W.toAffine.CoordinateRing).isIntegral _).map
        (IsScalarTower.toAlgHom F[X] W.toAffine.CoordinateRing W.toAffine.FunctionField)
    have halg : ∀ r : F[X], (algebraMap F[X] W.toAffine.FunctionField) r ∈ Lx := by
      intro r
      induction r using Polynomial.induction_on' with
      | add f g hf hg => rw [map_add]; exact add_mem hf hg
      | monomial n c =>
          rw [← C_mul_X_pow_eq_monomial, map_mul, map_pow,
            show algebraMap F[X] W.toAffine.FunctionField (C c)
              = algebraMap F W.toAffine.FunctionField c from rfl,
            show algebraMap F[X] W.toAffine.FunctionField X
              = polyToFunctionField W.toAffine X from rfl,
            ← (twoFFHom h2 hQ hgy).commutes c]
          exact mul_mem (IntermediateField.algebraMap_mem _ _)
            (pow_mem (IntermediateField.mem_adjoin_simple_self _ _) n)
    obtain ⟨q, hqmon, hq0⟩ := hyFx
    let φ : F[X] →+* Lx :=
      (algebraMap F[X] W.toAffine.FunctionField).codRestrict Lx.toSubring halg
    refine ⟨q.map φ, hqmon.map φ, ?_⟩
    rw [Polynomial.eval₂_map,
      show (algebraMap Lx W.toAffine.FunctionField).comp φ
          = algebraMap F[X] W.toAffine.FunctionField from RingHom.ext fun _ => rfl]
    exact hq0
  have hyint' : _root_.IsIntegral (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
      (yGen W.toAffine) :=
    haveI : Algebra.IsIntegral (W.veluQuotient2 x₀ y₀).toAffine.FunctionField Lx :=
      Algebra.IsIntegral.of_finite (W.veluQuotient2 x₀ y₀).toAffine.FunctionField Lx
    haveI : IsScalarTower (W.veluQuotient2 x₀ y₀).toAffine.FunctionField Lx
        W.toAffine.FunctionField := IntermediateField.isScalarTower_mid' Lx
    isIntegral_trans (R := (W.veluQuotient2 x₀ y₀).toAffine.FunctionField) (A := Lx)
      (yGen W.toAffine) hyint
  have hfd : FiniteDimensional (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
      (IntermediateField.adjoin (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
        ({polyToFunctionField W.toAffine X, yGen W.toAffine}
          : Set W.toAffine.FunctionField)) := by
    refine IntermediateField.finiteDimensional_adjoin fun z hz => ?_
    rcases hz with rfl | rfl
    · exact hxint
    · exact hyint'
  rw [adjoin_X_yGen_eq_top_twoFFHom h2 hQ hgy] at hfd
  exact (IntermediateField.topEquiv (F := (W.veluQuotient2 x₀ y₀).toAffine.FunctionField)
    (E := W.toAffine.FunctionField)).toLinearEquiv.finiteDimensional

omit [DecidableEq F] in
theorem twoFFHom_isIntegral : (twoFFHom h2 hQ hgy).toRingHom.IsIntegral := by
  letI : Algebra (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    (twoFFHom h2 hQ hgy).toRingHom.toAlgebra
  haveI : Module.Finite (W.veluQuotient2 x₀ y₀).toAffine.FunctionField W.toAffine.FunctionField :=
    twoFFHom_finiteAlong h2 hQ hgy
  exact fun z => (Algebra.IsIntegral.of_finite _ _).isIntegral z

section Ord

variable {K L : Type} [Field K] [Field L] [Algebra K L]

private theorem ord_pos_of_eq_mul (v : Place K L) {f a w : L} (hf : f = a * w) (hf0 : f ≠ 0)
    (ha : 0 < v.ord a) (hw : w ∈ v.toValuationSubring) : 0 < v.ord f := by
  have ha0 : a ≠ 0 := by rintro rfl; rw [zero_mul] at hf; exact hf0 hf
  have hw0 : w ≠ 0 := by rintro rfl; rw [mul_zero] at hf; exact hf0 hf
  rw [hf, v.ord_mul ha0 hw0]
  have := ord_nonneg_of_mem v hw
  omega

private theorem ord_pos_of_eq_add_mul (v : Place K L) {f a b A B : L}
    (hf : f = a * A + b * B) (hf0 : f ≠ 0) (ha : 0 < v.ord a) (hb : 0 < v.ord b)
    (hA : A ∈ v.toValuationSubring) (hB : B ∈ v.toValuationSubring) : 0 < v.ord f := by
  by_cases h1 : a * A = 0
  · rw [h1, zero_add] at hf
    exact ord_pos_of_eq_mul v hf hf0 hb hB
  by_cases h2 : b * B = 0
  · rw [h2, add_zero] at hf
    exact ord_pos_of_eq_mul v hf hf0 ha hA
  have hmin := min_ord_le_ord_add v (hf ▸ hf0)
  have p1 := ord_pos_of_eq_mul v rfl h1 ha hA
  have p2 := ord_pos_of_eq_mul v rfl h2 hb hB
  rw [hf]
  omega

private theorem inv_mem_of_ord_eq_zero (v : Place K L) {f : L} (hf : f ≠ 0) (h : v.ord f = 0) :
    f⁻¹ ∈ v.toValuationSubring :=
  mem_of_ord_nonneg v (inv_ne_zero hf) (by rw [v.ord_inv, h, neg_zero])

end Ord

section Seam

variable [IsAlgClosed F]

omit [DecidableEq F] [IsAlgClosed F] in
private theorem algebraMap_XClass (V : WeierstrassCurve F) (c : F) :
    algebraMap V.toAffine.CoordinateRing V.toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.XClass V.toAffine c) =
      polyToFunctionField V.toAffine X - algebraMap F V.toAffine.FunctionField c := by
  rw [← polyToFunctionField_C, ← map_sub]; rfl

omit [DecidableEq F] [IsAlgClosed F] in
private theorem algebraMap_YClass (V : WeierstrassCurve F) (c : F) :
    algebraMap V.toAffine.CoordinateRing V.toAffine.FunctionField
        (WeierstrassCurve.Affine.CoordinateRing.YClass V.toAffine (C c)) =
      yGen V.toAffine - algebraMap F V.toAffine.FunctionField c := by
  rw [WeierstrassCurve.Affine.CoordinateRing.YClass, map_sub, map_sub, yGen]
  congr 1

omit [DecidableEq F] [IsAlgClosed F] in
theorem twoFFHom_XClass (c : F) :
    twoFFHom h2 hQ hgy (algebraMap _ _
        (WeierstrassCurve.Affine.CoordinateRing.XClass (W.veluQuotient2 x₀ y₀).toAffine c)) =
      twoXFun W x₀ y₀ - algebraMap F W.toAffine.FunctionField c := by
  rw [algebraMap_XClass, map_sub, twoFFHom_X, AlgHom.commutes]

omit [DecidableEq F] [IsAlgClosed F] in
theorem twoFFHom_YClass (c : F) :
    twoFFHom h2 hQ hgy (algebraMap _ _
        (WeierstrassCurve.Affine.CoordinateRing.YClass (W.veluQuotient2 x₀ y₀).toAffine (C c))) =
      twoYFun W x₀ y₀ - algebraMap F W.toAffine.FunctionField c := by
  rw [algebraMap_YClass, map_sub, twoFFHom_Y, AlgHom.commutes]

omit [DecidableEq F] [IsAlgClosed F] in
include h2 hQ hgy in
theorem twoYFun_ne_algebraMap (c : F) : twoYFun W x₀ y₀ ≠ algebraMap F W.toAffine.FunctionField c := by
  intro h
  have hY : algebraMap _ (W.veluQuotient2 x₀ y₀).toAffine.FunctionField
      (WeierstrassCurve.Affine.CoordinateRing.YClass (W.veluQuotient2 x₀ y₀).toAffine (C c)) ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr
      (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero _)
  apply hY
  apply (twoFFHom h2 hQ hgy).toRingHom.injective
  change twoFFHom h2 hQ hgy _ = twoFFHom h2 hQ hgy 0
  rw [twoFFHom_YClass, h, sub_self, map_zero]

omit [DecidableEq F] [IsAlgClosed F] in
/-- At a place that is not finite, the first coordinate has a pole. -/
theorem twoXFun_notMem_of_not_isFinitePlace {v : Place F W.toAffine.FunctionField}
    (hv : ¬ IsFinitePlace v) : twoXFun W x₀ y₀ ∉ v.toValuationSubring := by
  intro h
  apply hv
  apply isFinitePlace_of_mem v
  have hδ := inv_X_sub_algebraMap_mem_of_not_isFinitePlace v hv x₀
  have hx : polyToFunctionField W.toAffine X = twoXFun W x₀ y₀ -
      algebraMap F _ (W.veluGx x₀ y₀) *
        (polyToFunctionField W.toAffine X - algebraMap F _ x₀)⁻¹ := by
    rw [twoXFun, div_eq_mul_inv]; ring
  rw [hx]
  exact sub_mem h (mul_mem (v.algebraMap_mem' _) hδ)

variable [W.IsElliptic]

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
/-- At a point with abscissa `x₀`, the first coordinate has a pole. -/
theorem twoXFun_notMem_placeOfEquation_of_eq [IsDedekindDomain W.toAffine.CoordinateRing]
    {r s : F} (hrs : W.toAffine.Equation r s) (hr : r = x₀) (hG : W.veluGx x₀ y₀ ≠ 0) :
    twoXFun W x₀ y₀ ∉ (placeOfEquation hrs).toValuationSubring := by
  intro h
  have hx := polyToFunctionField_X_mem_placeOfEquation hrs
  have hd : polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField x₀ ≠ 0 :=
    sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap x₀)
  have hG' : algebraMap F W.toAffine.FunctionField (W.veluGx x₀ y₀) ≠ 0 :=
    (_root_.map_ne_zero _).mpr hG
  have hinv : (polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField x₀)⁻¹ ∈
      (placeOfEquation hrs).toValuationSubring := by
    have hmem : algebraMap F _ (W.veluGx x₀ y₀) *
        (polyToFunctionField W.toAffine X - algebraMap F _ x₀)⁻¹ ∈
          (placeOfEquation hrs).toValuationSubring := by
      have : algebraMap F _ (W.veluGx x₀ y₀) *
          (polyToFunctionField W.toAffine X - algebraMap F _ x₀)⁻¹ =
          twoXFun W x₀ y₀ - polyToFunctionField W.toAffine X := by
        rw [twoXFun, div_eq_mul_inv]; ring
      rw [this]
      exact sub_mem h hx
    have : (polyToFunctionField W.toAffine X - algebraMap F _ x₀)⁻¹ =
        (algebraMap F _ (W.veluGx x₀ y₀))⁻¹ * (algebraMap F _ (W.veluGx x₀ y₀) *
          (polyToFunctionField W.toAffine X - algebraMap F _ x₀)⁻¹) := by
      field_simp
    rw [this, ← map_inv₀]
    exact mul_mem ((placeOfEquation hrs).algebraMap_mem' _) hmem
  have hpos : 0 < (placeOfEquation hrs).ord
      (polyToFunctionField W.toAffine X - algebraMap F W.toAffine.FunctionField x₀) := by
    have := (ord_polyToFunctionField_pos_iff hrs (X_sub_C_ne_zero x₀)).mpr (by simp [hr])
    rwa [map_sub, polyToFunctionField_C] at this
  have hnn := ord_nonneg_of_mem _ hinv
  rw [(placeOfEquation hrs).ord_inv] at hnn
  omega

omit [DecidableEq F] [W.IsElliptic] in
/-- Away from the abscissa `x₀`, the place of a point restricts to the place of its Vélu image. -/
theorem twoFFHom_restrict_placeOfEquation_of_ne [IsDedekindDomain W.toAffine.CoordinateRing]
    [IsDedekindDomain (W.veluQuotient2 x₀ y₀).toAffine.CoordinateRing]
    {r s : F} (hrs : W.toAffine.Equation r s) (hr : r ≠ x₀)
    (h' : (W.veluQuotient2 x₀ y₀).toAffine.Equation (W.velu2X x₀ y₀ r) (W.velu2Y x₀ y₀ r s)) :
    (placeOfEquation hrs).restrictAlong (twoFFHom h2 hQ hgy) (twoFFHom_isIntegral h2 hQ hgy) =
      placeOfEquation h' := by
  let v := placeOfEquation hrs
  have hδne : polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) x₀ ≠ 0 :=
    sub_ne_zero.mpr (polyToFunctionField_X_ne_algebraMap x₀)
  have hδ0 : (algebraMap F W.toAffine.FunctionField) r - (algebraMap F W.toAffine.FunctionField) x₀ ≠ 0 := by
    rw [← map_sub]; exact (_root_.map_ne_zero _).mpr (sub_ne_zero.mpr hr)
  have hδinv : (polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) x₀)⁻¹ ∈ v.toValuationSubring :=
    inv_mem_of_ord_eq_zero v hδne (ord_X_sub_const_placeOfEquation_of_ne hrs hr)
  have hδ0inv : ((algebraMap F W.toAffine.FunctionField) r - (algebraMap F W.toAffine.FunctionField) x₀)⁻¹ ∈ v.toValuationSubring := by
    rw [← map_sub, ← map_inv₀]; exact v.algebraMap_mem' _
  have hx := polyToFunctionField_X_mem_placeOfEquation hrs
  have hy := yGen_mem_placeOfEquation hrs
  have hc : ∀ c : F, (algebraMap F W.toAffine.FunctionField) c ∈ v.toValuationSubring := v.algebraMap_mem'
  have hXmem : twoXFun W x₀ y₀ ∈ v.toValuationSubring := by
    rw [twoXFun, div_eq_mul_inv]
    exact add_mem hx (mul_mem (hc _) hδinv)
  have hfin : IsFinitePlace (v.restrictAlong (twoFFHom h2 hQ hgy) (twoFFHom_isIntegral h2 hQ hgy)) :=
    isFinitePlace_of_mem _ (by rw [mem_restrictAlong_iff, twoFFHom_X]; exact hXmem)
  have hxpos : 0 < v.ord (polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) r) := by
    have := (ord_polyToFunctionField_pos_iff hrs (X_sub_C_ne_zero r)).mpr (by simp)
    rwa [map_sub, polyToFunctionField_C] at this
  have hypos : 0 < v.ord (yGen W.toAffine - (algebraMap F W.toAffine.FunctionField) s) := by
    have := (ord_placeOfEquation_pos_iff hrs
      (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero (W' := W.toAffine) (C s))).mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
    rwa [algebraMap_YClass] at this
  refine eq_placeOfEquation_of_le_centre hfin h' ?_
  rw [WeierstrassCurve.Affine.CoordinateRing.XYIdeal, Ideal.span_le]
  intro g hg
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
  rcases hg with rfl | rfl
  · rw [SetLike.mem_coe, hfin.mem_centre_iff_ord_ne_zero
      (WeierstrassCurve.Affine.CoordinateRing.XClass_ne_zero _),
      ord_restrictAlong_ne_zero_iff, twoFFHom_XClass]
    refine ne_of_gt (ord_pos_of_eq_mul v (a := polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) r)
      (w := 1 - (algebraMap F W.toAffine.FunctionField) (W.veluGx x₀ y₀) * ((polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) x₀)⁻¹ *
        ((algebraMap F W.toAffine.FunctionField) r - (algebraMap F W.toAffine.FunctionField) x₀)⁻¹)) ?_ ?_ hxpos ?_)
    · simp only [twoXFun, velu2X, map_add, map_div₀, map_sub]
      field_simp
      ring
    · exact sub_ne_zero.mpr fun h =>
        transcendental_twoXFun W x₀ y₀ (h ▸ isAlgebraic_algebraMap _)
    · exact sub_mem (one_mem _) (mul_mem (hc _) (mul_mem hδinv hδ0inv))
  · rw [SetLike.mem_coe, hfin.mem_centre_iff_ord_ne_zero
      (WeierstrassCurve.Affine.CoordinateRing.YClass_ne_zero _),
      ord_restrictAlong_ne_zero_iff, twoFFHom_YClass]
    refine ne_of_gt (ord_pos_of_eq_add_mul v (a := yGen W.toAffine - (algebraMap F W.toAffine.FunctionField) s)
      (b := polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) r)
      (A := 1 - (algebraMap F W.toAffine.FunctionField) (W.veluGx x₀ y₀) * (polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) x₀)⁻¹ ^ 2)
      (B := -(algebraMap F W.toAffine.FunctionField) (W.veluGx x₀ y₀) * ((algebraMap F W.toAffine.FunctionField) W.a₁ * ((algebraMap F W.toAffine.FunctionField) r - (algebraMap F W.toAffine.FunctionField) x₀) ^ 2 -
        ((algebraMap F W.toAffine.FunctionField) W.a₁ * ((algebraMap F W.toAffine.FunctionField) r - (algebraMap F W.toAffine.FunctionField) x₀) + (algebraMap F W.toAffine.FunctionField) s - (algebraMap F W.toAffine.FunctionField) y₀) * ((polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) x₀) +
          ((algebraMap F W.toAffine.FunctionField) r - (algebraMap F W.toAffine.FunctionField) x₀))) * ((polyToFunctionField W.toAffine X - (algebraMap F W.toAffine.FunctionField) x₀)⁻¹ ^ 2 *
            ((algebraMap F W.toAffine.FunctionField) r - (algebraMap F W.toAffine.FunctionField) x₀)⁻¹ ^ 2)) ?_ ?_ hypos hxpos ?_ ?_)
    · simp only [twoYFun, velu2Y, map_add, map_div₀, map_sub, map_mul, map_pow]
      field_simp
      ring
    · exact sub_ne_zero.mpr (twoYFun_ne_algebraMap h2 hQ hgy _)
    · exact sub_mem (one_mem _) (mul_mem (hc _) (pow_mem hδinv 2))
    · refine mul_mem (mul_mem (neg_mem (hc _)) (sub_mem (mul_mem (hc _)
        (pow_mem (sub_mem (hc _) (hc _)) 2)) (mul_mem (sub_mem (add_mem (mul_mem (hc _)
          (sub_mem (hc _) (hc _))) (hc _)) (hc _)) (add_mem (sub_mem hx (hc _))
            (sub_mem (hc _) (hc _)))))) (mul_mem (pow_mem hδinv 2) (pow_mem hδ0inv 2))

omit [DecidableEq F] [IsAlgClosed F] [W.IsElliptic] in
theorem twoFFHom_restrict_infinite [W.IsElliptic] [GenusOnePlaceGate W.toAffine]
    [GenusOnePlaceGate.IsCentred W.toAffine]
    [(W.veluQuotient2 x₀ y₀).IsElliptic] [GenusOnePlaceGate (W.veluQuotient2 x₀ y₀).toAffine]
    [GenusOnePlaceGate.IsCentred (W.veluQuotient2 x₀ y₀).toAffine] [IsAlgClosed F]
    [DecidableEq F] :
    (InfinitePlace.place : Place F W.toAffine.FunctionField).restrictAlong (twoFFHom h2 hQ hgy)
        (twoFFHom_isIntegral h2 hQ hgy) =
      (InfinitePlace.place : Place F (W.veluQuotient2 x₀ y₀).toAffine.FunctionField) := by
  haveI := WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.veluQuotient2 x₀ y₀)
  refine InfinitePlace.eq_of_not_isFinitePlace _ ?_
  intro hfin
  refine twoXFun_notMem_of_not_isFinitePlace (W := W) (x₀ := x₀) (y₀ := y₀)
    InfinitePlace.not_isFinitePlace ?_
  rw [← twoFFHom_X h2 hQ hgy, ← mem_restrictAlong_iff, polyToFunctionField_apply]
  exact hfin _

/-- **The order-two seam.** With the fixed centred gates, the place of every point restricts along
the order-two Vélu map of function fields to the place of its image under the vendored point map
`veluPointMap2`. -/
theorem twoFFHom_seam [CharZero F]
    (hΔ : (W.veluQuotient2 x₀ y₀).Δ ≠ 0) (P : W.toAffine.Point) :
    haveI : (W.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
    (pointPlace W P).restrictAlong (twoFFHom h2 hQ hgy) (twoFFHom_isIntegral h2 hQ hgy) =
      pointPlace (W.veluQuotient2 x₀ y₀) (veluPointMap2 h2 hQ hgy hΔ P) := by
  haveI hV : (W.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  haveI := WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain W
  haveI := WeierstrassCurve.Affine.CoordinateRing.isDedekindDomain (W.veluQuotient2 x₀ y₀)
  letI := gate W
  haveI := gate_isCentred W
  letI := gate (W.veluQuotient2 x₀ y₀)
  haveI := gate_isCentred (W.veluQuotient2 x₀ y₀)
  change Place.restrictAlong _ _ (placeOfPoint P) = placeOfPoint _
  have hG : W.veluGx x₀ y₀ ≠ 0 := W.veluGx_ne_zero_of_two_torsion W.isUnit_Δ.ne_zero hQ hgy
  cases P with
  | zero =>
      rw [veluPointMap2_zero, placeOfPoint_zero, placeOfPoint_zero]
      exact twoFFHom_restrict_infinite h2 hQ hgy
  | some r s h =>
      by_cases hr : r = x₀
      · rw [veluPointMap2_some_of_eq _ _ _ _ h hr, placeOfPoint_some, placeOfPoint_zero]
        refine InfinitePlace.eq_of_not_isFinitePlace _ ?_
        intro hfin
        refine twoXFun_notMem_placeOfEquation_of_eq (W := W) (y₀ := y₀) h.1 hr hG ?_
        rw [← twoFFHom_X h2 hQ hgy, ← mem_restrictAlong_iff, polyToFunctionField_apply]
        exact hfin _
      · rw [veluPointMap2_some_of_ne _ _ _ _ h hr, placeOfPoint_some, placeOfPoint_some]
        exact twoFFHom_restrict_placeOfEquation_of_ne h2 hQ hgy h.1 hr _

end Seam

open P2MW.S_WeierstrassCurve_bijOn_cyclicQuotientJ_isRoot_modularPolynomial_of_transcendental_j.P2MKcKI
  in
/-- The order-two step of the vendored quotient is induced by a function-field map whose
restriction of places is the vendored order-two Vélu map. -/
theorem stepSeam_two {k : Type} [Field k] [DecidableEq k] [IsAlgClosed k] [CharZero k] :
    StepSeam (k := k) 2 := by
  intro E _ H _ _ hdvd
  have h2 : (2 : k) ≠ 0 := two_ne_zero
  let := Fintype.ofFinite H
  obtain ⟨q, hq⟩ := exists_prime_addOrderOf_dvd_card (G := H) 2
    (by rwa [Fintype.card_eq_nat_card])
  have hQ2 : addOrderOf (q : E.toAffine.Point) = 2 :=
    (addOrderOf_injective H.subtype Subtype.coe_injective q).trans hq
  have hQ0 : (q : E.toAffine.Point) ≠ 0 := by
    intro h0; rw [h0, addOrderOf_zero] at hQ2; omega
  obtain ⟨x₀, y₀, hns, hqe⟩ : ∃ x₀ y₀ h, (q : E.toAffine.Point) = .some x₀ y₀ h := by
    rcases hqP : (q : E.toAffine.Point) with _ | ⟨x₀, y₀, h⟩
    · exact absurd hqP hQ0
    · exact ⟨x₀, y₀, h, rfl⟩
  have hgy : E.veluGy x₀ y₀ = 0 := by
    have h2Q : (2 : ℕ) • (q : E.toAffine.Point) = 0 := hQ2 ▸ addOrderOf_nsmul_eq_zero _
    rw [two_nsmul, hqe, ← eq_neg_iff_add_eq_zero, WeierstrassCurve.Affine.Point.neg_some] at h2Q
    have hy := (WeierstrassCurve.Affine.Point.some.inj h2Q).2
    rw [WeierstrassCurve.Affine.negY] at hy
    rw [veluGy]
    linear_combination -hy
  have hΔ := veluQuotient2_Delta_ne_zero E.isUnit_Δ.ne_zero hns.1 hgy
  haveI hV : (E.veluQuotient2 x₀ y₀).IsElliptic := ⟨isUnit_iff_ne_zero.mpr hΔ⟩
  obtain ⟨φ, hφ⟩ := E.exists_addMonoidHom_coe_eq_veluPointMap2 h2 hns.1 hgy hΔ
  have hQH : (WeierstrassCurve.Affine.Point.some x₀ y₀ hns : E.toAffine.Point) ∈ H :=
    hqe ▸ q.property
  have hbridge := E.stepCurve_stepSubgroup_two_eq h2 H hns hQH hgy hΔ φ hφ
  have hker : φ.ker = AddSubgroup.zmultiples (WeierstrassCurve.Affine.Point.some x₀ y₀ hns) := by
    rw [← hqe]
    ext P
    rw [mem_ker_veluPointMap2 E h2 hns.1 hgy hΔ φ hφ]
    have hord : addOrderOf (q : E.toAffine.Point) = 2 := hQ2
    constructor
    · rintro (rfl | hP)
      · exact AddSubgroup.zero_mem _
      · rw [hP, ← hqe]; exact AddSubgroup.mem_zmultiples _
    · intro hP
      obtain ⟨m, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 hP
      have hk : (m % 2) • (q : E.toAffine.Point) = m • (q : E.toAffine.Point) := by
        have := mod_addOrderOf_zsmul (q : E.toAffine.Point) m
        rwa [hord, Nat.cast_ofNat] at this
      rcases Int.emod_two_eq_zero_or_one m with h | h
      · left; rw [← hk, h, zero_smul]
      · right; rw [← hk, h, one_smul, hqe]
  have hseam : IsSeam (twoFFHom h2 hns.1 hgy) (twoFFHom_isIntegral h2 hns.1 hgy) φ := by
    intro P
    rw [show φ P = veluPointMap2 h2 hns.1 hgy hΔ P from congrFun hφ P]
    exact twoFFHom_seam h2 hns.1 hgy hΔ P
  have result (s : Σ V : WeierstrassCurve k, AddSubgroup V.toAffine.Point)
      (hs : s = ⟨E.veluQuotient2 x₀ y₀, H.map φ⟩) :
      ∃ _ : s.1.IsElliptic,
        ∃ (ι : s.1.toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
          (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
          ∃ f : E.toAffine.Point →+ s.1.toAffine.Point,
            f.ker ≤ H ∧ Nat.card f.ker = 2 ∧ H.map f = s.2 ∧ IsSeam ι hι f := by
    subst hs
    refine ⟨hV, twoFFHom h2 hns.1 hgy, twoFFHom_isIntegral h2 hns.1 hgy,
      twoFFHom_finiteAlong h2 hns.1 hgy, φ, ?_, ?_, rfl, hseam⟩
    · rw [hker]; exact AddSubgroup.zmultiples_le.mpr hQH
    · rw [hker, Nat.card_zmultiples, ← hqe, hQ2]
  exact result _ hbridge

/-- **The composite at every level.** The vendored iterated Vélu quotient by a cyclic subgroup of
any order is induced by a map of function fields whose restriction of places is a point
homomorphism with kernel exactly that subgroup. -/
theorem exists_quotientSeam {k : Type} [Field k] [DecidableEq k] [IsAlgClosed k] [CharZero k]
    (n : ℕ) (hn : n ≠ 0)
    (E : WeierstrassCurve k) [E.IsElliptic] (H : AddSubgroup E.toAffine.Point)
    (hH : IsAddCyclic H ∧ Nat.card H = n) :
    ∃ _ : (E.cyclicQuotientCurve H n).IsElliptic,
      ∃ (ι : (E.cyclicQuotientCurve H n).toAffine.FunctionField →ₐ[k] E.toAffine.FunctionField)
        (hι : ι.toRingHom.IsIntegral), FiniteAlong k ι ∧
        ∃ g : E.toAffine.Point →+ (E.cyclicQuotientCurve H n).toAffine.Point,
          g.ker = H ∧ IsSeam ι hι g :=
  exists_quotientSeam_of_steps n hn (fun ℓ hℓ _ => by
    by_cases h2 : ℓ = 2
    · subst h2; exact stepSeam_two
    · exact stepSeam_of_odd hℓ h2) E H hH

#print axioms twoFun_equation
#print axioms transcendental_twoXFun
#print axioms twoFFHom
#print axioms twoFFHom_finiteAlong
#print axioms twoFFHom_isIntegral
#print axioms twoFFHom_restrict_placeOfEquation_of_ne
#print axioms twoFFHom_seam
#print axioms stepSeam_two
#print axioms exists_quotientSeam

end WeierstrassCurve.ModelLevels.ModelGeneric4
