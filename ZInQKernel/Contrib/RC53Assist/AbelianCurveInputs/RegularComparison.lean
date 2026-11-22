/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Copyright (c) 2026 Axel Delaval, Jie Xu, and Shitan Xu.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import ZInQKernel.Contrib.RC53Assist.AbelianCurve.BirationalComparison
import TauCeti.FieldTheory.FunctionField.Differential.Cotrace
import TauCeti.FieldTheory.FunctionField.Differential.LocalOrder
import TauCeti.FieldTheory.FunctionField.RiemannRoch.RatFunc
import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Regular differentials and local lattices

The normalized comparison uses the cotrace of the rational differential with
`div(dX) = -2[∞]` and residue `-1` on `X⁻¹` at infinity. Its normalization and
basis construction follow
`ZInQKernel/Contrib/RC53Assist/InvariantDifferential/DivisorZero.lean`.

Regularity is tested separately at each place. The sheaf stalk calculation,
generic restriction, proper place coverage, and unique global gluing are proved.
The remaining field facts are `LocalUniformizerBasis`, `UniformizerResidueOrder`,
and `SeparatingCotraceChainRule`. The last fact is needed for independence of the
separating parameter and hence parameter-free naturality. Naturality with the
parameter transported by an actual curve isomorphism is proved without it.
The actual global sheaf pullback, not a dimension-chosen equivalence, is used.

Locators: Silverman, *The Arithmetic of Elliptic Curves*, Chapter II, §§4–5;
Stichtenoth, *Algebraic Function Fields and Codes*, second edition, §§I.5
and I.7. The latter gives the repartition formulation and is an auxiliary
reference, not a manuscript citation.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs

open AlgebraicGeometry CategoryTheory Limits Opposite TopologicalSpace
open TauCeti TauCeti.AlgebraicGeometry Polynomial Module KaehlerDifferential
open scoped IntermediateField

/-- THEOREM. The divisor `-2[∞]` is canonical on the rational function field.
Locator: `DivisorZero.lean`, `rational_canonical`; Stichtenoth §I.5. -/
private theorem rational_canonical (k : Type*) [Field k] :
    (Place.orderSystem (IsFunctionField.ratFunc k)).divisorClass
        ((-2 : ℤ) • WeilDivisor.ofPoint (Place.infty k)) =
      canonicalClass (IsFunctionField.ratFunc k) isIntegrallyClosedIn_ratFunc := by
  rw [divisorClass_eq_canonicalClass_iff, genus_ratFunc]
  refine ⟨?_, Nat.zero_le _⟩
  rw [Divisor.degree_zsmul, Divisor.degree_ofPoint, Place.degree_infty]
  norm_num

/-- THEOREM. The rational differential admits the prescribed divisor and residue.
Locator: `DivisorZero.lean`, `exists_normalized_rational`; Stichtenoth §I.5. -/
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

/-- DEFINITION. The rational differential with the prescribed normalization.
Locator: `DivisorZero.lean`, `rationalDifferential`. -/
private def rationalDifferential (k : Type*) [Field k] :
    Module.Dual k ↥(repartitionSpace k (RatFunc k)) :=
  (exists_normalized_rational k).choose

/-- THEOREM. The normalized rational differential is a Weil differential.
Locator: `exists_normalized_rational` above. -/
private theorem rationalDifferential_mem (k : Type*) [Field k] :
    rationalDifferential k ∈ weilDifferentialSpace k (RatFunc k) :=
  (exists_normalized_rational k).choose_spec.1

/-- THEOREM. The prescribed residue is `-1`.
Locator: `exists_normalized_rational` above. -/
private theorem rationalDifferential_normalization (k : Type*) [Field k] :
    repartitionDualComponent (rationalDifferential k) (Place.infty k)
      (RatFunc.X : RatFunc k)⁻¹ = -1 :=
  (exists_normalized_rational k).choose_spec.2.2

/-- THEOREM. The normalized rational differential is nonzero.
Locator: `DivisorZero.lean`, `rationalDifferential_ne_zero`. -/
private theorem rationalDifferential_ne_zero (k : Type*) [Field k] :
    rationalDifferential k ≠ 0 := by
  intro h
  have := rationalDifferential_normalization k
  rw [h, repartitionDualComponent_apply, LinearMap.zero_apply, eq_comm, neg_eq_zero] at this
  exact one_ne_zero this

variable {k F : Type*} [Field k] [Field F] [Algebra k F] {x : F}

/-- DEFINITION. The cotrace differential attached to a separating parameter.
Locator: `DivisorZero.lean`, `differentialOfSeparating`; Stichtenoth §I.5. -/
def differentialOfSeparating (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    ↥(weilDifferentialSpace k F) :=
  letI := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
    ⟨rationalDifferential k, rationalDifferential_mem k⟩

/-- THEOREM. Cotrace does not annihilate the normalized separating differential.
Locator: `DivisorZero.lean`, `differentialOfSeparating_ne_zero`. -/
private theorem differentialOfSeparating_ne_zero (hF : IsFunctionField k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    differentialOfSeparating hF hx ≠ 0 := by
  let _ := ratFuncAlgebraOfTranscendental hx
  let _ := isScalarTower_ratFuncAlgebraOfTranscendental hx
  let _ := isFunctionField_iff_functionField.mp hF
  let _ := isSeparable_ratFuncAlgebraOfTranscendental hx
  rw [differentialOfSeparating, ne_eq, weilDifferentialCotrace_eq_zero_iff,
    Submodule.mk_eq_zero]
  exact rationalDifferential_ne_zero k

/-- DEFINITION. The Weil basis given by the normalized separating differential.
Locator: `DivisorZero.lean`, `differentialBasis`. -/
private def differentialBasis (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    Basis Unit F ↥(weilDifferentialSpace k F) :=
  let _ := weilDifferentialSpaceModule hF
  FiniteDimensional.basisSingleton Unit (finrank_weilDifferentialSpace hF hex)
    (differentialOfSeparating hF hx) (differentialOfSeparating_ne_zero hF hx)

/-- DEFINITION. The normalized function-field-linear Kähler–Weil comparison.
It sends `dx` to the cotrace of normalized `dX`, not to a chosen regular form.
Locator: `DivisorZero.lean`, `comparison`; Stichtenoth §I.5. -/
def comparison (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    KaehlerDifferential k F ≃ₗ[F] ↥(weilDifferentialSpace k F) :=
  letI := weilDifferentialSpaceModule hF
  (kaehlerBasisOfSeparating hx).equiv (differentialBasis hF hex hx) (Equiv.refl Unit)

/-- THEOREM. The comparison sends `dx` to its normalized cotrace.
Locator: `DivisorZero.lean`, `comparison_D_self`. -/
theorem comparison_D_self (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    comparison hF hex hx (D k F x) = differentialOfSeparating hF hx := by
  let _ := weilDifferentialSpaceModule hF
  rw [← kaehlerBasisOfSeparating_apply hx (), comparison, Basis.equiv_apply]
  change differentialBasis hF hex hx () = differentialOfSeparating hF hx
  rw [differentialBasis]
  exact FiniteDimensional.basisSingleton_apply Unit (finrank_weilDifferentialSpace hF hex)
    (differentialOfSeparating hF hx) (differentialOfSeparating_ne_zero hF hx) ()

/-- DEFINITION. Local regularity of a Weil differential: its local residue functional
annihilates the valuation ring. Locator: Stichtenoth §I.5 and Proposition I.7.3(a);
`TauCeti.le_weilDifferentialOrder_iff`. -/
def RegularAt (P : Place k F) (ω : ↥(weilDifferentialSpace k F)) : Prop :=
  ∀ z : F, z ∈ P.integers → repartitionDualComponent (ω : Module.Dual k
    ↥(repartitionSpace k F)) P z = 0

/-- THEOREM. A nonzero Weil differential is locally regular exactly when its order
is nonnegative. Locator: Stichtenoth Proposition I.7.3(a);
`TauCeti.le_weilDifferentialOrder_iff`. -/
theorem regularAt_iff_order_nonneg (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (P : Place k F) (ω : ↥(weilDifferentialSpace k F))
    (hω : (ω : Module.Dual k ↥(repartitionSpace k F)) ≠ 0) :
    RegularAt P ω ↔ 0 ≤ weilDifferentialOrder hF hex ω.2 hω P := by
  rw [le_weilDifferentialOrder_iff hF hex ω.2 hω P 0]
  simp only [RegularAt, Place.mem_integers_iff, WithZero.exp_zero]

/-- THEOREM. The zero-divisor Weil filtration is exactly regularity at every place,
including the zero differential. Locator: Stichtenoth Definition I.5.6;
`TauCeti.mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero`. -/
theorem mem_zeroFiltration_iff_regularAt (ω : ↥(weilDifferentialSpace k F)) :
    (ω : Module.Dual k ↥(repartitionSpace k F)) ∈
      weilDifferentialFiltration (0 : Divisor k F) ↔ ∀ P : Place k F, RegularAt P ω := by
  rw [mem_weilDifferentialFiltration_iff_repartitionDualComponent_eq_zero ω.2]
  simp only [RegularAt, WeilDivisor.coeff_zero, WithZero.exp_zero, Place.mem_integers_iff]

/-- THEOREM. If a differential has order zero at a place, its multiples are regular
there exactly for coefficients in that place's valuation ring.
Locator: Silverman Chapter II, §4, the uniformizer expression `a dt`;
Stichtenoth Proposition I.5.13 and `weilDifferentialOrder_eq_ord_add_of_eq_repartitionDualMul`. -/
theorem regularAt_smul_iff (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (P : Place k F) (ω : ↥(weilDifferentialSpace k F))
    (hω : (ω : Module.Dual k ↥(repartitionSpace k F)) ≠ 0)
    (hord : weilDifferentialOrder hF hex ω.2 hω P = 0) (a : F) :
    letI := weilDifferentialSpaceModule hF
    RegularAt P (a • ω) ↔ a ∈ P.integers := by
  letI := weilDifferentialSpaceModule hF
  by_cases ha : a = 0
  · subst a
    simp only [zero_smul, RegularAt, Submodule.coe_zero,
      repartitionDualComponent_apply, LinearMap.zero_apply, implies_true, zero_mem]
  · have hmul : ((a • ω : ↥(weilDifferentialSpace k F)) : Module.Dual k
        ↥(repartitionSpace k F)) ≠ 0 := by
      rw [coe_weilDifferentialSpaceModule_smul]
      exact repartitionDualMul_ne_zero hF ha hω
    rw [regularAt_iff_order_nonneg hF hex P (a • ω) hmul]
    have horder := weilDifferentialOrder_eq_ord_add_of_eq_repartitionDualMul hF hex
      (a • ω : ↥(weilDifferentialSpace k F)).2 hmul ω.2 hω ha
      (coe_weilDifferentialSpaceModule_smul hF a ω) P
    rw [horder, hord, add_zero, Place.mem_integers_iff_ord_nonneg]

section LocalKaehler

/-- THEOREM. A local uniformizer is transcendental over the constant field.
Locator: Stichtenoth §I.1; `TauCeti.Place.ord_eq_zero_of_isAlgebraic`. -/
theorem uniformizer_transcendental (P : Place k F) {t : F}
    (ht : P.valuation.IsUniformizer t) : Transcendental k t := by
  intro halg
  have hzero := P.ord_eq_zero_of_isAlgebraic halg
  have hone := P.isUniformizer_iff_ord_eq_one.mp ht
  omega

variable [CharZero k]

/-- THEOREM. The rational Kähler differential of a uniformizer is nonzero.
Locator: Silverman Chapter II, §4; `TauCeti.D_ne_zero_of_separating`. -/
theorem uniformizer_D_ne_zero (hF : IsFunctionField k F) (P : Place k F) {t : F}
    (ht : P.valuation.IsUniformizer t) : D k F t ≠ 0 := by
  have ht' := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin ht'
  exact D_ne_zero_of_separating ht'

/-- THEOREM. The normalized comparison image of the differential of a uniformizer
is nonzero. Locator: `uniformizer_D_ne_zero` and the injectivity of `comparison`. -/
theorem comparison_uniformizer_ne_zero (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (P : Place k F) {t : F}
    (ht : P.valuation.IsUniformizer t) :
    letI := weilDifferentialSpaceModule hF
    (comparison hF hex hx (D k F t) : Module.Dual k ↥(repartitionSpace k F)) ≠ 0 := by
  letI := weilDifferentialSpaceModule hF
  rw [ne_eq, ZeroMemClass.coe_eq_zero, LinearEquiv.map_eq_zero_iff]
  exact uniformizer_D_ne_zero hF P ht

/-- DEFINITION. The constants-linear localization map from the Kähler differentials
of the actual valuation ring to rational Kähler differentials.
Locator: Mathlib `KaehlerDifferential.map`, with the inclusion `P.integers → F`. -/
def localKaehlerMap (P : Place k F) :
    KaehlerDifferential k P.integers →ₗ[k] KaehlerDifferential k F :=
  (KaehlerDifferential.map k k P.integers F).restrictScalars k

omit [CharZero k] in
/-- THEOREM. A local uniformizer basis computes localization by the same
coefficient in the function field. Locator: the uniformizer expression `a dt`,
Silverman Chapter II, §4; Mathlib `KaehlerDifferential.map_D`. -/
private theorem localKaehlerMap_basis_formula (P : Place k F) (t : P.integers)
    (b : Basis Unit P.integers (KaehlerDifferential k P.integers))
    (hb : b () = D k P.integers t) (ξ : KaehlerDifferential k P.integers) :
    localKaehlerMap P ξ = (b.repr ξ () : F) • D k F (t : F) := by
  have hrep : (b.repr ξ ()) • D k P.integers t = ξ := by
    simpa only [Fintype.sum_unique, hb] using b.sum_repr ξ
  change KaehlerDifferential.map k k P.integers F ξ = _
  conv_lhs => rw [← hrep]
  rw [map_smul, KaehlerDifferential.map_D]
  exact (algebraMap_smul F (b.repr ξ ()) (D k F (t : F))).symm

/-- THEOREM. A local Kähler module free on the differential of a uniformizer
embeds into the rational differential line. Locator: Silverman Chapter II, §4;
`localKaehlerMap_basis_formula` and `uniformizer_D_ne_zero`. -/
theorem localKaehlerMap_injective_of_uniformizerBasis (hF : IsFunctionField k F)
    (P : Place k F) (t : P.integers) (ht : P.valuation.IsUniformizer (t : F))
    (b : Basis Unit P.integers (KaehlerDifferential k P.integers))
    (hb : b () = D k P.integers t) : Function.Injective (localKaehlerMap P) := by
  rw [injective_iff_map_eq_zero]
  intro ξ hξ
  rw [localKaehlerMap_basis_formula P t b hb ξ] at hξ
  have hc : (b.repr ξ () : F) = 0 :=
    (smul_eq_zero.mp hξ).resolve_right (uniformizer_D_ne_zero hF P ht)
  have hc' : b.repr ξ () = 0 := Subtype.ext hc
  have hrep : (b.repr ξ ()) • D k P.integers t = ξ := by
    simpa only [Fintype.sum_unique, hb] using b.sum_repr ξ
  rw [← hrep, hc', zero_smul]

/-- THEOREM. A uniformizer basis and the single order identity `ord_P(dt) = 0`
identify the image of the actual local Kähler module with the locally regular
rational differentials. No global section space occurs in either hypothesis.
Locator: Silverman Chapter II, §4; Stichtenoth Proposition I.5.13. -/
theorem regularAt_comparison_iff_mem_local_range (hF : IsFunctionField k F)
    (hex : IsIntegrallyClosedIn k F) (hx : Transcendental k x)
    [Algebra.IsSeparable k⟮x⟯ F] (P : Place k F) (t : P.integers)
    (ht : P.valuation.IsUniformizer (t : F))
    (b : Basis Unit P.integers (KaehlerDifferential k P.integers))
    (hb : b () = D k P.integers t)
    (hord : letI := weilDifferentialSpaceModule hF
      weilDifferentialOrder hF hex (comparison hF hex hx (D k F (t : F))).2
        (comparison_uniformizer_ne_zero hF hex hx P ht) P = 0)
    (η : KaehlerDifferential k F) :
    letI := weilDifferentialSpaceModule hF
    RegularAt P (comparison hF hex hx η) ↔ η ∈ (localKaehlerMap P).range := by
  letI := weilDifferentialSpaceModule hF
  let φ := comparison hF hex hx
  have ht' := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin ht'
  constructor
  · intro hη
    let bF := kaehlerBasisOfSeparating ht'
    let a : F := bF.repr η ()
    have ha : a • D k F (t : F) = η := by
      simpa only [a, bF, Fintype.sum_unique, kaehlerBasisOfSeparating_apply]
        using bF.sum_repr η
    have haP : a ∈ P.integers := by
      apply (regularAt_smul_iff hF hex P (φ (D k F (t : F)))
        (comparison_uniformizer_ne_zero hF hex hx P ht) hord a).mp
      change RegularAt P (a • comparison hF hex hx (D k F (t : F)))
      rw [← map_smul, ha]
      exact hη
    refine ⟨(⟨a, haP⟩ : P.integers) • D k P.integers t, ?_⟩
    change KaehlerDifferential.map k k P.integers F
      ((⟨a, haP⟩ : P.integers) • D k P.integers t) = η
    rw [map_smul, KaehlerDifferential.map_D]
    exact (algebraMap_smul F (⟨a, haP⟩ : P.integers) (D k F (t : F))).symm.trans ha
  · rintro ⟨ξ, rfl⟩
    rw [localKaehlerMap_basis_formula P t b hb ξ, map_smul]
    exact (regularAt_smul_iff hF hex P (comparison hF hex hx (D k F (t : F)))
      (comparison_uniformizer_ne_zero hF hex hx P ht) hord (b.repr ξ () : F)).mpr
        (b.repr ξ ()).2

end LocalKaehler

/-- DEFINITION OF A LOCAL STANDARD FACT. At every place of a characteristic-zero
one-variable function field, the Kähler module of the actual valuation ring has
a basis `dt` for a local uniformizer. This is a local smoothness and cotangent
statement, not a comparison of global differential spaces.
Locator: Silverman Chapter II, §4, local parameters and regular differentials. -/
def LocalUniformizerBasis : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (_hF : IsFunctionField k F) (P : Place k F),
    ∃ t : P.integers, P.valuation.IsUniformizer (t : F) ∧
      ∃ b : Basis Unit P.integers (KaehlerDifferential k P.integers),
        b () = D k P.integers t

/-- DEFINITION OF A LOCAL STANDARD FACT. The normalized cotrace comparison gives
order zero to `dt` at the place where `t` is a uniformizer. Only one local order
is asserted, with no holomorphic filtration or sheaf section space in the input.
Locator: Stichtenoth §I.5, Remark I.5.12 and Proposition I.5.13;
Silverman Chapter II, §4, order of a differential in a local parameter. -/
def UniformizerResidueOrder : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (x : F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (P : Place k F) (t : F) (ht : P.valuation.IsUniformizer t),
    letI := weilDifferentialSpaceModule hF
    weilDifferentialOrder hF hex (comparison hF hex hx (D k F t)).2
      (comparison_uniformizer_ne_zero hF hex hx P ht) P = 0

section SheafGluing

variable {X : Scheme.{0}} [IsIntegral X] (M : X.Modules)

/-- INSTANCE. A module sheaf stalk is a module over the structure-sheaf stalk.
Locator: Mathlib, `Algebra/Category/ModuleCat/Stalk.lean`, the commutative-ring stalk action. -/
instance moduleStalk (p : X) : Module (X.presheaf.stalk p) (M.presheaf.stalk p) :=
  inferInstanceAs (Module (X.presheaf.stalk p)
    (TopCat.Presheaf.stalk (C := AddCommGrpCat.{0})
      (M.val : PresheafOfModules (X.presheaf ⋙ forget₂ _ _)).presheaf p))

omit [IsIntegral X] in
/-- THEOREM. A germ of a scalar multiple is the scalar germ times the section germ.
Locator: Mathlib `PresheafOfModules.germ_smul`. -/
private theorem moduleGerm_smul (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) (s : Γ(M, U)) :
    M.presheaf.germ U p hp (a • s) =
      X.presheaf.germ U p hp a • M.presheaf.germ U p hp s :=
  PresheafOfModules.germ_smul (R := X.presheaf) M.val p U hp a s

/-- THEOREM. Injectivity of specialization from every local stalk implies injectivity
of restriction to the generic stalk on every nonempty open.
Locator: the torsion-free sheaf criterion and Mathlib `TopCat.Presheaf.section_ext`. -/
theorem genericGerm_injective
    (hinj : ∀ p : X, Function.Injective
      (M.presheaf.stalkSpecializes (genericPoint_specializes p)))
    (U : X.Opens) [Nonempty U] : Function.Injective
      (M.presheaf.germ U (genericPoint X)
        (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr (by simpa using ‹Nonempty U›))) := by
  intro s t hst
  apply TopCat.Presheaf.section_ext ⟨M.presheaf, M.isSheaf⟩ U s t
  intro p hp
  apply hinj p
  rw [M.presheaf.germ_stalkSpecializes_apply hp (genericPoint_specializes p),
    M.presheaf.germ_stalkSpecializes_apply hp (genericPoint_specializes p)]
  exact hst

/-- THEOREM. A rational section lying in every local stalk on an open has a unique
regular section there. This is sheaf gluing, with no assertion about Weil differentials.
Locator: the standard intersection-of-stalks criterion; Mathlib
`TopCat.Sheaf.existsUnique_gluing'` and `TopCat.Presheaf.germ_stalkSpecializes_apply`. -/
theorem existsUnique_section_of_mem_local_stalks
    (hinj : ∀ p : X, Function.Injective
      (M.presheaf.stalkSpecializes (genericPoint_specializes p)))
    (U : X.Opens) [Nonempty U] (η : M.presheaf.stalk (genericPoint X))
    (hη : ∀ p ∈ U, η ∈ Set.range
      (M.presheaf.stalkSpecializes (genericPoint_specializes p))) :
    ∃! s : Γ(M, U), M.presheaf.germ U (genericPoint X)
      (((genericPoint_spec X).mem_open_set_iff U.isOpen).mpr
        (by simpa using ‹Nonempty U›)) s = η := by
  have hgen : ∀ V : X.Opens, Nonempty V → genericPoint X ∈ V := fun V hV =>
    ((genericPoint_spec X).mem_open_set_iff V.isOpen).mpr (by simpa using hV)
  have hlocal : ∀ p : U, ∃ V : X.Opens, ∃ hpV : (p : X) ∈ V, ∃ hVU : V ≤ U,
      ∃ s : Γ(M, V), M.presheaf.germ V (genericPoint X)
        (hgen V ⟨⟨(p : X), hpV⟩⟩) s = η := by
    intro p
    obtain ⟨ξ, hξ⟩ := hη p p.2
    obtain ⟨V, hVU, hVp, s, hs⟩ := M.presheaf.exists_le_germ_eq ξ p.2
    refine ⟨V, hVp, hVU, s, ?_⟩
    have heq := congrArg (M.presheaf.stalkSpecializes (genericPoint_specializes (p : X))) hs
    rw [M.presheaf.germ_stalkSpecializes_apply hVp (genericPoint_specializes (p : X)), hξ]
      at heq
    exact heq
  choose V hpV hVU s hs using hlocal
  have hne : ∀ p : U, Nonempty (V p) := fun p => ⟨⟨(p : X), hpV p⟩⟩
  have hcompat : TopCat.Presheaf.IsCompatible M.presheaf V s := by
    intro p q
    haveI : Nonempty (V p ⊓ V q : X.Opens) :=
      ⟨⟨genericPoint X, hgen (V p) (hne p), hgen (V q) (hne q)⟩⟩
    apply genericGerm_injective M hinj (V p ⊓ V q)
    rw [M.presheaf.germ_res_apply (Opens.infLELeft (V p) (V q)),
      M.presheaf.germ_res_apply (Opens.infLERight (V p) (V q))]
    exact (hs p).trans (hs q).symm
  obtain ⟨a, ha, -⟩ := (show TopCat.Sheaf AddCommGrpCat X from
    ⟨M.presheaf, M.isSheaf⟩).existsUnique_gluing' V U (fun p => homOfLE (hVU p))
      (fun p hp => Opens.mem_iSup.mpr ⟨⟨p, hp⟩, hpV ⟨p, hp⟩⟩) s hcompat
  have hagerm : M.presheaf.germ U (genericPoint X) (hgen U ‹Nonempty U›) a = η := by
    obtain ⟨p⟩ := ‹Nonempty U›
    have hres : M.presheaf.map (homOfLE (hVU p)).op a = s p := ha p
    rw [← hs p, ← hres, M.presheaf.germ_res_apply (homOfLE (hVU p))]
  refine ⟨a, hagerm, fun b hb => genericGerm_injective M hinj U (hb.trans hagerm.symm)⟩

/-- DEFINITION. Specialization to the generic stalk as a linear map over the
local ring, with the target action induced by its inclusion in the function field.
Locator: Mathlib `PresheafOfModules.germ_smul` and `TopCat.Presheaf.stalkSpecializes`. -/
def stalkSpecializationLinear (p : X) :
    letI : Module (X.presheaf.stalk p) (M.presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (algebraMap (X.presheaf.stalk p) X.functionField)
    M.presheaf.stalk p →ₗ[X.presheaf.stalk p] M.presheaf.stalk (genericPoint X) := by
  letI : Module (X.presheaf.stalk p) (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk p) X.functionField)
  refine { toFun := M.presheaf.stalkSpecializes (genericPoint_specializes p)
           map_add' := map_add _
           map_smul' := ?_ }
  intro r ξ
  change M.presheaf.stalkSpecializes (genericPoint_specializes p) (r • ξ) =
    algebraMap (X.presheaf.stalk p) X.functionField r •
      M.presheaf.stalkSpecializes (genericPoint_specializes p) ξ
  obtain ⟨U, hpU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hpV, m, rfl⟩ := M.presheaf.exists_germ_eq ξ
  have hpUV : p ∈ U ⊓ V := ⟨hpU, hpV⟩
  haveI : Nonempty (U ⊓ V : X.Opens) := ⟨⟨p, hpUV⟩⟩
  rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) p hpUV a,
    ← M.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) p hpUV m,
    ← moduleGerm_smul M p (U ⊓ V) hpUV]
  rw [M.presheaf.germ_stalkSpecializes_apply hpUV (genericPoint_specializes p),
    M.presheaf.germ_stalkSpecializes_apply hpUV (genericPoint_specializes p),
    moduleGerm_smul M,
    X.algebraMap_germ_eq_germToFunctionField]

/-- THEOREM. The linear specialization has the usual germ computation.
Locator: Mathlib `TopCat.Presheaf.germ_stalkSpecializes_apply`. -/
private theorem stalkSpecializationLinear_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (s : Γ(M, U)) :
    letI : Module (X.presheaf.stalk p) (M.presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (algebraMap (X.presheaf.stalk p) X.functionField)
    stalkSpecializationLinear M p (M.presheaf.germ U p hp s) =
      M.presheaf.germ U (genericPoint X) ((genericPoint_specializes p).mem_open U.isOpen hp) s :=
  M.presheaf.germ_stalkSpecializes_apply hp (genericPoint_specializes p) s

end SheafGluing

section DifferentialStalks

open ZInQ.Contrib.RC53Assist.AbelianCurve
open PresheafOfModules PresheafOfModulesOfCommRing
open PresheafOfModulesOfCommRing.DifferentialsConstruction

/-- DEFINITION. The actual sheafified universal relative derivation.
Locator: `DifferentialLine.lean`, `differentialSheaf`, and Mathlib's
`DifferentialsConstruction.derivation'` followed by the sheafification unit. -/
def differentialDerivation {X : Scheme.{0}} (f : X ⟶ Spec (.of ℚ)) :
    PresheafOfModulesOfCommRing.Derivation' (differentialSheaf f).val
      (inverseImageStructureMap f) :=
  (derivation' (inverseImageStructureMap f)).postcomp
    ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app _)

/-- DEFINITION OF LOCAL COMPARISON DATA. At each point, the actual differential
sheaf stalk is the Kähler module of the actual local ring, identifying the
universal derivations on germs. No global sections, properness, dimension,
Weil filtration, or genus occur in this data.
Locator: the standard stalk calculation for relative Kähler differentials,
Silverman Chapter II, §§4–5; the affine calculation in the vendored Jacobian
library, `AlgebraicGeometry/Modules/DifferentialsSections.lean`. -/
structure DifferentialStalkData {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) where
  /-- FIELD. The local linear identification. Locator: the stalk calculation of `Ω¹`. -/
  equiv : ∀ p : X,
    letI := stalkAlgebra f p
    KaehlerDifferential ℚ (X.presheaf.stalk p) ≃ₗ[X.presheaf.stalk p]
      (differentialSheaf f).presheaf.stalk p
  /-- FIELD. Compatibility with the universal derivation. Locator: `d a ↦ d a` on germs. -/
  equiv_D_germ : ∀ (p : X) (U : X.Opens) (hp : p ∈ U) (a : Γ(X, U)),
    letI := stalkAlgebra f p
    equiv p (D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hp a)) =
      (differentialSheaf f).presheaf.germ U p hp
        ((differentialDerivation f).d (X := op U) a)

/-- DEFINITION OF A LOCAL STANDARD FACT. Sheafification and taking stalks give
the canonical local Kähler identifications, compatibly with the universal
derivations. It applies without a properness or curve hypothesis.
Locator: the stalk formula for relative differentials; Silverman Chapter II, §§4–5. -/
def StalkDifferentials : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of ℚ)),
    Nonempty (DifferentialStalkData f)

/-- THEOREM. Canonical local Kähler identifications commute with specialization
to the generic point. Naturality is proved from the universal derivations rather
than included as a new input. Locator: Mathlib
`Derivation.liftKaehlerDifferential_unique` and the germ specialization identity. -/
theorem DifferentialStalkData.specializes_equiv {X : Scheme.{0}} [IsIntegral X]
    {f : X ⟶ Spec (.of ℚ)} (d : DifferentialStalkData f) (p : X) :
    letI := functionFieldAlgebra f
    letI := stalkAlgebra f p
    letI := stalk_functionField_tower f p
    ∀ ξ : KaehlerDifferential ℚ (X.presheaf.stalk p),
      (differentialSheaf f).presheaf.stalkSpecializes (genericPoint_specializes p)
        (d.equiv p ξ) =
      d.equiv (genericPoint X) (KaehlerDifferential.map ℚ ℚ (X.presheaf.stalk p)
        X.functionField ξ) := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  let M := differentialSheaf f
  letI : Module ℚ (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap ℚ X.functionField)
  letI : Module (X.presheaf.stalk p) (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap (X.presheaf.stalk p) X.functionField)
  haveI : IsScalarTower ℚ (X.presheaf.stalk p) (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun c ξ => by
      change algebraMap (X.presheaf.stalk p) X.functionField
        (algebraMap ℚ (X.presheaf.stalk p) c) • ξ = algebraMap ℚ X.functionField c • ξ
      rw [← IsScalarTower.algebraMap_apply ℚ (X.presheaf.stalk p) X.functionField]
  haveI : IsScalarTower (X.presheaf.stalk p) X.functionField
      (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : KaehlerDifferential ℚ X.functionField ≃ₗ[X.functionField]
      M.presheaf.stalk (genericPoint X) := d.equiv (genericPoint X)
  let L := (stalkSpecializationLinear M p) ∘ₗ (d.equiv p).toLinearMap
  let R := (e.restrictScalars (X.presheaf.stalk p)).toLinearMap ∘ₗ
    KaehlerDifferential.map ℚ ℚ (X.presheaf.stalk p) X.functionField
  have heq : L = R := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    obtain ⟨U, hpU, a, rfl⟩ := X.presheaf.exists_germ_eq z
    haveI : Nonempty U := ⟨⟨p, hpU⟩⟩
    change stalkSpecializationLinear M p
      (d.equiv p (D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hpU a))) =
      e (KaehlerDifferential.map ℚ ℚ (X.presheaf.stalk p) X.functionField
        (D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hpU a)))
    rw [d.equiv_D_germ, stalkSpecializationLinear_germ,
      KaehlerDifferential.map_D, X.algebraMap_germ_eq_germToFunctionField]
    exact (d.equiv_D_germ (genericPoint X) U
      ((genericPoint_specializes p).mem_open U.isOpen hpU) a).symm
  intro ξ
  change L ξ = R ξ
  exact LinearMap.congr_fun heq ξ

end DifferentialStalks

section StalkCalculation

open ZInQ.Contrib.RC53Assist.AbelianCurve
open PresheafOfModules PresheafOfModulesOfCommRing
open PresheafOfModulesOfCommRing.DifferentialsConstruction

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℚ))

/-- DEFINITION. The universal property of the actual sheafified relative
differentials. Locator: Mathlib's presheaf universal derivation and the
sheafification adjunction; Stacks Project, Tag 01UM. -/
private def differentialHomEquiv (N : X.Modules) :
    (differentialSheaf f ⟶ N) ≃
      PresheafOfModulesOfCommRing.Derivation' N.val (inverseImageStructureMap f) where
  toFun g := (differentialDerivation f).postcomp g.val
  invFun D := ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm
    ((isUniversal' (inverseImageStructureMap f)).desc D)
  left_inv g := by
    apply ((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).injective
    rw [Equiv.apply_symm_apply]
    apply (isUniversal' (inverseImageStructureMap f)).postcomp_injective
    rw [Derivation.Universal.fac]
    rfl
  right_inv D := by
    change (derivation' (inverseImageStructureMap f)).postcomp
      (((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _)
        (((sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).symm _)) = D
    rw [Equiv.apply_symm_apply, Derivation.Universal.fac]

omit [IsIntegral X] in
/-- THEOREM. The sheaf universal property sends the universal derivative to the
specified derivative. Locator: `differentialHomEquiv` and the universal derivation. -/
private theorem differentialHomEquiv_symm_app_d (N : X.Modules)
    (D : PresheafOfModulesOfCommRing.Derivation' N.val (inverseImageStructureMap f))
    (U : X.Opensᵒᵖ) (a : X.presheaf.obj U) :
    ((differentialHomEquiv f N).symm D).val.app U
      ((differentialDerivation f).d a) = D.d a :=
  congr($((differentialHomEquiv f N).apply_symm_apply D).d a)

/-- THEOREM. The inverse-image structure map has its defining adjunction identity.
Locator: the presheaf inverse-image adjunction, as in the vendored Jacobian
library, `AlgebraicGeometry/Differentials/Presheaf.lean`. -/
private theorem inverseImageMap_unit {Y S : Scheme.{0}} (g : Y ⟶ S) :
    (TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat g.base).unit.app S.presheaf ≫
      (TopCat.Presheaf.pushforward CommRingCat g.base).map (inverseImageStructureMap g) = g.c :=
  (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)

/-- THEOREM. Every structure-sheaf pullback on an open factors through the
inverse-image structure presheaf. Locator: the inverse-image adjunction;
`AlgebraicGeometry/Differentials/Presheaf.lean`, the affine restriction factorization. -/
private theorem inverseImageMap_appLE_factor {Y S : Scheme.{0}} (g : Y ⟶ S)
    (U : S.Opens) (V : Y.Opens) (h : V ≤ g ⁻¹ᵁ U) :
    g.appLE U V h =
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat g.base).unit.app
        S.presheaf).app (op U) ≫ (inverseImageStructure g).map (homOfLE h).op ≫
          (inverseImageStructureMap g).app (op V) := by
  rw [(inverseImageStructureMap g).naturality, ← Category.assoc]
  have heq := NatTrans.congr_app (inverseImageMap_unit g) (op U)
  rw [NatTrans.comp_app] at heq
  erw [heq]
  rfl

omit [IsIntegral X] in
/-- THEOREM. The universal sheaf derivative vanishes on base constants on each
open. Locator: the defining relative-derivation condition and
`inverseImageMap_appLE_factor`. -/
private theorem differentialDerivation_base_constant (U : X.Opens) (c : ℚ) :
    (differentialDerivation f).d (X := op U)
      (f.appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of ℚ)).inv c)) = 0 := by
  rw [inverseImageMap_appLE_factor]
  exact PresheafOfModulesOfCommRing.Derivation'.d_app (differentialDerivation f) _

omit [IsIntegral X] in
/-- THEOREM. Pulling a base constant to an open and taking its germ is the
specified base algebra map to the local ring. Locator: `IdentityPlace.lean`,
`stalkAlgebra`, and naturality of restriction. -/
private theorem germ_base_constant (p : X) (U : X.Opens) (hp : p ∈ U) (c : ℚ) :
    letI := stalkAlgebra f p
    X.presheaf.germ U p hp (f.appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of ℚ)).inv c)) =
      algebraMap ℚ (X.presheaf.stalk p) c := by
  letI := stalkAlgebra f p
  change X.presheaf.germ U p hp (f.appLE ⊤ U le_top ((Scheme.ΓSpecIso (.of ℚ)).inv c)) =
    X.presheaf.germ ⊤ p trivial (f.appTop ((Scheme.ΓSpecIso (.of ℚ)).inv c))
  simp only [Scheme.Hom.appLE, Scheme.Hom.appTop, ConcreteCategory.comp_apply]
  rw [X.presheaf.germ_res_apply]
  simp only [Opens.map_top]

omit [IsIntegral X] in
/-- THEOREM. The sheaf derivative commutes with restriction of sections.
Locator: the defining presheaf derivation naturality. -/
private theorem differentialDerivation_map {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (a : X.presheaf.obj U) :
    (differentialDerivation f).d (X.presheaf.map i a) =
      (differentialSheaf f).presheaf.map i ((differentialDerivation f).d a) :=
  (differentialDerivation f).d_map i a

/-- DEFINITION. The compatible additive maps on neighborhoods defining the
universal derivative on the local ring. Locator: the filtered-colimit definition
of a stalk and compatibility of the sheaf universal derivative with restriction. -/
private def stalkDerivativeCocone (p : X) :
    Cocone ((OpenNhds.inclusion p).op ⋙ X.presheaf ⋙ (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)) where
  pt := (differentialSheaf f).presheaf.stalk p
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        ((differentialDerivation f).d (X := op U.unop.1)) ≫
          (differentialSheaf f).presheaf.germ U.unop.1 p U.unop.2
      naturality := by
        intro U V i
        ext a
        change (differentialSheaf f).presheaf.germ V.unop.1 p V.unop.2
          ((differentialDerivation f).d
            (X.presheaf.map ((OpenNhds.inclusion p).op.map i) a)) =
          (differentialSheaf f).presheaf.germ U.unop.1 p U.unop.2
            ((differentialDerivation f).d a)
        have hD := differentialDerivation_map f ((OpenNhds.inclusion p).op.map i) a
        have hres := (differentialSheaf f).presheaf.germ_res_apply'
          ((OpenNhds.inclusion p).op.map i) p V.unop.2 ((differentialDerivation f).d a)
        exact (congrArg ((differentialSheaf f).presheaf.germ V.unop.1 p V.unop.2) hD).trans
          hres }

/-- DEFINITION. The additive universal derivative on the actual local ring,
obtained by the stalk colimit. Locator: Mathlib's preservation of filtered
colimits by `(forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat)`. -/
private def stalkDerivativeAdd (p : X) :
    X.presheaf.stalk p →+ (differentialSheaf f).presheaf.stalk p :=
  ConcreteCategory.hom ((isColimitOfPreserves ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    (colimit.isColimit ((OpenNhds.inclusion p).op ⋙ X.presheaf))).desc
      (stalkDerivativeCocone f p))

omit [IsIntegral X] in
/-- THEOREM. The local additive derivative is the germ of the sheaf derivative.
Locator: the stalk colimit computation `IsColimit.fac`. -/
private theorem stalkDerivativeAdd_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) :
    stalkDerivativeAdd f p (X.presheaf.germ U p hp a) =
      (differentialSheaf f).presheaf.germ U p hp
        ((differentialDerivation f).d (X := op U) a) := by
  have h := (isColimitOfPreserves ((forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat))
    (colimit.isColimit ((OpenNhds.inclusion p).op ⋙ X.presheaf))).fac
      (stalkDerivativeCocone f p) (op ⟨U, hp⟩)
  exact ConcreteCategory.congr_hom h a

/-- THEOREM. The local additive derivative kills the constants.
Locator: `germ_base_constant`, `stalkDerivativeAdd_germ`, and the relative
universal derivation. -/
private theorem stalkDerivativeAdd_algebraMap (p : X) (c : ℚ) :
    letI := stalkAlgebra f p
    stalkDerivativeAdd f p (algebraMap ℚ (X.presheaf.stalk p) c) = 0 := by
  letI := stalkAlgebra f p
  rw [← germ_base_constant f p ⊤ trivial c, stalkDerivativeAdd_germ,
    differentialDerivation_base_constant, map_zero]

/-- THEOREM. The local additive derivative satisfies the product rule.
Locator: the product rule for the sheaf derivative, represented on a common
neighborhood; Mathlib `PresheafOfModules.germ_smul`. -/
private theorem stalkDerivativeAdd_mul (p : X) (r s : X.presheaf.stalk p) :
    stalkDerivativeAdd f p (r * s) =
      r • stalkDerivativeAdd f p s + s • stalkDerivativeAdd f p r := by
  obtain ⟨U, hpU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hpV, b, rfl⟩ := X.presheaf.exists_germ_eq s
  have hpUV : p ∈ U ⊓ V := ⟨hpU, hpV⟩
  rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) p hpUV a,
    ← X.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) p hpUV b,
    ← map_mul (X.presheaf.germ (U ⊓ V) p hpUV).hom,
    stalkDerivativeAdd_germ, stalkDerivativeAdd_germ, stalkDerivativeAdd_germ,
    (differentialDerivation f).d_mul, map_add,
    moduleGerm_smul (differentialSheaf f), moduleGerm_smul (differentialSheaf f)]

/-- DEFINITION. The universal sheaf derivative induces an actual rational-base
local-ring derivation. Locator: the preceding additive, constant, and product
identities; the standard construction of differentials on a stalk. -/
private def stalkDerivative (p : X) :
    letI := stalkAlgebra f p
    letI : Module ℚ ((differentialSheaf f).presheaf.stalk p) :=
      Module.compHom _ (algebraMap ℚ (X.presheaf.stalk p))
    Derivation ℚ (X.presheaf.stalk p) ((differentialSheaf f).presheaf.stalk p) := by
  letI := stalkAlgebra f p
  letI : Module ℚ ((differentialSheaf f).presheaf.stalk p) :=
    Module.compHom _ (algebraMap ℚ (X.presheaf.stalk p))
  refine
    { toFun := stalkDerivativeAdd f p
      map_add' := map_add _
      map_smul' := ?_
      map_one_eq_zero' := ?_
      leibniz' := stalkDerivativeAdd_mul f p }
  · intro c r
    rw [RingHom.id_apply, Algebra.smul_def, stalkDerivativeAdd_mul,
      stalkDerivativeAdd_algebraMap, smul_zero, add_zero]
    rfl
  · rw [← map_one (algebraMap ℚ (X.presheaf.stalk p))]
    exact stalkDerivativeAdd_algebraMap f p 1

/-- THEOREM. The local derivation identifies the derivative of a germ with the
germ of its derivative. Locator: `stalkDerivativeAdd_germ`. -/
private theorem stalkDerivative_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) :
    letI := stalkAlgebra f p
    letI : Module ℚ ((differentialSheaf f).presheaf.stalk p) :=
      Module.compHom _ (algebraMap ℚ (X.presheaf.stalk p))
    stalkDerivative f p (X.presheaf.germ U p hp a) =
      (differentialSheaf f).presheaf.germ U p hp
        ((differentialDerivation f).d (X := op U) a) :=
  stalkDerivativeAdd_germ f p U hp a

end StalkCalculation

section SkyscraperCalculation

variable {X : Scheme.{0}} [IsIntegral X] (p : X) (N : Type) [AddCommGroup N]
  [Module (X.presheaf.stalk p) N]

/-- DEFINITION. Sections of the local-ring skyscraper module.
Locator: the stalk-to-skyscraper adjunction; the vendored Jacobian library,
`AlgebraicGeometry/Modules/Stalk.lean`, `SkyscraperSections`. -/
private def LocalSkySections (U : X.Opens) : Type := PLift (p ∈ U) → N

/-- INSTANCE. Pointwise addition on skyscraper sections.
Locator: the additive group of functions into an additive group. -/
private instance localSkyAddGroup (U : X.Opens) : AddCommGroup (LocalSkySections p N U) :=
  inferInstanceAs (AddCommGroup (PLift (p ∈ U) → N))

/-- INSTANCE. Functions act on skyscraper sections through their germs.
Locator: the local-ring module structure of a skyscraper sheaf. -/
private instance localSkySMul (U : X.Opens) : SMul Γ(X, U) (LocalSkySections p N U) :=
  ⟨fun a s hp => X.presheaf.germ U p hp.down a • s hp⟩

/-- INSTANCE. The germ action is a module action on skyscraper sections.
Locator: multiplicativity and additivity of the structure-sheaf germ map. -/
private instance localSkyModule (U : X.Opens) : Module Γ(X, U) (LocalSkySections p N U) where
  one_smul s := by
    funext hp
    change X.presheaf.germ U p hp.down 1 • s hp = s hp
    simp
  mul_smul a b s := by
    funext hp
    change X.presheaf.germ U p hp.down (a * b) • s hp =
      X.presheaf.germ U p hp.down a • (X.presheaf.germ U p hp.down b • s hp)
    simp [mul_smul]
  smul_zero a := by
    funext hp
    change X.presheaf.germ U p hp.down a • (0 : N) = 0
    exact smul_zero _
  smul_add a s t := by
    funext hp
    change X.presheaf.germ U p hp.down a • (s hp + t hp) =
      X.presheaf.germ U p hp.down a • s hp + X.presheaf.germ U p hp.down a • t hp
    exact smul_add _ _ _
  add_smul a b s := by
    funext hp
    change X.presheaf.germ U p hp.down (a + b) • s hp =
      X.presheaf.germ U p hp.down a • s hp + X.presheaf.germ U p hp.down b • s hp
    simp [add_smul]
  zero_smul s := by
    funext hp
    change X.presheaf.germ U p hp.down 0 • s hp = 0
    simp

/-- DEFINITION. The abelian presheaf of a local-ring skyscraper.
Locator: restriction of a function on memberships of the support point. -/
private def localSkyPresheaf : X.Opensᵒᵖ ⥤ AddCommGrpCat where
  obj U := AddCommGrpCat.of (LocalSkySections p N U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := fun s hp => s ⟨i.unop.le hp.down⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- INSTANCE. The skyscraper presheaf fibers carry the structure-ring action.
Locator: `localSkyModule`. -/
private instance localSkyPresheafModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((localSkyPresheaf p N).obj U) :=
  inferInstanceAs (Module Γ(X, U.unop) (LocalSkySections p N U.unop))

omit [IsIntegral X] in
/-- THEOREM. Skyscraper restrictions respect the germ scalar action.
Locator: Mathlib `TopCat.Presheaf.germ_res_apply`. -/
private theorem localSkyPresheaf_map_smul {U V : X.Opensᵒᵖ} (i : U ⟶ V)
    (a : X.ringCatSheaf.obj.obj U) (s : (localSkyPresheaf p N).obj U) :
    (localSkyPresheaf p N).map i (a • s) =
      X.ringCatSheaf.obj.map i a • (localSkyPresheaf p N).map i s := by
  funext hp
  exact congrArg (fun r => r • s ⟨i.unop.le hp.down⟩)
    (X.presheaf.germ_res_apply i.unop p hp.down a).symm

omit [IsIntegral X] [Module (X.presheaf.stalk p) N] in
/-- THEOREM. Skyscraper sections satisfy unique gluing.
Locator: the stalk-to-skyscraper adjunction, with gluing at the support point. -/
private theorem localSkyPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (localSkyPresheaf p N) := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (X := X.carrier)
    (localSkyPresheaf p N)).mpr
  intro ι cover sections compatible
  choose index index_mem using fun hp : PLift (p ∈ iSup cover) => Opens.mem_iSup.mp hp.down
  let glued : LocalSkySections p N (iSup cover) :=
    fun hp => sections (index hp) ⟨index_mem hp⟩
  refine ⟨glued, ?_, ?_⟩
  · intro i
    funext hp
    exact congrFun (compatible (index ⟨(Opens.leSupr cover i).le hp.down⟩) i)
      ⟨⟨index_mem ⟨(Opens.leSupr cover i).le hp.down⟩, hp.down⟩⟩
  · intro other hother
    funext hp
    exact congrFun (hother (index hp)) ⟨index_mem hp⟩

/-- DEFINITION. The actual module skyscraper with specified local-ring fiber.
Locator: the stalk-to-skyscraper adjunction;
`AlgebraicGeometry/Modules/Stalk.lean`, `skyscraper`. -/
private def localSky : X.Modules where
  val := PresheafOfModules.ofPresheaf (localSkyPresheaf p N)
    (fun _ _ i a s => localSkyPresheaf_map_smul p N i a s)
  isSheaf := localSkyPresheaf_isSheaf p N

/-- DEFINITION. A local-ring-linear map on the stalk gives a sheaf map to its
skyscraper. Locator: the stalk-to-skyscraper adjunction, defined on germs. -/
private def toLocalSky {M : X.Modules} (l : M.presheaf.stalk p →ₗ[X.presheaf.stalk p] N) :
    M ⟶ localSky p N :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => show LocalSkySections p N U.unop from
            fun hp => l (M.presheaf.germ U.unop p hp.down s)
          map_zero' := by
            funext hp
            simp only [map_zero]
            rfl
          map_add' := by
            intro s t
            funext hp
            simp only [map_add]
            rfl }
      naturality := by
        intro U V i
        ext s
        funext hp
        exact congrArg l (M.presheaf.germ_res_apply i.unop p hp.down s) }
    (fun U a s => by
      funext hp
      exact (congrArg l (moduleGerm_smul M p U.unop hp.down a s)).trans
        (l.map_smul _ _))⟩

omit [IsIntegral X] in
/-- THEOREM. The map to the skyscraper is evaluation of the map on the section germ.
Locator: `toLocalSky`. -/
private theorem toLocalSky_app {M : X.Modules}
    (l : M.presheaf.stalk p →ₗ[X.presheaf.stalk p] N)
    (U : X.Opens) (s : Γ(M, U)) (hp : p ∈ U) :
    (toLocalSky p N l).app U s ⟨hp⟩ = l (M.presheaf.germ U p hp s) := rfl

/-- DEFINITION. The additive stalk map induced by a sheaf map to a skyscraper,
expressed as its compatible neighborhood evaluations.
Locator: the filtered-colimit definition of a stalk. -/
private def localSkyMapCocone {M : X.Modules} (h : M ⟶ localSky p N) :
    Cocone ((OpenNhds.inclusion p).op ⋙ M.presheaf) where
  pt := AddCommGrpCat.of N
  ι :=
    { app := fun U => AddCommGrpCat.ofHom
        { toFun := fun s => h.app U.unop.1 s ⟨U.unop.2⟩
          map_zero' := by
            rw [map_zero]
            rfl
          map_add' := by
            intro s t
            rw [map_add]
            rfl }
      naturality := by
        intro U V i
        ext s
        have hn := h.mapPresheaf.naturality_apply ((OpenNhds.inclusion p).op.map i) s
        exact congrArg (fun z => z ⟨V.unop.2⟩) hn }

/-- DEFINITION. The additive map on a stalk furnished by its colimit.
Locator: `localSkyMapCocone` and `colimit.desc`. -/
private def localSkyMapAdd {M : X.Modules} (h : M ⟶ localSky p N) :
    M.presheaf.stalk p →+ N :=
  ConcreteCategory.hom (colimit.desc _ (localSkyMapCocone p N h))

omit [IsIntegral X] in
/-- THEOREM. Evaluation of the induced stalk map on a germ is the skyscraper
component at the support point. Locator: the stalk colimit identity. -/
private theorem localSkyMapAdd_germ {M : X.Modules} (h : M ⟶ localSky p N)
    (U : X.Opens) (hp : p ∈ U) (s : Γ(M, U)) :
    localSkyMapAdd p N h (M.presheaf.germ U p hp s) = h.app U s ⟨hp⟩ := by
  have hc := (colimit.isColimit ((OpenNhds.inclusion p).op ⋙ M.presheaf)).fac
    (localSkyMapCocone p N h) (op ⟨U, hp⟩)
  exact ConcreteCategory.congr_hom hc s

/-- DEFINITION. A compatible additive stalk map is linear when it respects
germ scalar multiplication. Locator: the local-ring action on a sheaf stalk;
`AlgebraicGeometry/Modules/Stalk.lean`, `stalkLinearMapMk`. -/
private def localStalkLinearMapMk {M : X.Modules} (l : M.presheaf.stalk p →+ N)
    (hl : ∀ (U : X.Opens) (hp : p ∈ U) (a : Γ(X, U)) (s : Γ(M, U)),
      l (M.presheaf.germ U p hp (a • s)) =
        X.presheaf.germ U p hp a • l (M.presheaf.germ U p hp s)) :
    M.presheaf.stalk p →ₗ[X.presheaf.stalk p] N where
  __ := l
  map_smul' r ξ := by
    obtain ⟨U, hpU, a, rfl⟩ := X.presheaf.exists_germ_eq r
    obtain ⟨V, hpV, s, rfl⟩ := M.presheaf.exists_germ_eq ξ
    have hpUV : p ∈ U ⊓ V := ⟨hpU, hpV⟩
    rw [← X.presheaf.germ_res_apply (homOfLE (inf_le_left : U ⊓ V ≤ U)) p hpUV a,
      ← M.presheaf.germ_res_apply (homOfLE (inf_le_right : U ⊓ V ≤ V)) p hpUV s,
      ← moduleGerm_smul M p (U ⊓ V) hpUV]
    exact hl _ hpUV _ _

/-- DEFINITION. A sheaf map to the local-ring skyscraper induces a local-ring
linear map on the stalk. Locator: the stalk-to-skyscraper adjunction. -/
private def localSkyMapLinear {M : X.Modules} (h : M ⟶ localSky p N) :
    M.presheaf.stalk p →ₗ[X.presheaf.stalk p] N :=
  localStalkLinearMapMk p N (localSkyMapAdd p N h) (fun U hp a s => by
    rw [localSkyMapAdd_germ, localSkyMapAdd_germ]
    exact congrArg (fun z => z ⟨hp⟩) (h.app_smul a s))

/-- THEOREM. The induced linear stalk map evaluates a germ by the corresponding
skyscraper component. Locator: `localSkyMapAdd_germ`. -/
private theorem localSkyMapLinear_germ {M : X.Modules} (h : M ⟶ localSky p N)
    (U : X.Opens) (hp : p ∈ U) (s : Γ(M, U)) :
    localSkyMapLinear p N h (M.presheaf.germ U p hp s) = h.app U s ⟨hp⟩ :=
  localSkyMapAdd_germ p N h U hp s

end SkyscraperCalculation

section StalkEquivalence

open ZInQ.Contrib.RC53Assist.AbelianCurve
open PresheafOfModulesOfCommRing

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℚ))

omit [IsIntegral X] in
/-- THEOREM. A section of the inverse-image structure presheaf has a representative
on a base open. Locator: the filtered left Kan extension defining presheaf pullback;
`AlgebraicGeometry/Modules/Differentials.lean`, the inverse-image representative lemma. -/
private theorem inverseImageStructureMap_exists_appLE (W : X.Opens)
    (b : (inverseImageStructure f).obj (op W)) :
    ∃ (V : (Spec (.of ℚ)).Opens) (h : W ≤ f ⁻¹ᵁ V) (a : Γ(Spec (.of ℚ), V)),
      (inverseImageStructureMap f).app (op W) b = f.appLE V W h a := by
  haveI : IsFiltered (CostructuredArrow (Opens.map f.base).op (op W)) :=
    IsFiltered.of_equivalence (structuredArrowOpEquivalence _ _)
  obtain ⟨g, a, rfl⟩ := Concrete.isColimit_exists_rep _
    ((Opens.map f.base).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit
      (Spec (.of ℚ)).presheaf (op W)) b
  refine ⟨g.left.unop, leOfHom g.hom.unop, a, ?_⟩
  rw [inverseImageMap_appLE_factor]
  have hunit :
      ((TopCat.Presheaf.pullbackPushforwardAdjunction CommRingCat f.base).unit.app
        (Spec (.of ℚ)).presheaf).app g.left ≫
          (inverseImageStructure f).map (homOfLE (leOfHom g.hom.unop)).op =
      ((Functor.LeftExtension.mk _ ((Opens.map f.base).op.leftKanExtensionUnit
        (Spec (.of ℚ)).presheaf)).coconeAt (op W)).ι.app g := by
    rw [TopCat.Presheaf.pullbackPushforwardAdjunction, Functor.lanAdjunction_unit]
    rfl
  rw [← Category.assoc, hunit]
  rfl

/-- DEFINITION. The local-ring universal Kähler derivative, as a relative sheaf
derivation into the corresponding skyscraper module.
Locator: the universal property of Kähler differentials and the stalk-to-skyscraper
adjunction; the vanishing on the inverse image is proved from its base representative. -/
private def localKaehlerSkyDerivation (p : X) :
    letI := stalkAlgebra f p
    PresheafOfModulesOfCommRing.Derivation'
      (localSky p (KaehlerDifferential ℚ (X.presheaf.stalk p))).val
      (inverseImageStructureMap f) := by
  letI := stalkAlgebra f p
  refine
    { d := fun {U} =>
        { toFun := fun a => show LocalSkySections p
            (KaehlerDifferential ℚ (X.presheaf.stalk p)) U.unop from
              fun hp => D ℚ (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down a)
          map_zero' := by
            funext hp
            change D ℚ (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down 0) = 0
            simp only [map_zero]
          map_add' := by
            intro a b
            funext hp
            change D ℚ (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down (a + b)) =
              D ℚ (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down a) +
                D ℚ (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down b)
            simp only [map_add] }
      d_mul := ?_
      d_map := ?_
      d_app := ?_ }
  · intro U a b
    funext hp
    change D ℚ (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down (a * b)) =
      X.presheaf.germ U.unop p hp.down a •
        D ℚ (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down b) +
      X.presheaf.germ U.unop p hp.down b •
        D ℚ (X.presheaf.stalk p) (X.presheaf.germ U.unop p hp.down a)
    rw [map_mul]
    exact (D ℚ (X.presheaf.stalk p)).leibniz _ _
  · intro U V i a
    funext hp
    exact congrArg (D ℚ (X.presheaf.stalk p))
      (X.presheaf.germ_res_apply i.unop p hp.down a)
  · intro W b
    funext hp
    obtain ⟨V, h, a, ha⟩ := inverseImageStructureMap_exists_appLE f W.unop b
    obtain rfl : V = ⊤ := eq_top_iff.mpr fun y _ =>
      Subsingleton.elim (f p) y ▸ h hp.down
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso
      (Scheme.ΓSpecIso (.of ℚ)).inv).2 a
    change D ℚ (X.presheaf.stalk p)
      (X.presheaf.germ W.unop p hp.down ((inverseImageStructureMap f).app W b)) = 0
    rw [ha, germ_base_constant f p W.unop hp.down c]
    exact (D ℚ (X.presheaf.stalk p)).map_algebraMap c

/-- DEFINITION. The universal derivation on the local ring gives the canonical
map from its Kähler module into the differential sheaf stalk.
Locator: `stalkDerivative` and `Derivation.liftKaehlerDifferential`. -/
private def localKaehlerToSheaf (p : X) :
    letI := stalkAlgebra f p
    KaehlerDifferential ℚ (X.presheaf.stalk p) →ₗ[X.presheaf.stalk p]
      (differentialSheaf f).presheaf.stalk p := by
  letI := stalkAlgebra f p
  letI : Module ℚ ((differentialSheaf f).presheaf.stalk p) :=
    Module.compHom _ (algebraMap ℚ (X.presheaf.stalk p))
  haveI : IsScalarTower ℚ (X.presheaf.stalk p) ((differentialSheaf f).presheaf.stalk p) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  exact (stalkDerivative f p).liftKaehlerDifferential

/-- THEOREM. The canonical map takes the Kähler derivative of a germ to the
sheaf derivative germ. Locator: the defining universal derivation. -/
private theorem localKaehlerToSheaf_D_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) :
    letI := stalkAlgebra f p
    localKaehlerToSheaf f p (D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hp a)) =
      (differentialSheaf f).presheaf.germ U p hp
        ((differentialDerivation f).d (X := op U) a) := by
  letI := stalkAlgebra f p
  letI : Module ℚ ((differentialSheaf f).presheaf.stalk p) :=
    Module.compHom _ (algebraMap ℚ (X.presheaf.stalk p))
  change (stalkDerivative f p).liftKaehlerDifferential
    (D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hp a)) = _
  rw [Derivation.liftKaehlerDifferential_comp_D]
  exact stalkDerivative_germ f p U hp a

/-- DEFINITION. The inverse map comes from the relative sheaf universal property
with target the local Kähler skyscraper and then its stalk evaluation.
Locator: `differentialHomEquiv` and `localSkyMapLinear`. -/
private def sheafToLocalKaehler (p : X) :
    letI := stalkAlgebra f p
    (differentialSheaf f).presheaf.stalk p →ₗ[X.presheaf.stalk p]
      KaehlerDifferential ℚ (X.presheaf.stalk p) := by
  letI := stalkAlgebra f p
  exact localSkyMapLinear p (KaehlerDifferential ℚ (X.presheaf.stalk p))
    ((differentialHomEquiv f _).symm (localKaehlerSkyDerivation f p))

/-- THEOREM. The inverse map sends a sheaf derivative germ to its local-ring
Kähler derivative. Locator: the sheaf universal property with skyscraper target. -/
private theorem sheafToLocalKaehler_D_germ (p : X) (U : X.Opens) (hp : p ∈ U)
    (a : Γ(X, U)) :
    letI := stalkAlgebra f p
    sheafToLocalKaehler f p ((differentialSheaf f).presheaf.germ U p hp
      ((differentialDerivation f).d (X := op U) a)) =
      D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hp a) := by
  letI := stalkAlgebra f p
  change localSkyMapLinear p (KaehlerDifferential ℚ (X.presheaf.stalk p))
    ((differentialHomEquiv f _).symm (localKaehlerSkyDerivation f p))
      ((differentialSheaf f).presheaf.germ U p hp ((differentialDerivation f).d a)) = _
  rw [localSkyMapLinear_germ]
  exact congrArg (fun s => s ⟨hp⟩) (differentialHomEquiv_symm_app_d f
    (localSky p (KaehlerDifferential ℚ (X.presheaf.stalk p)))
      (localKaehlerSkyDerivation f p) (op U) a)

/-- DEFINITION (proved local isomorphism). The stalk of the actual relative
Kähler differential sheaf is canonically the Kähler module of the actual local
ring, compatibly with both universal derivations. No smoothness is needed.
Locator: Stacks Project, Tag 01UM; the sheaf and local-ring universal properties
and the stalk-to-skyscraper adjunction. -/
def stalkKaehlerEquiv (p : X) :
    letI := stalkAlgebra f p
    KaehlerDifferential ℚ (X.presheaf.stalk p) ≃ₗ[X.presheaf.stalk p]
      (differentialSheaf f).presheaf.stalk p := by
  letI := stalkAlgebra f p
  let Θ := localKaehlerToSheaf f p
  let δ := sheafToLocalKaehler f p
  have hleft : δ ∘ₗ Θ = LinearMap.id := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    obtain ⟨U, hp, a, rfl⟩ := X.presheaf.exists_germ_eq z
    change sheafToLocalKaehler f p
      (localKaehlerToSheaf f p (D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hp a))) =
        D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hp a)
    rw [localKaehlerToSheaf_D_germ, sheafToLocalKaehler_D_germ]
  let M := differentialSheaf f
  let g : M ⟶ localSky p (M.presheaf.stalk p) :=
    toLocalSky p (M.presheaf.stalk p) (Θ ∘ₗ δ)
  let h : M ⟶ localSky p (M.presheaf.stalk p) :=
    toLocalSky p (M.presheaf.stalk p) LinearMap.id
  have hmaps : g = h := by
    apply (differentialHomEquiv f _).injective
    ext U a
    funext hp
    change g.app U.unop ((differentialDerivation f).d a) ⟨hp.down⟩ =
      h.app U.unop ((differentialDerivation f).d a) ⟨hp.down⟩
    rw [show g = toLocalSky p (M.presheaf.stalk p) (Θ ∘ₗ δ) from rfl,
      show h = toLocalSky p (M.presheaf.stalk p) LinearMap.id from rfl,
      toLocalSky_app, toLocalSky_app, LinearMap.comp_apply, LinearMap.id_apply]
    change localKaehlerToSheaf f p (sheafToLocalKaehler f p
      (M.presheaf.germ U.unop p hp.down ((differentialDerivation f).d a))) = _
    rw [sheafToLocalKaehler_D_germ, localKaehlerToSheaf_D_germ]
  refine { Θ with
    invFun := δ
    left_inv := LinearMap.congr_fun hleft
    right_inv := ?_ }
  intro ξ
  obtain ⟨U, hp, s, rfl⟩ := M.presheaf.exists_germ_eq ξ
  have heq := congrArg (fun b : M ⟶ localSky p (M.presheaf.stalk p) => b.app U s ⟨hp⟩) hmaps
  change (toLocalSky p (M.presheaf.stalk p) (Θ ∘ₗ δ)).app U s ⟨hp⟩ =
    (toLocalSky p (M.presheaf.stalk p) LinearMap.id).app U s ⟨hp⟩ at heq
  rw [toLocalSky_app, toLocalSky_app, LinearMap.comp_apply, LinearMap.id_apply] at heq
  exact heq

/-- THEOREM. The canonical stalk isomorphism respects the universal derivative
of every section germ. Locator: `localKaehlerToSheaf_D_germ`. -/
theorem stalkKaehlerEquiv_D_germ (p : X) (U : X.Opens) (hp : p ∈ U) (a : Γ(X, U)) :
    letI := stalkAlgebra f p
    stalkKaehlerEquiv f p (D ℚ (X.presheaf.stalk p) (X.presheaf.germ U p hp a)) =
      (differentialSheaf f).presheaf.germ U p hp ((differentialDerivation f).d (X := op U) a) :=
  localKaehlerToSheaf_D_germ f p U hp a

/-- THEOREM. The canonical local Kähler identifications are proved for every
integral scheme over the rationals; they are not a remaining comparison input.
Locator: `stalkKaehlerEquiv` and its universal-derivation computation. -/
theorem stalkDifferentials : StalkDifferentials := by
  intro X _ f
  exact ⟨{
    equiv := stalkKaehlerEquiv f
    equiv_D_germ := stalkKaehlerEquiv_D_germ f }⟩

end StalkEquivalence

section SchemePlaces

open ZInQ.Contrib.RC53Assist.AbelianCurve

/-- THEOREM. The local ring of a smooth integral rational curve is either a field
or a discrete valuation ring. Locator: `SmoothCurve.lean`,
`smooth_curve_valuation_stalk`, including its local-dimension proof. -/
theorem stalk_isField_or_discreteValuationRing {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (hdim : topologicalKrullDim X = 1) (p : X) :
    IsField (X.presheaf.stalk p) ∨ IsDiscreteValuationRing (X.presheaf.stalk p) := by
  haveI := smooth_stalk_regular f p
  have hle : ringKrullDim (X.presheaf.stalk p) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    have h := Order.coheight_le_krullDim p
    have heq : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    rw [← heq, hdim] at h
    exact_mod_cast h
  by_cases h₁ : ringKrullDim (X.presheaf.stalk p) = 1
  · right
    apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := X.presheaf.stalk p)).mp
      (inferInstance : IsRegularLocalRing (X.presheaf.stalk p))
    rw [h₁] at h
    exact_mod_cast h
  · left
    have h₀ : ringKrullDim (X.presheaf.stalk p) ≤ 0 :=
      ENat.WithBot.lt_add_one_iff.mp (lt_of_le_of_ne hle h₁)
    haveI : Ring.KrullDimLE 0 (X.presheaf.stalk p) := ⟨by exact_mod_cast h₀⟩
    exact Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk p)

/-- DEFINITION. The normalized place attached to a discrete local ring of a curve.
Locator: `IdentityPlace.lean`, `identityPlace`, with the point arbitrary. -/
def stalkPlace {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (p : X) [IsDiscreteValuationRing (X.presheaf.stalk p)] :
    letI := functionFieldAlgebra f
    Place k X.functionField := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  exact Place.ofPrime k X.functionField
    (IsDiscreteValuationRing.maximalIdeal (X.presheaf.stalk p))

/-- THEOREM. The valuation ring of the local-ring place is its actual image
in the function field. Locator: `IdentityPlace.lean`, `identityPlace_integers`;
Mathlib `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`. -/
theorem stalkPlace_integers {k : Type} [Field k] {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of k)) (p : X) [IsDiscreteValuationRing (X.presheaf.stalk p)] :
    letI := functionFieldAlgebra f
    (stalkPlace f p).integers.toSubring =
      (⊤ : Subring (X.presheaf.stalk p)).map
        (algebraMap (X.presheaf.stalk p) X.functionField) := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  rw [stalkPlace, Place.integers_ofPrime,
    IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact (IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring
    (A := X.presheaf.stalk p) (K := X.functionField)).symm

/-- THEOREM. A fraction-field embedding out of a field is surjective.
Locator: Mathlib `IsFractionRing.algEquiv`. -/
private theorem fractionMap_surjective {A K : Type} [Field A] [Field K]
    [Algebra A K] [IsFractionRing A K] : Function.Surjective (algebraMap A K) := by
  let e : A ≃ₐ[A] K := IsFractionRing.algEquiv A A K
  intro z
  obtain ⟨a, ha⟩ := e.surjective z
  refine ⟨a, ?_⟩
  have hc : e a = algebraMap A K a := by simpa using e.commutes a
  exact hc.symm.trans ha

/-- THEOREM. Every place of the actual function field of a smooth proper rational
curve is represented by a discrete local ring on the curve. Properness is used
only through the valuative criterion; no genus or differential comparison is used.
Locator: Silverman Chapter II, §§2 and 4; Mathlib's valuative criterion and
`TauCeti.Place.eq_of_integers_le`. -/
theorem everyPlace_has_stalk_model {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    ∀ P : Place ℚ X.functionField, ∃ p : X,
      IsDiscreteValuationRing (X.presheaf.stalk p) ∧
      P.integers.toSubring = (⊤ : Subring (X.presheaf.stalk p)).map
        (algebraMap (X.presheaf.stalk p) X.functionField) := by
  letI := functionFieldAlgebra f
  intro P
  let i : Spec X.functionField ⟶ Spec (.of P.integers) :=
    Spec.map (CommRingCat.ofHom (algebraMap P.integers X.functionField))
  let s : Spec (.of P.integers) ⟶ Spec (.of ℚ) :=
    Spec.map (CommRingCat.ofHom (algebraMap ℚ P.integers))
  have hsquare : CommSq (fromFunctionField X) i f s := ⟨by
    rw [fromFunctionField_structure]
    dsimp only [i, s]
    rw [← Spec.map_comp]
    congr 1⟩
  have hex : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f)).1
  obtain ⟨⟨l, hl, -⟩⟩ := hex
    { R := P.integers, domain := inferInstance, K := X.functionField,
      i₁ := fromFunctionField X, i₂ := s, commSq := hsquare }
  let p : X := l (IsLocalRing.closedPoint P.integers)
  let φ : X.presheaf.stalk p ⟶ CommRingCat.of P.integers := Scheme.stalkClosedPointTo l
  have hφ : φ ≫ CommRingCat.ofHom (algebraMap P.integers X.functionField) =
      CommRingCat.ofHom (algebraMap (X.presheaf.stalk p) X.functionField) := by
    apply Spec.map_injective
    apply (cancel_mono (X.fromSpecStalk p)).mp
    rw [Spec.map_comp, Category.assoc]
    change i ≫ (Spec.map (Scheme.stalkClosedPointTo l) ≫ X.fromSpecStalk p) = _
    rw [Scheme.Spec_stalkClosedPointTo_fromSpecStalk, hl]
    exact (Scheme.SpecMap_stalkSpecializes_fromSpecStalk (genericPoint_specializes p)).symm
  have hmem : ∀ a : X.presheaf.stalk p,
      algebraMap (X.presheaf.stalk p) X.functionField a ∈ P.integers := by
    intro a
    have heq := ConcreteCategory.congr_hom hφ a
    change (φ a : X.functionField) = algebraMap (X.presheaf.stalk p) X.functionField a at heq
    exact heq ▸ (φ a).2
  rcases stalk_isField_or_discreteValuationRing f hdim p with hp | hp
  · letI := hp.toField
    have hall : ∀ z : X.functionField, z ∈ P.integers := by
      intro z
      obtain ⟨a, rfl⟩ := fractionMap_surjective (A := X.presheaf.stalk p) (K := X.functionField) z
      exact hmem a
    exact (P.integers_ne_top (top_unique fun z _ => hall z)).elim
  · haveI := hp
    let Q : Place ℚ X.functionField := stalkPlace f p
    have hQP : Q.integers ≤ P.integers := by
      change Q.integers.toSubring ≤ P.integers.toSubring
      rw [show Q.integers.toSubring = (⊤ : Subring (X.presheaf.stalk p)).map
        (algebraMap (X.presheaf.stalk p) X.functionField) from stalkPlace_integers f p]
      rintro z ⟨a, -, rfl⟩
      exact hmem a
    have heq : Q = P := Place.eq_of_integers_le hQP
    refine ⟨p, hp, ?_⟩
    rw [← heq]
    exact stalkPlace_integers f p

end SchemePlaces

section RingModels

variable {A B : Type*} [CommRing A] [CommRing B]
  [Algebra k A] [Algebra k B] [Algebra A B] [IsScalarTower k A B]

/-- THEOREM. A bijective algebra map induces a bijective Kähler differential map.
Locator: Mathlib `KaehlerDifferential.ker_map_of_surjective` and
`KaehlerDifferential.map_surjective_of_surjective`. -/
private theorem kaehlerMap_bijective_of_bijective
    (h : Function.Bijective (algebraMap A B)) :
    Function.Bijective (KaehlerDifferential.map k k A B) := by
  refine ⟨?_, KaehlerDifferential.map_surjective_of_surjective k k A B h.2⟩
  rw [← LinearMap.ker_eq_bot, KaehlerDifferential.ker_map_of_surjective k A B h.2]
  have hfs : Function.Injective
      ((Finsupp.mapRange.linearMap (Algebra.linearMap A B)).comp
        (Finsupp.lmapDomain A A (algebraMap A B))) :=
    (Finsupp.mapRange_injective (algebraMap A B) (map_zero _) h.1).comp
      (Finsupp.mapDomain_injective h.1)
  rw [LinearMap.ker_eq_bot.mpr hfs, Submodule.map_bot]

variable [Algebra A F] [IsScalarTower k A F]

/-- DEFINITION. An injective algebra map with image the valuation ring identifies
its source with that actual ring. Locator: `AlgEquiv.ofBijective` and the
local-ring image statement `stalkPlace_integers`. -/
private def modelRingEquiv (P : Place k F)
    (hP : P.integers.toSubring = (⊤ : Subring A).map (algebraMap A F))
    (hinj : Function.Injective (algebraMap A F)) : A ≃ₐ[k] P.integers := by
  let j : A →ₐ[k] P.integers :=
    { toFun := fun a => ⟨algebraMap A F a, by
        change algebraMap A F a ∈ P.integers.toSubring
        rw [hP]
        exact ⟨a, trivial, rfl⟩⟩
      map_zero' := Subtype.ext (map_zero _)
      map_one' := Subtype.ext (map_one _)
      map_add' := fun a b => Subtype.ext (map_add _ a b)
      map_mul' := fun a b => Subtype.ext (map_mul _ a b)
      commutes' := fun c => Subtype.ext
        ((IsScalarTower.algebraMap_apply k A F c).symm.trans
          (P.coe_algebraMap_constants c).symm) }
  refine AlgEquiv.ofBijective j ⟨?_, ?_⟩
  · intro a b hab
    exact hinj (congrArg Subtype.val hab)
  · intro b
    have hb : (b : F) ∈ (⊤ : Subring A).map (algebraMap A F) := by
      rw [← hP]
      exact b.2
    obtain ⟨a, -, ha⟩ := hb
    exact ⟨a, Subtype.ext ha⟩

/-- THEOREM. The model-ring equivalence is the specified inclusion in the
function field. Locator: the definition of `modelRingEquiv`. -/
private theorem modelRingEquiv_val (P : Place k F)
    (hP : P.integers.toSubring = (⊤ : Subring A).map (algebraMap A F))
    (hinj : Function.Injective (algebraMap A F)) (a : A) :
    (modelRingEquiv P hP hinj a : F) = algebraMap A F a := rfl

/-- THEOREM. Changing the ring model without changing its image in the function
field preserves both injectivity and the image of its Kähler localization map.
Locator: the functoriality of Kähler differentials and the universal derivation;
Mathlib `KaehlerDifferential.map_D`. -/
theorem kaehler_local_image_transport (P : Place k F)
    (hP : P.integers.toSubring = (⊤ : Subring A).map (algebraMap A F))
    (hinj : Function.Injective (algebraMap A F))
    (hinjP : Function.Injective (localKaehlerMap P)) :
    Function.Injective (KaehlerDifferential.map k k A F) ∧
      ∀ η : KaehlerDifferential k F,
        η ∈ Set.range (KaehlerDifferential.map k k A F) ↔
          η ∈ (localKaehlerMap P).range := by
  let e := modelRingEquiv P hP hinj
  letI : Algebra A P.integers := e.toRingHom.toAlgebra
  haveI : IsScalarTower k A P.integers :=
    IsScalarTower.of_algebraMap_eq fun c => (e.commutes c).symm
  haveI : IsScalarTower A P.integers F :=
    IsScalarTower.of_algebraMap_eq fun a => (modelRingEquiv_val P hP hinj a).symm
  let m := KaehlerDifferential.map k k A P.integers
  let n := (KaehlerDifferential.map k k P.integers F).restrictScalars A
  have hm : Function.Bijective m :=
    kaehlerMap_bijective_of_bijective (k := k) (A := A) (B := P.integers) e.bijective
  have hc : n ∘ₗ m = KaehlerDifferential.map k k A F := by
    apply Derivation.liftKaehlerDifferential_unique
    ext a
    change KaehlerDifferential.map k k P.integers F
      (KaehlerDifferential.map k k A P.integers (D k A a)) =
        KaehlerDifferential.map k k A F (D k A a)
    rw [KaehlerDifferential.map_D, KaehlerDifferential.map_D, KaehlerDifferential.map_D,
      ← IsScalarTower.algebraMap_apply A P.integers F]
  constructor
  · rw [← hc]
    exact hinjP.comp hm.1
  · intro η
    constructor
    · rintro ⟨ξ, hξ⟩
      exact ⟨m ξ, (LinearMap.congr_fun hc ξ).trans hξ⟩
    · rintro ⟨ζ, hζ⟩
      obtain ⟨ξ, rfl⟩ := hm.2 ζ
      exact ⟨ξ, (LinearMap.congr_fun hc ξ).symm.trans hζ⟩

end RingModels

section CurveComparison

open ZInQ.Contrib.RC53Assist.AbelianCurve

/-- THEOREM. The two local uniformizer facts give injectivity of localization and
identify its image with local regularity for the normalized comparison.
Locator: `localKaehlerMap_injective_of_uniformizerBasis` and
`regularAt_comparison_iff_mem_local_range` above. -/
theorem localComparison_of_uniformizer_facts (hB : LocalUniformizerBasis)
    (hO : UniformizerResidueOrder) (k F : Type) [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    (x : F) (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] (P : Place k F) :
    letI := weilDifferentialSpaceModule hF
    Function.Injective (localKaehlerMap P) ∧
      ∀ η : KaehlerDifferential k F,
        RegularAt P (comparison hF hex hx η) ↔ η ∈ (localKaehlerMap P).range := by
  letI := weilDifferentialSpaceModule hF
  obtain ⟨t, ht, b, hb⟩ := hB k F hF P
  exact ⟨localKaehlerMap_injective_of_uniformizerBasis hF P t ht b hb,
    regularAt_comparison_iff_mem_local_range hF hex hx P t ht b hb
      (hO k F hF hex x hx P t ht)⟩

/-- DEFINITION. The constants-linear map from the Kähler module of a scheme's
local ring to the Kähler module of its actual function field.
Locator: Mathlib `KaehlerDifferential.map`; the scalar towers in `IdentityPlace.lean`. -/
def stalkKaehlerMap {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) (p : X) :
    letI := functionFieldAlgebra f
    letI := stalkAlgebra f p
    letI := stalk_functionField_tower f p
    KaehlerDifferential ℚ (X.presheaf.stalk p) →ₗ[ℚ]
      KaehlerDifferential ℚ X.functionField := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  exact (KaehlerDifferential.map ℚ ℚ (X.presheaf.stalk p) X.functionField).restrictScalars ℚ

/-- THEOREM. Local uniformizer bases imply that every stalk Kähler localization
map on a smooth integral curve is injective. The field case is proved separately.
Locator: `stalk_isField_or_discreteValuationRing`, `stalkPlace_integers`, and
`kaehler_local_image_transport`. -/
theorem stalkKaehlerMap_injective (hB : LocalUniformizerBasis)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℚ)) [Smooth f]
    (hdim : topologicalKrullDim X = 1) (p : X) :
    letI := functionFieldAlgebra f
    Function.Injective (stalkKaehlerMap f p) := by
  letI := functionFieldAlgebra f
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  have hF := isFunctionField_of_dimension_one f hdim
  rcases stalk_isField_or_discreteValuationRing f hdim p with hp | hp
  · letI := hp.toField
    exact (kaehlerMap_bijective_of_bijective (k := ℚ)
      (A := X.presheaf.stalk p) (B := X.functionField)
      ⟨IsFractionRing.injective _ _, fractionMap_surjective⟩).1
  · haveI := hp
    let P : Place ℚ X.functionField := stalkPlace f p
    obtain ⟨t, ht, b, hb⟩ := hB ℚ X.functionField hF P
    exact (kaehler_local_image_transport P (stalkPlace_integers f p)
      (IsFractionRing.injective _ _)
      (localKaehlerMap_injective_of_uniformizerBasis hF P t ht b hb)).1

/-- THEOREM. Regularity at every place is membership in the Kähler localization
image of every actual local ring of a smooth proper geometrically integral curve.
All point-to-place and place-to-point steps are proved, not supplied as inputs.
Locator: Silverman Chapter II, §§4–5; `everyPlace_has_stalk_model` above. -/
theorem regularAt_iff_mem_stalk_ranges (hB : LocalUniformizerBasis)
    (hO : UniformizerResidueOrder) {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) (x : X.functionField)
    (hx : letI := functionFieldAlgebra f; Transcendental ℚ x) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    let hex := functionField_exact_constants f
    letI := hF.finiteDimensional_adjoin hx
    letI := weilDifferentialSpaceModule hF
    ∀ η : KaehlerDifferential ℚ X.functionField,
      (∀ P : Place ℚ X.functionField, RegularAt P (comparison hF hex hx η)) ↔
      ∀ p : X, letI := stalkAlgebra f p
        η ∈ (stalkKaehlerMap f p).range := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  let hex := functionField_exact_constants f
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  dsimp only
  intro η
  constructor
  · intro hη p
    letI := stalkAlgebra f p
    haveI := stalk_functionField_tower f p
    rcases stalk_isField_or_discreteValuationRing f hdim p with hp | hp
    · letI := hp.toField
      exact (kaehlerMap_bijective_of_bijective (k := ℚ)
        (A := X.presheaf.stalk p) (B := X.functionField)
        ⟨IsFractionRing.injective _ _, fractionMap_surjective⟩).2 η
    · haveI := hp
      let P : Place ℚ X.functionField := stalkPlace f p
      have hloc := localComparison_of_uniformizer_facts hB hO ℚ X.functionField
        hF hex x hx P
      exact (kaehler_local_image_transport P (stalkPlace_integers f p)
        (IsFractionRing.injective _ _) hloc.1).2 η |>.mpr ((hloc.2 η).mp (hη P))
  · intro hη P
    obtain ⟨p, hp, hP⟩ := everyPlace_has_stalk_model f hdim P
    letI := stalkAlgebra f p
    haveI := stalk_functionField_tower f p
    have hloc := localComparison_of_uniformizer_facts hB hO ℚ X.functionField
      hF hex x hx P
    exact (hloc.2 η).mpr
      (((kaehler_local_image_transport P hP (IsFractionRing.injective _ _) hloc.1).2 η).mp
        (hη p))

end CurveComparison

section GlobalSections

open ZInQ.Contrib.RC53Assist.AbelianCurve

variable {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℚ))

/-- DEFINITION. Restriction of global sections to the actual generic sheaf stalk,
as a constants-linear map with the specified structure morphism.
Locator: Mathlib `PresheafOfModules.germ_smul`; `DifferentialLine.lean`,
`globalSectionsModule` and `functionFieldAlgebra`. -/
private def genericGermLinear (M : X.Modules) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f M
    letI : Module ℚ (M.presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (algebraMap ℚ X.functionField)
    Γ(M, ⊤) →ₗ[ℚ] M.presheaf.stalk (genericPoint X) := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f M
  letI : Module ℚ (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap ℚ X.functionField)
  refine { toFun := M.presheaf.germ ⊤ (genericPoint X) trivial
           map_add' := map_add _
           map_smul' := ?_ }
  intro c s
  change M.presheaf.germ ⊤ (genericPoint X) trivial ((globalFunctionsMap f c) • s) =
    algebraMap ℚ X.functionField c • M.presheaf.germ ⊤ (genericPoint X) trivial s
  rw [moduleGerm_smul M]
  rfl

/-- DEFINITION. The canonical rational Kähler differential of a global sheaf
section, using the local stalk calculation, not an assumed global equivalence.
Locator: Silverman Chapter II, §§4–5; `DifferentialStalkData.equiv_D_germ`. -/
def rationalRestriction (d : DifferentialStalkData f) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    Γ(differentialSheaf f, ⊤) →ₗ[ℚ] KaehlerDifferential ℚ X.functionField := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  let M := differentialSheaf f
  letI : Module ℚ (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap ℚ X.functionField)
  haveI : IsScalarTower ℚ X.functionField (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e : KaehlerDifferential ℚ X.functionField ≃ₗ[X.functionField]
      M.presheaf.stalk (genericPoint X) := d.equiv (genericPoint X)
  exact (e.symm.restrictScalars ℚ).toLinearMap ∘ₗ genericGermLinear f M

/-- THEOREM. Injectivity of the local Kähler maps implies injectivity of
specialization for the actual differential sheaf stalks.
Locator: the local Kähler identification and `DifferentialStalkData.specializes_equiv`. -/
theorem DifferentialStalkData.specializes_injective (d : DifferentialStalkData f)
    (hinj : letI := functionFieldAlgebra f
      ∀ p : X, Function.Injective (stalkKaehlerMap f p)) :
    ∀ p : X, Function.Injective
      ((differentialSheaf f).presheaf.stalkSpecializes (genericPoint_specializes p)) := by
  letI := functionFieldAlgebra f
  intro p a b hab
  letI := stalkAlgebra f p
  haveI := stalk_functionField_tower f p
  apply (d.equiv p).symm.injective
  apply hinj p
  apply (d.equiv (genericPoint X)).injective
  change d.equiv (genericPoint X)
      (KaehlerDifferential.map ℚ ℚ (X.presheaf.stalk p) X.functionField
        ((d.equiv p).symm a)) =
    d.equiv (genericPoint X)
      (KaehlerDifferential.map ℚ ℚ (X.presheaf.stalk p) X.functionField
        ((d.equiv p).symm b))
  rw [← d.specializes_equiv p, ← d.specializes_equiv p,
    LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  exact hab

/-- THEOREM. Restriction of global sheaf differentials to rational Kähler
differentials is injective once the local Kähler maps are injective.
Locator: the torsion-free sheaf criterion `genericGerm_injective`. -/
theorem rationalRestriction_injective (d : DifferentialStalkData f)
    (hinj : letI := functionFieldAlgebra f
      ∀ p : X, Function.Injective (stalkKaehlerMap f p)) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    Function.Injective (rationalRestriction f d) := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  intro s t hst
  apply genericGerm_injective (differentialSheaf f) (d.specializes_injective f hinj) ⊤
  change (d.equiv (genericPoint X)).symm
      ((differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial s) =
    (d.equiv (genericPoint X)).symm
      ((differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial t) at hst
  exact (d.equiv (genericPoint X)).symm.injective hst

/-- THEOREM. The image of global restriction is exactly membership in every
actual local Kähler image. Its reverse direction is proved by unique sheaf
gluing, not included in any input.
Locator: Silverman Chapter II, §§4–5; `existsUnique_section_of_mem_local_stalks`. -/
theorem rationalRestriction_range_iff_mem_stalk_ranges (d : DifferentialStalkData f)
    (hinj : letI := functionFieldAlgebra f
      ∀ p : X, Function.Injective (stalkKaehlerMap f p)) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ η : KaehlerDifferential ℚ X.functionField,
      η ∈ (rationalRestriction f d).range ↔
        ∀ p : X, letI := stalkAlgebra f p
          η ∈ (stalkKaehlerMap f p).range := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let M := differentialSheaf f
  let e : KaehlerDifferential ℚ X.functionField ≃ₗ[X.functionField]
      M.presheaf.stalk (genericPoint X) := d.equiv (genericPoint X)
  intro η
  constructor
  · rintro ⟨s, rfl⟩ p
    letI := stalkAlgebra f p
    haveI := stalk_functionField_tower f p
    let ξ := (d.equiv p).symm (M.presheaf.germ ⊤ p trivial s)
    refine ⟨ξ, ?_⟩
    apply e.injective
    change d.equiv (genericPoint X)
      (KaehlerDifferential.map ℚ ℚ (X.presheaf.stalk p) X.functionField ξ) =
        e (e.symm (M.presheaf.germ ⊤ (genericPoint X) trivial s))
    rw [LinearEquiv.apply_symm_apply, ← d.specializes_equiv p]
    change M.presheaf.stalkSpecializes (genericPoint_specializes p)
      (d.equiv p ((d.equiv p).symm (M.presheaf.germ ⊤ p trivial s))) = _
    rw [LinearEquiv.apply_symm_apply,
      M.presheaf.germ_stalkSpecializes_apply (U := ⊤) (y := p)
        trivial (genericPoint_specializes p)]
  · intro hη
    let q : M.presheaf.stalk (genericPoint X) := e η
    have hlocal : ∀ p ∈ (⊤ : X.Opens), q ∈ Set.range
        (M.presheaf.stalkSpecializes (genericPoint_specializes p)) := by
      intro p _
      letI := stalkAlgebra f p
      haveI := stalk_functionField_tower f p
      obtain ⟨ξ, hξ⟩ := hη p
      refine ⟨d.equiv p ξ, ?_⟩
      exact (d.specializes_equiv p ξ).trans (congrArg e hξ)
    obtain ⟨s, hs, -⟩ := existsUnique_section_of_mem_local_stalks M
      (d.specializes_injective f hinj) ⊤ q hlocal
    refine ⟨s, ?_⟩
    change e.symm (M.presheaf.germ ⊤ (genericPoint X) trivial s) = η
    rw [hs]
    exact e.symm_apply_apply η

end GlobalSections

/-- THEOREM (reduction of the regular-differential input). The exact
`AbelianCurve.RegularDifferentialComparison` follows from three strictly local
standard facts: the stalk calculation of the actual sheafified differentials,
a uniformizer basis for the actual valuation-ring Kähler module, and the order
zero of `dt` under the normalized cotrace comparison. The generic restriction,
its injectivity, both directions of regularity, proper place coverage, and
unique global gluing are proved here. No global comparison is an input.
Locator: Silverman Chapter II, §§4–5; Stichtenoth §§I.5 and I.7. -/
theorem regularDifferentialComparison_of_local_inputs
    (hS : StalkDifferentials) (hB : LocalUniformizerBasis) (hO : UniformizerResidueOrder) :
    ZInQ.Contrib.RC53Assist.AbelianCurve.RegularDifferentialComparison := by
  intro X _ f _ _ _ hdim
  letI := ZInQ.Contrib.RC53Assist.AbelianCurve.functionFieldAlgebra f
  letI := ZInQ.Contrib.RC53Assist.AbelianCurve.globalSectionsModule f
    (ZInQ.Contrib.RC53Assist.AbelianCurve.differentialSheaf f)
  obtain ⟨d⟩ := hS X f
  have hinj : ∀ p : X, Function.Injective (stalkKaehlerMap f p) :=
    stalkKaehlerMap_injective hB f hdim
  have hRinj := rationalRestriction_injective f d hinj
  let hF := ZInQ.Contrib.RC53Assist.AbelianCurve.isFunctionField_of_dimension_one f hdim
  let hex := ZInQ.Contrib.RC53Assist.AbelianCurve.functionField_exact_constants f
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  haveI := isScalarTower_weilDifferentialSpace hF
  let φ := (comparison hF hex hx).restrictScalars ℚ
  let L : Γ(ZInQ.Contrib.RC53Assist.AbelianCurve.differentialSheaf f, ⊤) →ₗ[ℚ]
      Module.Dual ℚ ↥(repartitionSpace ℚ X.functionField) :=
    (weilDifferentialSpace ℚ X.functionField).subtype ∘ₗ φ.toLinearMap ∘ₗ
      rationalRestriction f d
  let W := weilDifferentialFiltration (0 : Divisor ℚ X.functionField)
  have hLmem : ∀ s, L s ∈ W := by
    intro s
    change (φ (rationalRestriction f d s) : Module.Dual ℚ
      ↥(repartitionSpace ℚ X.functionField)) ∈ W
    rw [mem_zeroFiltration_iff_regularAt]
    exact (regularAt_iff_mem_stalk_ranges hB hO f hdim x hx
      (rationalRestriction f d s)).mpr
        ((rationalRestriction_range_iff_mem_stalk_ranges f d hinj
          (rationalRestriction f d s)).mp ⟨s, rfl⟩)
  let L₀ := L.codRestrict W hLmem
  have hLinj : Function.Injective L₀ := by
    intro s t hst
    have hv := congrArg (fun z : W => (z : Module.Dual ℚ
      ↥(repartitionSpace ℚ X.functionField))) hst
    change L s = L t at hv
    apply hRinj
    apply φ.injective
    exact Subtype.ext hv
  have hLsurj : Function.Surjective L₀ := by
    intro ω
    let w : ↥(weilDifferentialSpace ℚ X.functionField) :=
      ⟨ω, weilDifferentialFiltration_le_weilDifferentialSpace _ ω.2⟩
    let η : KaehlerDifferential ℚ X.functionField := φ.symm w
    have hmem : (φ η : Module.Dual ℚ ↥(repartitionSpace ℚ X.functionField)) ∈ W := by
      change (φ (φ.symm w) : Module.Dual ℚ ↥(repartitionSpace ℚ X.functionField)) ∈ W
      rw [LinearEquiv.apply_symm_apply]
      exact ω.2
    have hregular : ∀ P : Place ℚ X.functionField, RegularAt P (comparison hF hex hx η) :=
      (mem_zeroFiltration_iff_regularAt (φ η)).mp hmem
    have hrange := (rationalRestriction_range_iff_mem_stalk_ranges f d hinj η).mpr
      ((regularAt_iff_mem_stalk_ranges hB hO f hdim x hx η).mp hregular)
    obtain ⟨s, hs⟩ := hrange
    refine ⟨s, Subtype.ext ?_⟩
    change (φ (rationalRestriction f d s) : Module.Dual ℚ
      ↥(repartitionSpace ℚ X.functionField)) = (ω : Module.Dual ℚ
        ↥(repartitionSpace ℚ X.functionField))
    rw [hs]
    exact congrArg Subtype.val (φ.apply_symm_apply w)
  exact ⟨LinearEquiv.ofBijective L₀ ⟨hLinj, hLsurj⟩⟩

/-- THEOREM (reduction to two local field facts). The exact regular-differential
comparison needs only a uniformizer basis for the actual valuation-ring Kähler
module and the single normalized comparison order identity `ord_P(dt) = 0`.
The stalk comparison is proved, not an input. No statement about global regular
sections, genus, or a Weierstrass model occurs in the remaining hypotheses.
Locator: Silverman Chapter II, §§4–5; Stichtenoth §§I.5 and I.7. -/
theorem regularDifferentialComparison_of_uniformizer_inputs
    (hB : LocalUniformizerBasis) (hO : UniformizerResidueOrder) :
    ZInQ.Contrib.RC53Assist.AbelianCurve.RegularDifferentialComparison :=
  regularDifferentialComparison_of_local_inputs stalkDifferentials hB hO

/-- THEOREM (S2a differential reduction). The genus-one conclusion for the actual
smooth proper integral group curve no longer takes the global regular-differential
comparison as an input. Its replacement consists only of the two local uniformizer
facts. The invariant differential trivialization remains explicit.
Locator: `AbelianCurve.abelian_genus_one_of_differentials`; Milne IV.6.4(a)–(b)
and IV.6.6; Silverman Chapter II, §§4–5. -/
theorem abelian_genus_one_of_uniformizer_inputs
    (hT : ZInQ.Contrib.RC53Assist.AbelianCurve.InvariantDifferentialTrivialization)
    (hB : LocalUniformizerBasis) (hO : UniformizerResidueOrder)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := ZInQ.Contrib.RC53Assist.AbelianCurve.functionFieldAlgebra G.hom
    TauCeti.genus ℚ G.left.functionField = 1 :=
  ZInQ.Contrib.RC53Assist.AbelianCurve.abelian_genus_one_of_differentials hT
    (regularDifferentialComparison_of_uniformizer_inputs hB hO) G hdim

section FieldNaturality

variable {k F F' : Type*} [Field k] [Field F] [Field F'] [Algebra k F] [Algebra k F']

/-- DEFINITION. The Kähler pullback along a field isomorphism is induced by its
actual algebra map and the universal derivation.
Locator: Mathlib `KaehlerDifferential.map`; it is not defined by conjugating comparisons. -/
def kaehlerFieldTransport (σ : F ≃ₐ[k] F') :
    KaehlerDifferential k F →ₗ[k] KaehlerDifferential k F' := by
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  exact (KaehlerDifferential.map k k F F').restrictScalars k

/-- THEOREM. Field pullback takes `da` to the differential of the actual image
of `a`. Locator: Mathlib `KaehlerDifferential.map_D`. -/
theorem kaehlerFieldTransport_D (σ : F ≃ₐ[k] F') (a : F) :
    kaehlerFieldTransport σ (D k F a) = D k F' (σ a) := by
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  exact KaehlerDifferential.map_D k k F F' a

/-- THEOREM. Kähler pullback is semilinear for the specified field isomorphism.
Locator: the scalar law of `KaehlerDifferential.map`. -/
theorem kaehlerFieldTransport_smul (σ : F ≃ₐ[k] F') (a : F) (η : KaehlerDifferential k F) :
    kaehlerFieldTransport σ (a • η) = σ a • kaehlerFieldTransport σ η := by
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  change KaehlerDifferential.map k k F F' (a • η) = _
  rw [map_smul]
  exact (algebraMap_smul F' a (KaehlerDifferential.map k k F F' η)).symm

/-- THEOREM. A field isomorphism presents the target as a finite-dimensional
algebra over the source. Locator: `Module.Finite.of_surjective`. -/
private theorem fieldIso_finiteDimensional (σ : F ≃ₐ[k] F') :
    letI : Algebra F F' := σ.toRingHom.toAlgebra
    FiniteDimensional F F' := by
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  exact Module.Finite.of_surjective (Algebra.linearMap F F') σ.surjective

/-- THEOREM. The algebra extension presented by a field isomorphism is separable.
Locator: transport of the identity extension by `Algebra.IsSeparable.of_equiv_equiv`. -/
private theorem fieldIso_isSeparable (σ : F ≃ₐ[k] F') :
    letI : Algebra F F' := σ.toRingHom.toAlgebra
    Algebra.IsSeparable F F' := by
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  exact Algebra.IsSeparable.of_equiv_equiv (RingEquiv.refl F) σ.toRingEquiv (by
    ext a
    rfl)

variable [CharZero k]

/-- DEFINITION. Weil pullback along a field isomorphism is the actual cotrace
for the degree-one extension given by that isomorphism.
Locator: Stichtenoth III.4; `TauCeti.weilDifferentialCotrace` and its trace-pairing characterization. -/
def weilFieldTransport (σ : F ≃ₐ[k] F') (hF : IsFunctionField k F)
    (hF' : IsFunctionField k F') :
    ↥(weilDifferentialSpace k F) →ₗ[k] ↥(weilDifferentialSpace k F') := by
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  haveI := fieldIso_finiteDimensional σ
  haveI := fieldIso_isSeparable σ
  exact weilDifferentialCotrace k F' hF hF'

/-- THEOREM. Weil transport is semilinear for the actual field isomorphism.
Locator: Stichtenoth Proposition III.4.11(a); `TauCeti.weilDifferentialCotrace_smul`. -/
theorem weilFieldTransport_smul (σ : F ≃ₐ[k] F') (hF : IsFunctionField k F)
    (hF' : IsFunctionField k F') (a : F) (ω : ↥(weilDifferentialSpace k F)) :
    letI := weilDifferentialSpaceModule hF
    letI := weilDifferentialSpaceModule hF'
    weilFieldTransport σ hF hF' (a • ω) = σ a • weilFieldTransport σ hF hF' ω := by
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  haveI := fieldIso_finiteDimensional σ
  haveI := fieldIso_isSeparable σ
  letI := weilDifferentialSpaceModule hF
  letI := weilDifferentialSpaceModule hF'
  exact weilDifferentialCotrace_smul hF hF' a ω

/-- THEOREM. Transport of the normalized separating differential is the
normalized differential of the transported parameter. This uses transitivity
of cotrace, not an arbitrary linear equivalence.
Locator: Stichtenoth Proposition III.4.11(b); the rational-function embedding naturality
`TauCeti.map_algebraMap_ratFuncAlgebraOfTranscendental`. -/
theorem differentialOfSeparating_fieldTransport (σ : F ≃ₐ[k] F')
    (hF : IsFunctionField k F) (hF' : IsFunctionField k F') {x : F}
    (hx : Transcendental k x) :
    let hx' := hx.algHom σ σ.injective
    letI := hF.finiteDimensional_adjoin hx
    letI := hF'.finiteDimensional_adjoin hx'
    weilFieldTransport σ hF hF' (differentialOfSeparating hF hx) =
      differentialOfSeparating hF' hx' := by
  let hx' := hx.algHom σ σ.injective
  haveI := hF.finiteDimensional_adjoin hx
  haveI := hF'.finiteDimensional_adjoin hx'
  letI := ratFuncAlgebraOfTranscendental hx
  letI := ratFuncAlgebraOfTranscendental hx'
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hx
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hx'
  haveI := isFunctionField_iff_functionField.mp hF
  haveI := isFunctionField_iff_functionField.mp hF'
  haveI := isSeparable_ratFuncAlgebraOfTranscendental hx
  haveI := isSeparable_ratFuncAlgebraOfTranscendental hx'
  letI : Algebra F F' := σ.toRingHom.toAlgebra
  haveI : IsScalarTower k F F' := IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  haveI := fieldIso_finiteDimensional σ
  haveI := fieldIso_isSeparable σ
  haveI : IsScalarTower (RatFunc k) F F' :=
    IsScalarTower.of_algebraMap_eq fun r =>
      (map_algebraMap_ratFuncAlgebraOfTranscendental σ σ.injective hx r).symm
  change weilDifferentialCotrace k F' hF hF'
    (weilDifferentialCotrace k F (IsFunctionField.ratFunc k) hF
      ⟨rationalDifferential k, rationalDifferential_mem k⟩) =
    weilDifferentialCotrace k F' (IsFunctionField.ratFunc k) hF'
      ⟨rationalDifferential k, rationalDifferential_mem k⟩
  exact weilDifferentialCotrace_weilDifferentialCotrace
    (IsFunctionField.ratFunc k) hF hF' _

/-- THEOREM. The normalized Kähler–Weil comparison commutes with the actual
Kähler and Weil pullbacks along a field isomorphism, with the separating
parameter transported by that isomorphism.
Locator: the universal derivative basis and cotrace transitivity, Stichtenoth III.4.11. -/
theorem comparison_fieldTransport (σ : F ≃ₐ[k] F')
    (hF : IsFunctionField k F) (hF' : IsFunctionField k F')
    (hex : IsIntegrallyClosedIn k F) (hex' : IsIntegrallyClosedIn k F') {x : F}
    (hx : Transcendental k x) :
    let hx' := hx.algHom σ σ.injective
    letI := hF.finiteDimensional_adjoin hx
    letI := hF'.finiteDimensional_adjoin hx'
    letI := weilDifferentialSpaceModule hF
    letI := weilDifferentialSpaceModule hF'
    ∀ η : KaehlerDifferential k F,
      weilFieldTransport σ hF hF' (comparison hF hex hx η) =
        comparison hF' hex' hx' (kaehlerFieldTransport σ η) := by
  let hx' := hx.algHom σ σ.injective
  haveI := hF.finiteDimensional_adjoin hx
  haveI := hF'.finiteDimensional_adjoin hx'
  letI := weilDifferentialSpaceModule hF
  letI := weilDifferentialSpaceModule hF'
  dsimp only
  intro η
  let b := kaehlerBasisOfSeparating hx
  let a : F := b.repr η ()
  have hη : a • D k F x = η := by
    simpa only [a, b, Fintype.sum_unique, kaehlerBasisOfSeparating_apply] using b.sum_repr η
  rw [← hη, (comparison hF hex hx).map_smul, weilFieldTransport_smul,
    kaehlerFieldTransport_smul, (comparison hF' hex' hx').map_smul,
    kaehlerFieldTransport_D, comparison_D_self hF hex hx,
    comparison_D_self hF' hex' hx', differentialOfSeparating_fieldTransport]

end FieldNaturality

section CanonicalComparison

open ZInQ.Contrib.RC53Assist.AbelianCurve

/-- DEFINITION. The proved, canonical local differential identifications,
with their universal-derivation computation attached.
Locator: `stalkKaehlerEquiv` and `stalkKaehlerEquiv_D_germ`. -/
def canonicalDifferentialStalkData {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) : DifferentialStalkData f :=
  { equiv := stalkKaehlerEquiv f
    equiv_D_germ := stalkKaehlerEquiv_D_germ f }

/-- DEFINITION. The actual restriction of a global sheaf differential to the
Kähler module of the actual function field, without a chosen sheaf isomorphism.
Locator: the proved stalk calculation and restriction to the generic point. -/
def canonicalRationalRestriction {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    Γ(differentialSheaf f, ⊤) →ₗ[ℚ] KaehlerDifferential ℚ X.functionField :=
  rationalRestriction f (canonicalDifferentialStalkData f)

/-- DEFINITION. The zero-divisor regular Weil subspace, inside the space of
all Weil differentials. Locator: `TauCeti.weilDifferentialFiltration` at zero. -/
def holomorphicWeilSubmodule {k F : Type*} [Field k] [Field F] [Algebra k F] :
    Submodule k ↥(weilDifferentialSpace k F) :=
  (weilDifferentialFiltration (0 : Divisor k F)).comap (weilDifferentialSpace k F).subtype

/-- DEFINITION. The specified mathematical comparison: restriction of a global
sheaf differential to the generic Kähler module, followed by normalized cotrace.
The separating parameter is specified and is transported along an isomorphism.
Locator: Silverman II, §§4–5; the normalized Kähler–Weil comparison `comparison`. -/
def canonicalWeilComparison {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) (x : X.functionField)
    (hx : letI := functionFieldAlgebra f; Transcendental ℚ x) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := hF.finiteDimensional_adjoin hx
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    Γ(differentialSheaf f, ⊤) →ₗ[ℚ] ↥(weilDifferentialSpace ℚ X.functionField) := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  haveI := isScalarTower_weilDifferentialSpace hF
  letI := globalSectionsModule f (differentialSheaf f)
  exact ((comparison hF (functionField_exact_constants f) hx).restrictScalars ℚ).toLinearMap
    ∘ₗ canonicalRationalRestriction f

/-- THEOREM. The specified generic-restriction–cotrace map is injective under
the local uniformizer-basis fact. No abstract global equivalence is used.
Locator: `rationalRestriction_injective` and the injectivity of `comparison`. -/
theorem canonicalWeilComparison_injective (hB : LocalUniformizerBasis)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) (x : X.functionField)
    (hx : letI := functionFieldAlgebra f; Transcendental ℚ x) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := hF.finiteDimensional_adjoin hx
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    Function.Injective (canonicalWeilComparison f hdim x hx) := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  haveI := isScalarTower_weilDifferentialSpace hF
  letI := globalSectionsModule f (differentialSheaf f)
  exact (comparison hF (functionField_exact_constants f) hx).injective.comp
    (rationalRestriction_injective f (canonicalDifferentialStalkData f)
      (stalkKaehlerMap_injective hB f hdim))

/-- THEOREM. The image of the specified comparison is exactly the zero-divisor
Weil filtration, not merely a vector space of the same dimension.
Locator: the intersection-of-stalks theorem and the local uniformizer order criterion. -/
theorem canonicalWeilComparison_range (hB : LocalUniformizerBasis)
    (hO : UniformizerResidueOrder) {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) (x : X.functionField)
    (hx : letI := functionFieldAlgebra f; Transcendental ℚ x) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := hF.finiteDimensional_adjoin hx
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    (canonicalWeilComparison f hdim x hx).range =
      holomorphicWeilSubmodule (k := ℚ) (F := X.functionField) := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  let hex := functionField_exact_constants f
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  haveI := isScalarTower_weilDifferentialSpace hF
  letI := globalSectionsModule f (differentialSheaf f)
  let d := canonicalDifferentialStalkData f
  have hinj : ∀ p : X, Function.Injective (stalkKaehlerMap f p) :=
    stalkKaehlerMap_injective hB f hdim
  let φ := (comparison hF hex hx).restrictScalars ℚ
  ext ω
  change (∃ s, φ (rationalRestriction f d s) = ω) ↔
    (ω : Module.Dual ℚ ↥(repartitionSpace ℚ X.functionField)) ∈
      weilDifferentialFiltration (0 : Divisor ℚ X.functionField)
  constructor
  · rintro ⟨s, rfl⟩
    rw [mem_zeroFiltration_iff_regularAt]
    exact (regularAt_iff_mem_stalk_ranges hB hO f hdim x hx
      (rationalRestriction f d s)).mpr
        ((rationalRestriction_range_iff_mem_stalk_ranges f d hinj
          (rationalRestriction f d s)).mp ⟨s, rfl⟩)
  · intro hω
    let η := φ.symm ω
    have hreg : ∀ P : Place ℚ X.functionField, RegularAt P (comparison hF hex hx η) := by
      change ∀ P, RegularAt P (φ (φ.symm ω))
      rw [LinearEquiv.apply_symm_apply]
      exact (mem_zeroFiltration_iff_regularAt ω).mp hω
    obtain ⟨s, hs⟩ := (rationalRestriction_range_iff_mem_stalk_ranges f d hinj η).mpr
      ((regularAt_iff_mem_stalk_ranges hB hO f hdim x hx η).mp hreg)
    exact ⟨s, (congrArg φ hs).trans (φ.apply_symm_apply ω)⟩

/-- DEFINITION. The canonical regular-differential comparison records injectivity
and the exact image of the specified generic-restriction–cotrace map. The
construction retains its parameter and universal-derivation compatibility.
Locator: Silverman II, §§4–5; `canonicalWeilComparison`. -/
def RegularDifferentialComparisonImage : Prop :=
  ∀ (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f] (hdim : topologicalKrullDim X = 1)
    (x : X.functionField) (hx : letI := functionFieldAlgebra f; Transcendental ℚ x),
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := hF.finiteDimensional_adjoin hx
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    Function.Injective (canonicalWeilComparison f hdim x hx) ∧
      (canonicalWeilComparison f hdim x hx).range =
        holomorphicWeilSubmodule (k := ℚ) (F := X.functionField)

/-- THEOREM. The two precisely local uniformizer facts give the canonical
comparison, retaining the actual map and its exact image.
Locator: `canonicalWeilComparison_injective` and `canonicalWeilComparison_range`. -/
theorem regularDifferentialComparisonImage_of_uniformizer_inputs
    (hB : LocalUniformizerBasis) (hO : UniformizerResidueOrder) :
    RegularDifferentialComparisonImage := by
  intro X _ f _ _ _ hdim x hx
  exact ⟨canonicalWeilComparison_injective hB f hdim x hx,
    canonicalWeilComparison_range hB hO f hdim x hx⟩

/-- THEOREM. The canonical comparison implies the pre-existing dimension-form
comparison by restricting its actual map to its proved image.
Locator: `LinearEquiv.ofBijective`; no dimension argument defines the map. -/
theorem RegularDifferentialComparisonImage.implies_dimension
    (hC : RegularDifferentialComparisonImage) :
    ZInQ.Contrib.RC53Assist.AbelianCurve.RegularDifferentialComparison := by
  intro X _ f _ _ _ hdim
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  let hF := isFunctionField_of_dimension_one f hdim
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  obtain ⟨hinj, hrange⟩ := hC X f hdim x hx
  let L := (weilDifferentialSpace ℚ X.functionField).subtype ∘ₗ
    canonicalWeilComparison f hdim x hx
  let V := weilDifferentialFiltration (0 : Divisor ℚ X.functionField)
  have hmem : ∀ s, L s ∈ V := by
    intro s
    have hs : canonicalWeilComparison f hdim x hx s ∈
        holomorphicWeilSubmodule (k := ℚ) (F := X.functionField) :=
      hrange ▸ ⟨s, rfl⟩
    exact hs
  let L₀ := L.codRestrict V hmem
  refine ⟨LinearEquiv.ofBijective L₀ ⟨?_, ?_⟩⟩
  · intro s t hst
    apply hinj
    have heq := congrArg (fun z : V =>
      (z : Module.Dual ℚ ↥(repartitionSpace ℚ X.functionField))) hst
    exact Subtype.ext heq
  · intro ω
    let w : ↥(weilDifferentialSpace ℚ X.functionField) :=
      ⟨ω, weilDifferentialFiltration_le_weilDifferentialSpace _ ω.2⟩
    have hw : w ∈ (canonicalWeilComparison f hdim x hx).range := by
      rw [hrange]
      exact ω.2
    obtain ⟨s, hs⟩ := hw
    refine ⟨s, Subtype.ext ?_⟩
    exact congrArg (fun z : ↥(weilDifferentialSpace ℚ X.functionField) =>
      (z : Module.Dual ℚ ↥(repartitionSpace ℚ X.functionField))) hs

end CanonicalComparison

section SchemePullback

open ZInQ.Contrib.RC53Assist.AbelianCurve
open PresheafOfModulesOfCommRing

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

/-- THEOREM. The actual relative sheaf derivative vanishes on every base
structure-sheaf pullback. Locator: the inverse-image adjunction and the relative
universal derivation, Stacks Project Tag 01UM. -/
private theorem differentialDerivation_app (f : X ⟶ Spec (.of ℚ))
    (V : (Spec (.of ℚ)).Opens) (a : Γ(Spec (.of ℚ), V)) :
    (differentialDerivation f).d (X := op (f ⁻¹ᵁ V)) (f.app V a) = 0 := by
  rw [Scheme.Hom.app_eq_appLE, inverseImageMap_appLE_factor]
  exact PresheafOfModulesOfCommRing.Derivation'.d_app (differentialDerivation f) _

/-- DEFINITION. A restriction-compatible derivation which vanishes on all base
pullbacks is a relative derivation for the inverse-image structure presheaf.
Locator: its filtered base-open representatives and Stacks Project Tag 01UM. -/
private def relativeDerivationMk (g : Y ⟶ Spec (.of ℚ)) (M : Y.Modules)
    (d : ∀ {U : Y.Opensᵒᵖ}, Y.presheaf.obj U →+ M.val.obj U)
    (dmul : ∀ {U : Y.Opensᵒᵖ} (a b : Y.presheaf.obj U),
      d (a * b) = a • d b + b • d a)
    (dmap : ∀ {U V : Y.Opensᵒᵖ} (i : U ⟶ V) (a : Y.presheaf.obj U),
      d (Y.presheaf.map i a) = M.presheaf.map i (d a))
    (dapp : ∀ (V : (Spec (.of ℚ)).Opens) (a : Γ(Spec (.of ℚ), V)),
      d (U := op (g ⁻¹ᵁ V)) (g.app V a) = 0) :
    PresheafOfModulesOfCommRing.Derivation' M.val (inverseImageStructureMap g) where
  d := d
  d_mul := dmul
  d_map := dmap
  d_app {W} b := by
    obtain ⟨V, h, a, ha⟩ := inverseImageStructureMap_exists_appLE g W.unop b
    change d ((inverseImageStructureMap g).app W b) = 0
    rw [ha]
    change d (Y.presheaf.map (homOfLE h).op (g.app V a)) = 0
    rw [dmap, dapp, map_zero]

/-- DEFINITION. The actual pullback of sheaf differentials sends `da` to
`d(i* a)` through the universal relative derivation. It is defined before any
Kähler–Weil comparison and before any genus or holomorphic-dimension calculation.
Locator: the universal property of relative differentials, Stacks Project Tag 01UM. -/
def differentialPullbackSheaf (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ))
    (i : X ⟶ Y) (hi : i ≫ g = f) :
    differentialSheaf g ⟶ (Scheme.Modules.pushforward i).obj (differentialSheaf f) := by
  subst f
  refine (differentialHomEquiv g _).symm ?_
  refine relativeDerivationMk g _
    (fun {U} => ((differentialDerivation (i ≫ g)).d (X := op (i ⁻¹ᵁ U.unop))).comp
      (i.app U.unop).hom.toAddMonoidHom) ?_ ?_ ?_
  · intro U a b
    change (differentialDerivation (i ≫ g)).d (i.app U.unop (a * b)) =
      i.app U.unop a • (differentialDerivation (i ≫ g)).d (i.app U.unop b) +
        i.app U.unop b • (differentialDerivation (i ≫ g)).d (i.app U.unop a)
    rw [map_mul]
    exact (differentialDerivation (i ≫ g)).d_mul _ _
  · intro U V j a
    change (differentialDerivation (i ≫ g)).d (i.app V.unop (Y.presheaf.map j a)) =
      (differentialSheaf (i ≫ g)).presheaf.map ((Opens.map i.base).map j.unop).op
        ((differentialDerivation (i ≫ g)).d (i.app U.unop a))
    rw [← ConcreteCategory.comp_apply, i.naturality, ConcreteCategory.comp_apply]
    exact (differentialDerivation (i ≫ g)).d_map _ _
  · intro V a
    exact differentialDerivation_app (i ≫ g) V a

/-- THEOREM. The sheaf pullback has its actual universal-derivation computation
on every open, not only on global functions.
Locator: `differentialHomEquiv_symm_app_d`. -/
theorem differentialPullbackSheaf_D (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ))
    (i : X ⟶ Y) (hi : i ≫ g = f) (U : Y.Opens) (a : Γ(Y, U)) :
    (differentialPullbackSheaf f g i hi).app U ((differentialDerivation g).d (X := op U) a) =
      (differentialDerivation f).d (X := op (i ⁻¹ᵁ U)) (i.app U a) := by
  subst f
  exact differentialHomEquiv_symm_app_d g _ _ (op U) a

/-- DEFINITION. Global pullback of sheaf differentials, using the actual sheaf
pullback and the identity `i⁻¹(⊤) = ⊤`. Rational scalar compatibility follows
from the structure maps, not from a comparison isomorphism.
Locator: `differentialPullbackSheaf` and Mathlib `Scheme.Modules.map_smul`. -/
def globalDifferentialPullback (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ))
    (i : X ⟶ Y) (hi : i ≫ g = f) :
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    Γ(differentialSheaf g, ⊤) →ₗ[ℚ] Γ(differentialSheaf f, ⊤) := by
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  let M := differentialSheaf f
  let α := differentialPullbackSheaf f g i hi
  let e : (⊤ : X.Opens) ⟶ i ⁻¹ᵁ (⊤ : Y.Opens) := eqToHom (Opens.map_top i.base).symm
  let ρ := M.presheaf.map e.op
  have hscalar (c : ℚ) : X.presheaf.map e.op (i.app ⊤ (globalFunctionsMap g c)) =
      globalFunctionsMap f c := by
    exact RingHom.congr_fun
      (RingHom.ext_rat ((X.presheaf.map e.op).hom.comp
        ((i.app ⊤).hom.comp (globalFunctionsMap g))) (globalFunctionsMap f)) c
  refine { toFun := fun s => ρ (α.app ⊤ s)
           map_add' := ?_
           map_smul' := ?_ }
  · intro s t
    simp only [map_add]
  · intro c s
    change ρ (α.app ⊤ ((globalFunctionsMap g c) • s)) =
      globalFunctionsMap f c • ρ (α.app ⊤ s)
    rw [α.app_smul]
    let t : Γ(M, i ⁻¹ᵁ (⊤ : Y.Opens)) := α.app ⊤ s
    change M.presheaf.map e.op (i.app ⊤ (globalFunctionsMap g c) • t) =
      globalFunctionsMap f c • M.presheaf.map e.op t
    rw [M.map_smul, hscalar]

/-- DEFINITION. The actual field isomorphism induced by a curve isomorphism.
The inverse is the field pullback of the inverse scheme isomorphism.
Locator: `Scheme.Hom.functionFieldMap_comp` and `functionFieldMap_id`. -/
def curveFunctionFieldEquiv (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    Y.functionField ≃ₐ[ℚ] X.functionField := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  have hl : i.hom.functionFieldMap ≫ i.inv.functionFieldMap = 𝟙 Y.functionField := by
    simpa only [i.inv_hom_id, Scheme.Hom.functionFieldMap_id] using
      (Scheme.Hom.functionFieldMap_comp i.inv i.hom).symm
  have hr : i.inv.functionFieldMap ≫ i.hom.functionFieldMap = 𝟙 X.functionField := by
    simpa only [i.hom_inv_id, Scheme.Hom.functionFieldMap_id] using
      (Scheme.Hom.functionFieldMap_comp i.hom i.inv).symm
  exact {
    i.hom.functionFieldMap.hom with
    invFun := i.inv.functionFieldMap.hom
    left_inv := ConcreteCategory.congr_hom hl
    right_inv := ConcreteCategory.congr_hom hr
    commutes' := fun c => RingHom.congr_fun
      (RingHom.ext_rat (i.hom.functionFieldMap.hom.comp (algebraMap ℚ Y.functionField))
        (algebraMap ℚ X.functionField)) c }

/-- THEOREM. The curve field isomorphism sends a rational function germ to the
germ of its actual sheaf pullback.
Locator: `Scheme.Hom.germToFunctionField_functionFieldMap`. -/
theorem curveFunctionFieldEquiv_germ (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ))
    (i : X ≅ Y) (U : Y.Opens) (hp : genericPoint Y ∈ U) (a : Γ(Y, U)) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    curveFunctionFieldEquiv f g i (Y.presheaf.germ U (genericPoint Y) hp a) =
      X.presheaf.germ (i.hom ⁻¹ᵁ U) (genericPoint X)
        (by change i.hom (genericPoint X) ∈ U
            rw [i.hom.genericPoint_eq_of_isDominant]
            exact hp) (i.hom.app U a) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  haveI : Nonempty U := ⟨⟨genericPoint Y, hp⟩⟩
  exact ConcreteCategory.congr_hom (i.hom.germToFunctionField_functionFieldMap U) a

end SchemePullback

section GenericPullback

open ZInQ.Contrib.RC53Assist.AbelianCurve

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

/-- THEOREM. An isomorphism pulls a generic-point neighborhood back to a
neighborhood of the generic point. Locator: the generic point of a dominant morphism. -/
private theorem generic_mem_iso_preimage (i : X ≅ Y) (U : Y.Opens)
    (hp : genericPoint Y ∈ U) : genericPoint X ∈ i.hom ⁻¹ᵁ U := by
  change i.hom (genericPoint X) ∈ U
  rw [i.hom.genericPoint_eq_of_isDominant]
  exact hp

/-- DEFINITION. The stalk pullback induced by the actual sheaf differential
pullback, defined as compatible maps on neighborhoods of the generic point.
Locator: the stalk colimit and naturality of a sheaf morphism. -/
private def genericDifferentialPullbackCocone (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    Cocone ((OpenNhds.inclusion (genericPoint Y)).op ⋙ (differentialSheaf g).presheaf) where
  pt := (differentialSheaf f).presheaf.stalk (genericPoint X)
  ι :=
    { app := fun U => (differentialPullbackSheaf f g i.hom hi).app U.unop.1 ≫
        (differentialSheaf f).presheaf.germ (i.hom ⁻¹ᵁ U.unop.1) (genericPoint X)
          (generic_mem_iso_preimage i U.unop.1 U.unop.2)
      naturality := by
        intro U V j
        ext s
        have hα := (differentialPullbackSheaf f g i.hom hi).mapPresheaf.naturality_apply
          ((OpenNhds.inclusion (genericPoint Y)).op.map j) s
        have hres := (differentialSheaf f).presheaf.germ_res_apply'
          ((Opens.map i.hom.base).map
            (((OpenNhds.inclusion (genericPoint Y)).op.map j).unop)).op
          (genericPoint X) (generic_mem_iso_preimage i V.unop.1 V.unop.2)
          ((differentialPullbackSheaf f g i.hom hi).app U.unop.1 s)
        exact (congrArg ((differentialSheaf f).presheaf.germ (i.hom ⁻¹ᵁ V.unop.1)
          (genericPoint X) (generic_mem_iso_preimage i V.unop.1 V.unop.2)) hα).trans hres }

/-- DEFINITION. The additive map on generic differential stalks is induced by
the actual sheaf pullback and the stalk colimit.
Locator: `genericDifferentialPullbackCocone`. -/
private def genericDifferentialPullbackAdd (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    (differentialSheaf g).presheaf.stalk (genericPoint Y) →+
      (differentialSheaf f).presheaf.stalk (genericPoint X) :=
  ConcreteCategory.hom (colimit.desc _ (genericDifferentialPullbackCocone f g i hi))

/-- THEOREM. The generic stalk pullback computes on an arbitrary section germ
by the actual sheaf pullback. Locator: `IsColimit.fac`. -/
private theorem genericDifferentialPullbackAdd_germ (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) (hi : i.hom ≫ g = f)
    (U : Y.Opens) (hp : genericPoint Y ∈ U) (s : Γ(differentialSheaf g, U)) :
    genericDifferentialPullbackAdd f g i hi
      ((differentialSheaf g).presheaf.germ U (genericPoint Y) hp s) =
      (differentialSheaf f).presheaf.germ (i.hom ⁻¹ᵁ U) (genericPoint X)
        (generic_mem_iso_preimage i U hp) ((differentialPullbackSheaf f g i.hom hi).app U s) := by
  have hc := (colimit.isColimit
    ((OpenNhds.inclusion (genericPoint Y)).op ⋙ (differentialSheaf g).presheaf)).fac
      (genericDifferentialPullbackCocone f g i hi) (op ⟨U, hp⟩)
  exact ConcreteCategory.congr_hom hc s

/-- DEFINITION. The generic differential stalk pullback is linear over the
source function field, acting on the target through the actual field isomorphism.
Locator: the germ scalar law and the pullback of rational functions. -/
def genericDifferentialPullback (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ))
    (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (curveFunctionFieldEquiv f g i).toRingHom
    (differentialSheaf g).presheaf.stalk (genericPoint Y) →ₗ[Y.functionField]
      (differentialSheaf f).presheaf.stalk (genericPoint X) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  let σ := curveFunctionFieldEquiv f g i
  letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
    Module.compHom _ σ.toRingHom
  refine localStalkLinearMapMk (genericPoint Y)
    ((differentialSheaf f).presheaf.stalk (genericPoint X))
      (genericDifferentialPullbackAdd f g i hi) ?_
  intro U hp a s
  rw [genericDifferentialPullbackAdd_germ, genericDifferentialPullbackAdd_germ,
    (differentialPullbackSheaf f g i.hom hi).app_smul]
  let t : Γ(differentialSheaf f, i.hom ⁻¹ᵁ U) :=
    (differentialPullbackSheaf f g i.hom hi).app U s
  change (differentialSheaf f).presheaf.germ (i.hom ⁻¹ᵁ U) (genericPoint X)
      (generic_mem_iso_preimage i U hp) (i.hom.app U a • t) =
    σ (Y.presheaf.germ U (genericPoint Y) hp a) •
      (differentialSheaf f).presheaf.germ (i.hom ⁻¹ᵁ U) (genericPoint X)
        (generic_mem_iso_preimage i U hp) t
  rw [moduleGerm_smul (differentialSheaf f)]
  exact congrArg (fun r : X.functionField => r •
    (differentialSheaf f).presheaf.germ (i.hom ⁻¹ᵁ U) (genericPoint X)
      (generic_mem_iso_preimage i U hp) t) (curveFunctionFieldEquiv_germ f g i U hp a).symm

/-- THEOREM. The linear generic stalk pullback has the sheaf germ computation.
Locator: `genericDifferentialPullbackAdd_germ`. -/
private theorem genericDifferentialPullback_germ (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) (hi : i.hom ≫ g = f)
    (U : Y.Opens) (hp : genericPoint Y ∈ U) (s : Γ(differentialSheaf g, U)) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (curveFunctionFieldEquiv f g i).toRingHom
    genericDifferentialPullback f g i hi
      ((differentialSheaf g).presheaf.germ U (genericPoint Y) hp s) =
      (differentialSheaf f).presheaf.germ (i.hom ⁻¹ᵁ U) (genericPoint X)
        (generic_mem_iso_preimage i U hp) ((differentialPullbackSheaf f g i.hom hi).app U s) :=
  genericDifferentialPullbackAdd_germ f g i hi U hp s

/-- THEOREM. The proved stalk Kähler identifications commute with actual curve
pullback. The proof checks the universal derivatives of local section germs;
it does not assume that global functions generate global differential sections.
Locator: the two universal derivations and `Derivation.liftKaehlerDifferential_unique`. -/
theorem genericDifferentialPullback_equiv (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (curveFunctionFieldEquiv f g i).toRingHom
    ∀ η : KaehlerDifferential ℚ Y.functionField,
      genericDifferentialPullback f g i hi (stalkKaehlerEquiv g (genericPoint Y) η) =
        stalkKaehlerEquiv f (genericPoint X)
          (kaehlerFieldTransport (curveFunctionFieldEquiv f g i) η) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  let σ := curveFunctionFieldEquiv f g i
  letI : Algebra Y.functionField X.functionField := σ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ Y.functionField X.functionField :=
    IsScalarTower.of_algebraMap_eq fun c => (σ.commutes c).symm
  let M := differentialSheaf f
  letI : Module ℚ (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (algebraMap ℚ X.functionField)
  letI : Module Y.functionField (M.presheaf.stalk (genericPoint X)) :=
    Module.compHom _ σ.toRingHom
  haveI : IsScalarTower Y.functionField X.functionField (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsScalarTower ℚ Y.functionField (M.presheaf.stalk (genericPoint X)) :=
    IsScalarTower.of_algebraMap_smul fun c ξ => by
      change σ (algebraMap ℚ Y.functionField c) • ξ = algebraMap ℚ X.functionField c • ξ
      rw [σ.commutes]
  let L := genericDifferentialPullback f g i hi ∘ₗ (stalkKaehlerEquiv g (genericPoint Y)).toLinearMap
  let R := ((stalkKaehlerEquiv f (genericPoint X)).restrictScalars Y.functionField).toLinearMap
    ∘ₗ KaehlerDifferential.map ℚ ℚ Y.functionField X.functionField
  have heq : L = R := by
    apply Derivation.liftKaehlerDifferential_unique
    ext z
    obtain ⟨U, hp, a, rfl⟩ := Y.presheaf.exists_germ_eq z
    change genericDifferentialPullback f g i hi
      (stalkKaehlerEquiv g (genericPoint Y)
        (D ℚ Y.functionField (Y.presheaf.germ U (genericPoint Y) hp a))) =
      stalkKaehlerEquiv f (genericPoint X)
        (KaehlerDifferential.map ℚ ℚ Y.functionField X.functionField
          (D ℚ Y.functionField (Y.presheaf.germ U (genericPoint Y) hp a)))
    rw [stalkKaehlerEquiv_D_germ, genericDifferentialPullback_germ,
      differentialPullbackSheaf_D, KaehlerDifferential.map_D]
    change M.presheaf.germ (i.hom ⁻¹ᵁ U) (genericPoint X)
        (generic_mem_iso_preimage i U hp) ((differentialDerivation f).d (i.hom.app U a)) =
      stalkKaehlerEquiv f (genericPoint X)
        (D ℚ X.functionField (σ (Y.presheaf.germ U (genericPoint Y) hp a)))
    rw [curveFunctionFieldEquiv_germ f g i U hp a]
    exact (stalkKaehlerEquiv_D_germ f (genericPoint X) (i.hom ⁻¹ᵁ U)
      (generic_mem_iso_preimage i U hp) (i.hom.app U a)).symm
  intro η
  change L η = R η
  exact LinearMap.congr_fun heq η

/-- THEOREM. Canonical rational restriction is restriction to the actual generic
stalk followed by its proved Kähler identification.
Locator: `canonicalRationalRestriction` and the inverse identity of `stalkKaehlerEquiv`. -/
theorem canonicalRationalRestriction_generic (f : X ⟶ Spec (.of ℚ)) :
    letI := functionFieldAlgebra f
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ s : Γ(differentialSheaf f, ⊤),
      stalkKaehlerEquiv f (genericPoint X) (canonicalRationalRestriction f s) =
        (differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial s := by
  letI := functionFieldAlgebra f
  letI := globalSectionsModule f (differentialSheaf f)
  intro s
  change stalkKaehlerEquiv f (genericPoint X)
      ((stalkKaehlerEquiv f (genericPoint X)).symm
        ((differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial s)) = _
  exact (stalkKaehlerEquiv f (genericPoint X)).apply_symm_apply _

/-- THEOREM. Actual global pullback and actual generic-stalk pullback agree on
the germ of every global differential section.
Locator: the two stalk colimit computations and restriction along `i⁻¹(⊤) = ⊤`. -/
theorem genericDifferentialPullback_global_germ (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
      Module.compHom _ (curveFunctionFieldEquiv f g i).toRingHom
    ∀ s : Γ(differentialSheaf g, ⊤),
      genericDifferentialPullback f g i hi
        ((differentialSheaf g).presheaf.germ ⊤ (genericPoint Y) trivial s) =
      (differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial
        (globalDifferentialPullback f g i.hom hi s) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (curveFunctionFieldEquiv f g i).toRingHom
  intro s
  rw [genericDifferentialPullback_germ]
  change (differentialSheaf f).presheaf.germ (i.hom ⁻¹ᵁ ⊤) (genericPoint X)
      (generic_mem_iso_preimage i ⊤ trivial) ((differentialPullbackSheaf f g i.hom hi).app ⊤ s) =
    (differentialSheaf f).presheaf.germ ⊤ (genericPoint X) trivial
      ((differentialSheaf f).presheaf.map (eqToHom (Opens.map_top i.hom.base).symm).op
        ((differentialPullbackSheaf f g i.hom hi).app ⊤ s))
  exact ((differentialSheaf f).presheaf.germ_res_apply
    (eqToHom (Opens.map_top i.hom.base).symm) (genericPoint X) trivial _).symm

/-- THEOREM. Actual global sheaf differential pullback commutes with rational
Kähler restriction along every curve isomorphism. The global pullback was defined
independently by the sheaf universal property.
Locator: `genericDifferentialPullback_equiv` and the generic-stalk restriction identities. -/
theorem canonicalRationalRestriction_pullback (f : X ⟶ Spec (.of ℚ))
    (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ s : Γ(differentialSheaf g, ⊤),
      canonicalRationalRestriction f (globalDifferentialPullback f g i.hom hi s) =
        kaehlerFieldTransport (curveFunctionFieldEquiv f g i) (canonicalRationalRestriction g s) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  letI : Module Y.functionField ((differentialSheaf f).presheaf.stalk (genericPoint X)) :=
    Module.compHom _ (curveFunctionFieldEquiv f g i).toRingHom
  intro s
  apply (stalkKaehlerEquiv f (genericPoint X)).injective
  rw [canonicalRationalRestriction_generic, ← genericDifferentialPullback_equiv,
    canonicalRationalRestriction_generic, genericDifferentialPullback_global_germ]

end GenericPullback

section CanonicalNaturality

open ZInQ.Contrib.RC53Assist.AbelianCurve

/-- THEOREM. The specified generic-restriction–cotrace comparison commutes with
the actual sheaf differential pullback along every isomorphism of rational curves.
The field transport is the actual cotrace of the induced field isomorphism; neither
side is defined by conjugating an arbitrary global linear equivalence. The separating
parameter is transported by the induced field isomorphism.
Locator: the sheaf universal derivation, `canonicalRationalRestriction_pullback`, and
cotrace transitivity, Stichtenoth Proposition III.4.11(b). -/
theorem canonicalWeilComparison_natural_iso {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (g : Y ⟶ Spec (.of ℚ)) [Smooth g] [IsProper g] [GeometricallyIntegral g]
    (hdX : topologicalKrullDim X = 1) (hdY : topologicalKrullDim Y = 1)
    (i : X ≅ Y) (hi : i.hom ≫ g = f) (x : Y.functionField)
    (hx : letI := functionFieldAlgebra g; Transcendental ℚ x) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    let σ := curveFunctionFieldEquiv f g i
    let hx' := hx.algHom σ σ.injective
    let hFY := isFunctionField_of_dimension_one g hdY
    let hFX := isFunctionField_of_dimension_one f hdX
    letI := hFY.finiteDimensional_adjoin hx
    letI := hFX.finiteDimensional_adjoin hx'
    letI := weilDifferentialSpaceModule hFY
    letI := weilDifferentialSpaceModule hFX
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ s : Γ(differentialSheaf g, ⊤),
      canonicalWeilComparison f hdX (σ x) hx' (globalDifferentialPullback f g i.hom hi s) =
        weilFieldTransport σ hFY hFX (canonicalWeilComparison g hdY x hx s) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  let σ := curveFunctionFieldEquiv f g i
  let hx' := hx.algHom σ σ.injective
  let hFY := isFunctionField_of_dimension_one g hdY
  let hFX := isFunctionField_of_dimension_one f hdX
  haveI := hFY.finiteDimensional_adjoin hx
  haveI := hFX.finiteDimensional_adjoin hx'
  letI := weilDifferentialSpaceModule hFY
  letI := weilDifferentialSpaceModule hFX
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  dsimp only
  intro s
  change comparison hFX (functionField_exact_constants f) hx'
      (canonicalRationalRestriction f (globalDifferentialPullback f g i.hom hi s)) =
    weilFieldTransport σ hFY hFX
      (comparison hFY (functionField_exact_constants g) hx (canonicalRationalRestriction g s))
  rw [canonicalRationalRestriction_pullback]
  exact (comparison_fieldTransport σ hFY hFX (functionField_exact_constants g)
    (functionField_exact_constants f) hx (canonicalRationalRestriction g s)).symm

/-- DEFINITION. A canonical regular-differential comparison consists of the
injectivity and exact image of the specified generic-restriction–cotrace map,
together with its naturality for actual isomorphisms of curves. These data preserve
differential forms, not only dimensions. The map and both transport maps are fixed
by their universal-derivation and trace-pairing constructions.
Locator: Silverman II, §§4–5; Stichtenoth III.4.11. -/
structure RegularDifferentialComparisonParameterized : Prop where
  /-- FIELD. Injectivity and exact zero-divisor image of the specified map.
  Locator: `RegularDifferentialComparisonImage`. -/
  image : RegularDifferentialComparisonImage
  /-- FIELD. Naturality for curve isomorphisms, with transported separating parameter.
  Locator: `canonicalWeilComparison_natural_iso`. -/
  naturality : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (g : Y ⟶ Spec (.of ℚ)) [Smooth g] [IsProper g] [GeometricallyIntegral g]
    (hdX : topologicalKrullDim X = 1) (hdY : topologicalKrullDim Y = 1)
    (i : X ≅ Y) (hi : i.hom ≫ g = f) (x : Y.functionField)
    (hx : letI := functionFieldAlgebra g; Transcendental ℚ x),
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    let σ := curveFunctionFieldEquiv f g i
    let hx' := hx.algHom σ σ.injective
    let hFY := isFunctionField_of_dimension_one g hdY
    let hFX := isFunctionField_of_dimension_one f hdX
    letI := hFY.finiteDimensional_adjoin hx
    letI := hFX.finiteDimensional_adjoin hx'
    letI := weilDifferentialSpaceModule hFY
    letI := weilDifferentialSpaceModule hFX
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ s : Γ(differentialSheaf g, ⊤),
      canonicalWeilComparison f hdX (σ x) hx' (globalDifferentialPullback f g i.hom hi s) =
        weilFieldTransport σ hFY hFX (canonicalWeilComparison g hdY x hx s)

/-- THEOREM (canonical reduction of S2a's regular comparison). The canonical
comparison, including actual isomorphism naturality, follows from only the two
precisely local uniformizer facts. Naturality itself is proved without either
local fact. No global comparison or genus assertion is assumed.
Locator: `canonicalWeilComparison_range`, `canonicalWeilComparison_injective`, and
`canonicalWeilComparison_natural_iso`. -/
theorem regularDifferentialComparisonParameterized_of_uniformizer_inputs
    (hB : LocalUniformizerBasis) (hO : UniformizerResidueOrder) :
    RegularDifferentialComparisonParameterized := by
  refine { image := regularDifferentialComparisonImage_of_uniformizer_inputs hB hO
           naturality := ?_ }
  intro X Y _ _ f _ _ _ g _ _ _ hdX hdY i hi x hx
  exact canonicalWeilComparison_natural_iso f g hdX hdY i hi x hx

/-- THEOREM. The canonical map-and-naturality form implies the previous
existence-of-linear-equivalence form. The implication discards information;
it is not used to manufacture the canonical map.
Locator: `RegularDifferentialComparisonImage.implies_dimension`. -/
theorem RegularDifferentialComparisonParameterized.implies_dimension
    (hC : RegularDifferentialComparisonParameterized) :
    ZInQ.Contrib.RC53Assist.AbelianCurve.RegularDifferentialComparison :=
  hC.image.implies_dimension

end CanonicalNaturality

section ParameterIndependence

open ZInQ.Contrib.RC53Assist.AbelianCurve

/-- DEFINITION OF A LOCAL FIELD STANDARD FACT. The normalized cotrace
separating differentials obey the rational differential chain rule when the
separating parameter is changed. This is a statement about rational differentials
of one function field only: no global sheaf sections, zero-divisor filtration,
genus, or curve model occur in it.
Locator: Silverman II, §4, the chain rule for rational differentials; Stichtenoth
I.5, Remark 1.5.12, for the repartition comparison. -/
def SeparatingCotraceChainRule : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (hF : IsFunctionField k F) (_hex : IsIntegrallyClosedIn k F) (x y : F)
    (hx : Transcendental k x) (hy : Transcendental k y),
    letI := hF.finiteDimensional_adjoin hx
    letI := hF.finiteDimensional_adjoin hy
    letI := weilDifferentialSpaceModule hF
    differentialOfSeparating hF hy = derivativeOfSeparating hx y • differentialOfSeparating hF hx

/-- THEOREM. The normalized comparison is independent of the separating
parameter under the precisely typed rational cotrace chain-rule fact.
Locator: the universal Kähler derivative basis and `SeparatingCotraceChainRule`;
no global regular-differential comparison is assumed. -/
theorem comparison_parameter_independent (hP : SeparatingCotraceChainRule)
    (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (x y : F)
    (hx : Transcendental k x) (hy : Transcendental k y) :
    letI := hF.finiteDimensional_adjoin hx
    letI := hF.finiteDimensional_adjoin hy
    letI := weilDifferentialSpaceModule hF
    comparison hF hex hx = comparison hF hex hy := by
  haveI := hF.finiteDimensional_adjoin hx
  haveI := hF.finiteDimensional_adjoin hy
  letI := weilDifferentialSpaceModule hF
  have hD : comparison hF hex hx (D k F y) = comparison hF hex hy (D k F y) := by
    calc
      comparison hF hex hx (D k F y) =
          derivativeOfSeparating hx y • differentialOfSeparating hF hx := by
            rw [← derivativeOfSeparating_smul_D hx y,
              (comparison hF hex hx).map_smul, comparison_D_self]
      _ = differentialOfSeparating hF hy := (hP k F hF hex x y hx hy).symm
      _ = comparison hF hex hy (D k F y) := (comparison_D_self hF hex hy).symm
  ext η
  let b := kaehlerBasisOfSeparating hy
  let a : F := b.repr η ()
  have hη : a • D k F y = η := by
    simpa only [a, b, Fintype.sum_unique, kaehlerBasisOfSeparating_apply] using b.sum_repr η
  rw [← hη, (comparison hF hex hx).map_smul, (comparison hF hex hy).map_smul, hD]

/-- DEFINITION. The intrinsic global comparison uses the actual generic
restriction and normalized cotrace, with a separating parameter chosen only to
execute the construction. Its agreement with every separating parameter is proved
under `SeparatingCotraceChainRule`, so the resulting map is choice-independent.
Locator: the generic restriction, the normalized rational differential, and the
rational differential chain rule. -/
def intrinsicWeilComparison {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    Γ(differentialSheaf f, ⊤) →ₗ[ℚ] ↥(weilDifferentialSpace ℚ X.functionField) := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  letI := weilDifferentialSpaceModule hF
  letI := globalSectionsModule f (differentialSheaf f)
  exact canonicalWeilComparison f hdim hF.exists_transcendental.choose
    hF.exists_transcendental.choose_spec

/-- THEOREM. The intrinsic map agrees with the specified generic-restriction–
cotrace map for every separating parameter, not merely for its chosen one.
Locator: `comparison_parameter_independent`. -/
theorem intrinsicWeilComparison_agrees (hP : SeparatingCotraceChainRule)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (hdim : topologicalKrullDim X = 1) (x : X.functionField)
    (hx : letI := functionFieldAlgebra f; Transcendental ℚ x) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    intrinsicWeilComparison f hdim = canonicalWeilComparison f hdim x hx := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  let x₀ := hF.exists_transcendental.choose
  have hx₀ : Transcendental ℚ x₀ := hF.exists_transcendental.choose_spec
  haveI := hF.finiteDimensional_adjoin hx₀
  haveI := hF.finiteDimensional_adjoin hx
  letI := weilDifferentialSpaceModule hF
  haveI := isScalarTower_weilDifferentialSpace hF
  letI := globalSectionsModule f (differentialSheaf f)
  have heq := comparison_parameter_independent hP ℚ X.functionField hF
    (functionField_exact_constants f) x₀ x hx₀ hx
  apply LinearMap.ext
  intro s
  change comparison hF (functionField_exact_constants f) hx₀ (canonicalRationalRestriction f s) =
    comparison hF (functionField_exact_constants f) hx (canonicalRationalRestriction f s)
  rw [heq]

/-- THEOREM. The intrinsic map is injective under the valuation-ring basis fact.
Locator: `canonicalWeilComparison_injective`, evaluated at the construction parameter. -/
theorem intrinsicWeilComparison_injective (hB : LocalUniformizerBasis)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f] (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    Function.Injective (intrinsicWeilComparison f hdim) := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  exact canonicalWeilComparison_injective hB f hdim hF.exists_transcendental.choose
    hF.exists_transcendental.choose_spec

/-- THEOREM. The image of the intrinsic comparison is exactly the regular
zero-divisor Weil subspace. Locator: `canonicalWeilComparison_range`. -/
theorem intrinsicWeilComparison_range (hB : LocalUniformizerBasis) (hO : UniformizerResidueOrder)
    {X : Scheme.{0}} [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f] (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    (intrinsicWeilComparison f hdim).range =
      holomorphicWeilSubmodule (k := ℚ) (F := X.functionField) := by
  letI := functionFieldAlgebra f
  let hF := isFunctionField_of_dimension_one f hdim
  exact canonicalWeilComparison_range hB hO f hdim hF.exists_transcendental.choose
    hF.exists_transcendental.choose_spec

/-- THEOREM. The intrinsic comparison is natural for isomorphisms of curves,
with no separating parameter in the statement. The actual sheaf differential
pullback and actual field cotrace are used on the two sides.
Locator: parameter independence and `canonicalWeilComparison_natural_iso`. -/
theorem intrinsicWeilComparison_natural_iso (hP : SeparatingCotraceChainRule)
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (g : Y ⟶ Spec (.of ℚ)) [Smooth g] [IsProper g] [GeometricallyIntegral g]
    (hdX : topologicalKrullDim X = 1) (hdY : topologicalKrullDim Y = 1)
    (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    let hFY := isFunctionField_of_dimension_one g hdY
    let hFX := isFunctionField_of_dimension_one f hdX
    letI := weilDifferentialSpaceModule hFY
    letI := weilDifferentialSpaceModule hFX
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ s : Γ(differentialSheaf g, ⊤),
      intrinsicWeilComparison f hdX (globalDifferentialPullback f g i.hom hi s) =
        weilFieldTransport (curveFunctionFieldEquiv f g i) hFY hFX (intrinsicWeilComparison g hdY s) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  let hFY := isFunctionField_of_dimension_one g hdY
  let hFX := isFunctionField_of_dimension_one f hdX
  letI := weilDifferentialSpaceModule hFY
  letI := weilDifferentialSpaceModule hFX
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  obtain ⟨x, hx⟩ := hFY.exists_transcendental
  let σ := curveFunctionFieldEquiv f g i
  have hx' : Transcendental ℚ (σ x) := hx.algHom σ σ.injective
  dsimp only
  intro s
  rw [intrinsicWeilComparison_agrees hP f hdX (σ x) hx',
    intrinsicWeilComparison_agrees hP g hdY x hx]
  exact canonicalWeilComparison_natural_iso f g hdX hdY i hi x hx s

end ParameterIndependence

section IntrinsicCanonicalComparison

open ZInQ.Contrib.RC53Assist.AbelianCurve

/-- DEFINITION. The canonical regular-differential comparison retains the
intrinsic map, its exact image, agreement with every normalized separating-parameter
construction, and parameter-free naturality for actual curve isomorphisms.
It is stronger than an equality of dimensions and does not choose a global generator.
Locator: Silverman II, §§4–5; the universal sheaf derivation and normalized cotrace. -/
structure RegularDifferentialComparisonCanonical : Prop where
  /-- FIELD. Injectivity and exact zero-divisor image of the intrinsic map.
  Locator: `intrinsicWeilComparison_injective` and `intrinsicWeilComparison_range`. -/
  image : ∀ (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f] (hdim : topologicalKrullDim X = 1),
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    Function.Injective (intrinsicWeilComparison f hdim) ∧
      (intrinsicWeilComparison f hdim).range =
        holomorphicWeilSubmodule (k := ℚ) (F := X.functionField)
  /-- FIELD. Agreement with every separating parameter proves choice independence.
  Locator: `intrinsicWeilComparison_agrees`. -/
  parameter_agreement : ∀ (X : Scheme.{0}) [IsIntegral X] (f : X ⟶ Spec (.of ℚ))
    [Smooth f] [IsProper f] [GeometricallyIntegral f] (hdim : topologicalKrullDim X = 1)
    (x : X.functionField) (hx : letI := functionFieldAlgebra f; Transcendental ℚ x),
    letI := functionFieldAlgebra f
    let hF := isFunctionField_of_dimension_one f hdim
    letI := weilDifferentialSpaceModule hF
    letI := globalSectionsModule f (differentialSheaf f)
    intrinsicWeilComparison f hdim = canonicalWeilComparison f hdim x hx
  /-- FIELD. Parameter-free naturality for isomorphisms of curves.
  Locator: `intrinsicWeilComparison_natural_iso`. -/
  naturality : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] [IsProper f] [GeometricallyIntegral f]
    (g : Y ⟶ Spec (.of ℚ)) [Smooth g] [IsProper g] [GeometricallyIntegral g]
    (hdX : topologicalKrullDim X = 1) (hdY : topologicalKrullDim Y = 1)
    (i : X ≅ Y) (hi : i.hom ≫ g = f),
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    let hFY := isFunctionField_of_dimension_one g hdY
    let hFX := isFunctionField_of_dimension_one f hdX
    letI := weilDifferentialSpaceModule hFY
    letI := weilDifferentialSpaceModule hFX
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ s : Γ(differentialSheaf g, ⊤),
      intrinsicWeilComparison f hdX (globalDifferentialPullback f g i.hom hi s) =
        weilFieldTransport (curveFunctionFieldEquiv f g i) hFY hFX (intrinsicWeilComparison g hdY s)

/-- THEOREM (canonical reduction of S2a). The canonical comparison follows from
three precisely typed rational/local field facts: a valuation-ring uniformizer basis,
order zero of the normalized uniformizer differential, and the normalized cotrace
chain rule under change of separating parameter. All sheaf, generic restriction,
gluing, curve-isomorphism pullback, and cotrace-isomorphism naturality steps are proved.
None of the inputs mentions global sections, a holomorphic dimension, or genus one.
Locator: Silverman II, §§4–5; the local and rational differential lemmas above. -/
theorem regularDifferentialComparisonCanonical_of_local_inputs
    (hB : LocalUniformizerBasis) (hO : UniformizerResidueOrder) (hP : SeparatingCotraceChainRule) :
    RegularDifferentialComparisonCanonical := by
  refine { image := ?_, parameter_agreement := ?_, naturality := ?_ }
  · intro X _ f _ _ _ hdim
    exact ⟨intrinsicWeilComparison_injective hB f hdim, intrinsicWeilComparison_range hB hO f hdim⟩
  · intro X _ f _ _ _ hdim x hx
    exact intrinsicWeilComparison_agrees hP f hdim x hx
  · intro X Y _ _ f _ _ _ g _ _ _ hdX hdY i hi
    exact intrinsicWeilComparison_natural_iso hP f g hdX hdY i hi

/-- THEOREM. The intrinsic canonical comparison implies the original
existence-of-linear-equivalence form by restricting its actual map to its image.
Locator: parameter agreement and `RegularDifferentialComparisonImage.implies_dimension`. -/
theorem RegularDifferentialComparisonCanonical.implies_dimension
    (hC : RegularDifferentialComparisonCanonical) :
    ZInQ.Contrib.RC53Assist.AbelianCurve.RegularDifferentialComparison := by
  have hImage : RegularDifferentialComparisonImage := by
    intro X _ f _ _ _ hdim x hx
    have h := hC.image X f hdim
    rw [hC.parameter_agreement X f hdim x hx] at h
    exact h
  exact hImage.implies_dimension

end IntrinsicCanonicalComparison

section PullbackIsomorphism

open ZInQ.Contrib.RC53Assist.AbelianCurve

/-- THEOREM. Kähler transport along a field isomorphism and its inverse cancel
on every rational differential. Locator: the separating derivative basis and
the actual transport identities `kaehlerFieldTransport_D` and `kaehlerFieldTransport_smul`. -/
theorem kaehlerFieldTransport_symm_apply {k F F' : Type} [Field k] [Field F] [Field F']
    [Algebra k F] [Algebra k F'] [CharZero k] (σ : F ≃ₐ[k] F')
    (hF : IsFunctionField k F) (η : KaehlerDifferential k F) :
    kaehlerFieldTransport σ.symm (kaehlerFieldTransport σ η) = η := by
  obtain ⟨x, hx⟩ := hF.exists_transcendental
  haveI := hF.finiteDimensional_adjoin hx
  let b := kaehlerBasisOfSeparating hx
  let a : F := b.repr η ()
  have hη : a • D k F x = η := by
    simpa only [a, b, Fintype.sum_unique, kaehlerBasisOfSeparating_apply] using b.sum_repr η
  rw [← hη, kaehlerFieldTransport_smul, kaehlerFieldTransport_D,
    kaehlerFieldTransport_smul, kaehlerFieldTransport_D,
    AlgEquiv.symm_apply_apply, AlgEquiv.symm_apply_apply]

/-- THEOREM. The field pullback of the inverse curve isomorphism is the inverse
of the field pullback. Locator: `curveFunctionFieldEquiv` and scheme field-map functoriality. -/
theorem curveFunctionFieldEquiv_symm {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) (g : Y ⟶ Spec (.of ℚ)) (i : X ≅ Y) :
    letI := functionFieldAlgebra f
    letI := functionFieldAlgebra g
    curveFunctionFieldEquiv g f i.symm = (curveFunctionFieldEquiv f g i).symm := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  apply AlgEquiv.ext
  intro z
  rfl

/-- DEFINITION (proved global pullback isomorphism). The actual sheaf differential
pullbacks of a curve isomorphism and its inverse induce inverse rational-linear
maps on global differential sections. No holomorphic dimension or chosen global
basis defines either map. This makes the naturality theorem a transport of actual
differential spaces along the curve isomorphism.
Locator: the proved Kähler restriction naturality and injectivity on smooth curves. -/
def globalDifferentialPullbackEquiv (hB : LocalUniformizerBasis)
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (g : Y ⟶ Spec (.of ℚ)) [Smooth g]
    (hdX : topologicalKrullDim X = 1) (hdY : topologicalKrullDim Y = 1)
    (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    Γ(differentialSheaf g, ⊤) ≃ₗ[ℚ] Γ(differentialSheaf f, ⊤) := by
  letI := functionFieldAlgebra f
  letI := functionFieldAlgebra g
  letI := globalSectionsModule g (differentialSheaf g)
  letI := globalSectionsModule f (differentialSheaf f)
  have hi' : i.inv ≫ f = g := by
    rw [← hi, ← Category.assoc, i.inv_hom_id, Category.id_comp]
  let P := globalDifferentialPullback f g i.hom hi
  let Q := globalDifferentialPullback g f i.inv hi'
  have hRf := rationalRestriction_injective f (canonicalDifferentialStalkData f)
    (stalkKaehlerMap_injective hB f hdX)
  have hRg := rationalRestriction_injective g (canonicalDifferentialStalkData g)
    (stalkKaehlerMap_injective hB g hdY)
  have hInv : ∀ s : Γ(differentialSheaf f, ⊤),
      canonicalRationalRestriction g (globalDifferentialPullback g f i.inv hi' s) =
        kaehlerFieldTransport (curveFunctionFieldEquiv f g i).symm (canonicalRationalRestriction f s) := by
    intro s
    have h := canonicalRationalRestriction_pullback g f i.symm hi' s
    change canonicalRationalRestriction g (globalDifferentialPullback g f i.inv hi' s) =
      kaehlerFieldTransport (curveFunctionFieldEquiv g f i.symm) (canonicalRationalRestriction f s) at h
    rw [curveFunctionFieldEquiv_symm] at h
    exact h
  refine { P with invFun := Q, left_inv := ?_, right_inv := ?_ }
  · intro s
    apply hRg
    change canonicalRationalRestriction g
      (globalDifferentialPullback g f i.inv hi' (globalDifferentialPullback f g i.hom hi s)) =
        canonicalRationalRestriction g s
    rw [hInv, canonicalRationalRestriction_pullback f g i hi]
    exact kaehlerFieldTransport_symm_apply (curveFunctionFieldEquiv f g i)
      (isFunctionField_of_dimension_one g hdY) (canonicalRationalRestriction g s)
  · intro s
    apply hRf
    change canonicalRationalRestriction f
      (globalDifferentialPullback f g i.hom hi (globalDifferentialPullback g f i.inv hi' s)) =
        canonicalRationalRestriction f s
    rw [canonicalRationalRestriction_pullback f g i hi, hInv]
    simpa only [AlgEquiv.symm_symm] using
      kaehlerFieldTransport_symm_apply (curveFunctionFieldEquiv f g i).symm
        (isFunctionField_of_dimension_one f hdX) (canonicalRationalRestriction f s)

/-- THEOREM. The global pullback isomorphism's forward map is the actual sheaf
pullback, not a vector-space equivalence chosen by dimension.
Locator: `globalDifferentialPullbackEquiv`. -/
theorem globalDifferentialPullbackEquiv_apply (hB : LocalUniformizerBasis)
    {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (g : Y ⟶ Spec (.of ℚ)) [Smooth g]
    (hdX : topologicalKrullDim X = 1) (hdY : topologicalKrullDim Y = 1)
    (i : X ≅ Y) (hi : i.hom ≫ g = f) :
    letI := globalSectionsModule g (differentialSheaf g)
    letI := globalSectionsModule f (differentialSheaf f)
    ∀ s : Γ(differentialSheaf g, ⊤),
      globalDifferentialPullbackEquiv hB f g hdX hdY i hi s =
        globalDifferentialPullback f g i.hom hi s := by
  intro s
  rfl

end PullbackIsomorphism

section NormalizationUniqueness

/-- THEOREM. A function-field-linear rational differential comparison is
uniquely determined by sending `dx` to the normalized cotrace differential.
This reconciles implementations through their mathematical normalization,
not through an equality of holomorphic dimensions.
Locator: `comparison_D_self` and the separating derivative basis. -/
theorem comparison_unique_of_D_self {k F : Type} [Field k] [Field F] [Algebra k F]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    ∀ φ : KaehlerDifferential k F →ₗ[F] ↥(weilDifferentialSpace k F),
      φ (D k F x) = differentialOfSeparating hF hx →
      φ = (comparison hF hex hx).toLinearMap := by
  letI := weilDifferentialSpaceModule hF
  intro φ hφ
  apply LinearMap.ext
  intro η
  let b := kaehlerBasisOfSeparating hx
  let a : F := b.repr η ()
  have hη : a • D k F x = η := by
    simpa only [a, b, Fintype.sum_unique, kaehlerBasisOfSeparating_apply] using b.sum_repr η
  rw [← hη, φ.map_smul, (comparison hF hex hx).toLinearMap.map_smul]
  change a • φ (D k F x) = a • comparison hF hex hx (D k F x)
  rw [hφ, comparison_D_self]

end NormalizationUniqueness

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs
