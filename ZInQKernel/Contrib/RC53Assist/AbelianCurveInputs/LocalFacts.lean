import ZInQKernel.Contrib.RC53Assist.AbelianCurveInputs.RegularComparison
import ZInQKernel.Contrib.RC53Assist.InvariantDifferential.DivisorZero
import ZInQKernel.Contrib.TauCeti.FieldTheory.FunctionField.Different.Tame
import Mathlib.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Localization.Integral

/-!
# Local Kähler differentials and normalized comparison

The local generation argument uses finite generation, a separable residue field,
and Nakayama's lemma. It does not assume a global differential comparison.
The normalized comparison is reconciled with the one used for the invariant
Weierstrass differential.

Locators: Silverman, Chapter II, §§4–5; Stichtenoth, §§I.5 and III.5.
The latter is an auxiliary reference for repartitions and the different.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts

open AlgebraicGeometry CategoryTheory Module Polynomial KaehlerDifferential IsLocalRing
open TauCeti
open ZInQ.Contrib.RC53Assist.AbelianCurveInputs
open scoped IntermediateField

/-- THEOREM. The reconstructed normalized comparison is definitionally equal to
that used for the invariant Weierstrass differential. The normalization, cotrace,
and singleton basis are the same constructions, not dimension-chosen maps.
Locator: `InvariantDifferential/DivisorZero.lean`, `comparison`, and
`AbelianCurveInputs/RegularComparison.lean`, `comparison`. -/
theorem comparison_eq_divisorZero {k F : Type*} [Field k] [Field F] [Algebra k F]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) {x : F}
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F] :
    letI := weilDifferentialSpaceModule hF
    ZInQ.Contrib.RC53Assist.AbelianCurveInputs.comparison hF hex hx =
      ZInQ.Contrib.RC53Assist.InvariantDifferential.comparison hF hex hx := by
  rfl

/-- THEOREM. In a local algebra with separable algebraic residue field and
finitely generated Kähler module, the differential of a generator of the maximal
ideal spans the Kähler module. The proof differentiates a residue minimal
polynomial and applies Nakayama's lemma.
Locator: the local parameter description in Silverman II, §4; Mathlib
`Derivation.map_aeval` and `Submodule.le_of_le_smul_of_le_jacobson_bot`. -/
theorem span_uniformizer_D_eq_top {k A : Type*} [Field k] [CommRing A] [IsLocalRing A]
    [Algebra k A] [Algebra.EssFiniteType k A]
    [Algebra.IsSeparable k (ResidueField A)]
    (t : A) (ht : maximalIdeal A = Ideal.span {t}) :
    Submodule.span A {D k A t} = ⊤ := by
  let N : Submodule A (KaehlerDifferential k A) := Submodule.span A {D k A t}
  have hgen : (⊤ : Submodule A (KaehlerDifferential k A)) ≤ N ⊔ maximalIdeal A • ⊤ := by
    conv_lhs => rw [← KaehlerDifferential.span_range_derivation k A]
    rw [Submodule.span_le]
    rintro _ ⟨r, rfl⟩
    let p : k[X] := minpoly k (residue A r)
    have hp : p.Separable := Algebra.IsSeparable.isSeparable k (residue A r)
    have hroot : aeval (residue A r) p = 0 := minpoly.aeval k (residue A r)
    have heval : ∀ q : k[X], residue A (aeval r q) = aeval (residue A r) q :=
      fun q => (aeval_algebraMap_apply (ResidueField A) r q).symm
    have hp0 : aeval r p ∈ maximalIdeal A := (residue_eq_zero_iff _).mp ((heval p).trans hroot)
    have hunit : IsUnit (aeval r p.derivative) := by
      by_contra h
      have hz : residue A (aeval r p.derivative) = 0 := (residue_eq_zero_iff _).mpr h
      exact hp.aeval_derivative_ne_zero hroot ((heval _).symm.trans hz)
    obtain ⟨a, ha⟩ : ∃ a : A, aeval r p = t * a := by
      rw [ht, Ideal.mem_span_singleton] at hp0
      obtain ⟨a, ha⟩ := hp0
      exact ⟨a, ha⟩
    have hD : aeval r p.derivative • D k A r = a • D k A t + t • D k A a := by
      rw [← (D k A).map_aeval p r, ha, (D k A).leibniz, add_comm]
    have hmem : aeval r p.derivative • D k A r ∈ N ⊔ maximalIdeal A • ⊤ := by
      rw [hD]
      exact add_mem
        (Submodule.mem_sup_left (N.smul_mem a (Submodule.mem_span_singleton_self _)))
        (Submodule.mem_sup_right (Submodule.smul_mem_smul
          (ht ▸ Ideal.mem_span_singleton_self t) (Submodule.mem_top : D k A a ∈ ⊤)))
    exact (Submodule.smul_mem_iff_of_isUnit _ hunit).mp hmem
  exact top_unique (Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top
    (maximalIdeal_le_jacobson _) hgen)

/-- THEOREM. A local uniformizer whose rational differential is nonzero is a
basis of the local Kähler module once its span is the whole module.
Locator: `span_uniformizer_D_eq_top`; injectivity follows in the function-field
Kähler line, not from an assumed local smoothness assertion. -/
theorem uniformizerBasis_of_span {k F : Type*} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (P : Place k F) (t : P.integers)
    (ht : P.valuation.IsUniformizer (t : F))
    (hspan : Submodule.span P.integers {D k P.integers t} = ⊤) :
    ∃ b : Basis Unit P.integers (KaehlerDifferential k P.integers),
      b () = D k P.integers t := by
  let L := LinearMap.toSpanSingleton P.integers (KaehlerDifferential k P.integers)
    (D k P.integers t)
  have hsurj : Function.Surjective L := by
    intro η
    obtain ⟨a, ha⟩ := (Submodule.span_singleton_eq_top_iff P.integers _).mp hspan η
    exact ⟨a, ha⟩
  have hinj : Function.Injective L := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    have h := congrArg (KaehlerDifferential.map k k P.integers F) ha
    change KaehlerDifferential.map k k P.integers F (a • D k P.integers t) =
      KaehlerDifferential.map k k P.integers F 0 at h
    rw [map_smul, KaehlerDifferential.map_D, map_zero] at h
    have h' : (a : F) • D k F (t : F) = 0 :=
      (algebraMap_smul F a (D k F (t : F))).trans h
    exact Subtype.ext ((smul_eq_zero.mp h').resolve_right (uniformizer_D_ne_zero hF P ht))
  let e : P.integers ≃ₗ[P.integers] KaehlerDifferential k P.integers :=
    LinearEquiv.ofBijective L ⟨hinj, hsurj⟩
  refine ⟨(Basis.singleton Unit P.integers).map e, ?_⟩
  simp only [Basis.map_apply, Basis.singleton_apply]
  change (1 : P.integers) • D k P.integers t = D k P.integers t
  exact one_smul _ _

/-- THEOREM. The valuation ring of a place of a characteristic-zero one-variable
function field is essentially of finite type over the constant field. It is a
localization of the finite normalization of `k[t]`, where `t` has positive order.
Locator: the affine-model/place correspondence in Stichtenoth III.2; Mathlib's
finiteness of integral closure in a finite separable field extension. -/
theorem placeIntegers_essFiniteType {k F : Type*} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (P : Place k F) :
    Algebra.EssFiniteType k P.integers := by
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have httr : Transcendental k t := uniformizer_transcendental P ht
  have htmem : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr
    (by rw [P.isUniformizer_iff_ord_eq_one.mp ht]; norm_num)
  letI : Algebra k[X] F := (aeval t).toRingHom.toAlgebra
  haveI : IsScalarTower k k[X] F :=
    IsScalarTower.of_algebraMap_eq fun c => ((aeval t).commutes c).symm
  letI := ratFuncAlgebraOfTranscendental httr
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental httr
  haveI := hF.finiteDimensional_adjoin httr
  haveI := isFunctionField_iff_functionField.mp hF
  haveI := isSeparable_ratFuncAlgebraOfTranscendental httr
  haveI : IsScalarTower k[X] (RatFunc k) F :=
    IsScalarTower.of_algebraMap_eq fun p => by
      rw [algebraMap_ratFuncAlgebraOfTranscendental_apply,
        RatFunc.algEquivOfTranscendental_algebraMap]
      simp only [IntermediateField.AdjoinSimple.coe_aeval_gen_apply]
      rfl
  let C := integralClosure k[X] F
  haveI : IsFractionRing C F :=
    IsIntegralClosure.isFractionRing_of_finite_extension k[X] (RatFunc k) F C
  haveI : IsDedekindDomain C :=
    IsIntegralClosure.isDedekindDomain k[X] (RatFunc k) F C
  haveI : Module.Finite k[X] C := IsIntegralClosure.finite (A := k[X]) (K := RatFunc k) (L := F) C
  letI : Algebra k C := ((algebraMap k[X] C).comp (algebraMap k k[X])).toAlgebra
  haveI : IsScalarTower k k[X] C := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k C F := IsScalarTower.of_algebraMap_eq fun c => by
    rw [IsScalarTower.algebraMap_apply k k[X] F c,
      IsScalarTower.algebraMap_apply k[X] C F]
    rfl
  have hpoly : ∀ p : k[X], algebraMap k[X] F p ∈ P.integers := by
    intro p
    let t₀ : P.integers := ⟨t, htmem⟩
    have heq : algebraMap k[X] F p = (aeval t₀ p : F) :=
      aeval_algebraMap_apply F t₀ p
    exact heq ▸ (aeval t₀ p).2
  have hC : ∀ b : C, algebraMap C F b ∈ P.integers := by
    intro b
    exact P.mem_integers_of_isIntegral hpoly b.2
  letI : Algebra C P.integers := ((algebraMap C F).codRestrict P.integers hC).toAlgebra
  haveI : IsScalarTower C P.integers F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower k C P.integers := IsScalarTower.of_algebraMap_eq fun c =>
    Subtype.ext ((P.coe_algebraMap_constants c).trans
      (IsScalarTower.algebraMap_apply k C F c))
  let q := P.center hC
  let V : ValuationSubring F := (q.valuation F).valuationSubring
  letI : Algebra C V := ((algebraMap C F).codRestrict V.toSubring
    (fun b => q.valuation_le_one b)).toAlgebra
  haveI : IsScalarTower C V F := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsLocalization.AtPrime V q.asIdeal := inferInstance
  have hV : V = P.integers := by
    dsimp only [V]
    rw [P.valuation_center hC, P.integers_def]
  let e : V ≃ₐ[C] P.integers :=
    { RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hV) with
      commutes' := fun b => Subtype.ext rfl }
  haveI : IsLocalization.AtPrime P.integers q.asIdeal :=
    IsLocalization.isLocalization_of_algEquiv q.asIdeal.primeCompl e
  haveI : Algebra.EssFiniteType C P.integers :=
    Algebra.EssFiniteType.of_isLocalization P.integers q.asIdeal.primeCompl
  haveI : Algebra.EssFiniteType k C := Algebra.EssFiniteType.comp k k[X] C
  exact Algebra.EssFiniteType.comp k C P.integers

/-- THEOREM. The local uniformizer-basis fact is proved for every
characteristic-zero one-variable function field. The generator spans by
Nakayama and is linearly independent after passage to rational differentials.
Locator: Silverman II, §4; `placeIntegers_essFiniteType`,
`span_uniformizer_D_eq_top`, and `uniformizerBasis_of_span`. -/
theorem localUniformizerBasis : LocalUniformizerBasis := by
  intro k F _ _ _ _ hF P
  haveI := placeIntegers_essFiniteType hF P
  haveI := P.finiteDimensional_residueField hF
  haveI : Algebra.IsSeparable k (ResidueField P.integers) := inferInstance
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible P.integers
  let e : P.integers ≃+* P.valuation.valuationSubring :=
    RingEquiv.subringCongr (congrArg ValuationSubring.toSubring P.integers_def)
  have hi : Irreducible (e π) := hπ.map e
  have hπuni : P.valuation.IsUniformizer (e π : F) :=
    Valuation.isUniformizer_of_maximalIdeal_eq_span P.valuation hi.maximalIdeal_eq
  have heπ : (e π : F) = (π : F) := RingEquiv.coe_subringCongr_apply _ π
  have hu : P.valuation.IsUniformizer (π : F) := heπ ▸ hπuni
  exact ⟨π, hu, uniformizerBasis_of_span hF P π hu
    (span_uniformizer_D_eq_top π hπ.maximalIdeal_eq)⟩

/-- THEOREM. Every uniformizer, not only the chosen one, generates the
maximal ideal of the actual place valuation ring.
Locator: the normalized order-one characterization of a uniformizer and
Stichtenoth I.1, the uniformizer factorization. -/
theorem uniformizer_maximalIdeal {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) (t : P.integers) (ht : P.valuation.IsUniformizer (t : F)) :
    maximalIdeal P.integers = Ideal.span {t} := by
  have hord : P.ord (t : F) = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
  have ht0 : (t : F) ≠ 0 := by
    intro h
    rw [h, P.ord_zero] at hord
    norm_num at hord
  apply le_antisymm
  · intro a ha
    by_cases ha0 : (a : F) = 0
    · have h : a = 0 := Subtype.ext ha0
      rw [h]
      exact Ideal.zero_mem _
    have haord : 0 < P.ord (a : F) := (P.mem_maximalIdeal_iff_ord_pos ha0).mp ha
    have hdiv : (a : F) / (t : F) ∈ P.integers := by
      rw [P.mem_integers_iff_ord_nonneg, div_eq_mul_inv,
        P.ord_mul ha0 (inv_ne_zero ht0), P.ord_inv, hord]
      omega
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨(a : F) / (t : F), hdiv⟩, Subtype.ext ?_⟩
    change (a : F) = (t : F) * ((a : F) / (t : F))
    field_simp
  · apply Ideal.span_le.mpr
    rintro a rfl
    exact (P.mem_maximalIdeal_iff_ord_pos ht0).mpr (by rw [hord]; norm_num)

/-- THEOREM. Every local uniformizer differential is a basis of the actual
local Kähler module in characteristic zero.
Locator: the proved finite-type local generation and rational independence. -/
theorem uniformizerBasis {k F : Type*} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (P : Place k F) (t : P.integers)
    (ht : P.valuation.IsUniformizer (t : F)) :
    ∃ b : Basis Unit P.integers (KaehlerDifferential k P.integers),
      b () = D k P.integers t := by
  haveI := placeIntegers_essFiniteType hF P
  haveI := P.finiteDimensional_residueField hF
  haveI : Algebra.IsSeparable k (ResidueField P.integers) := inferInstance
  exact uniformizerBasis_of_span hF P t ht
    (span_uniformizer_D_eq_top t (uniformizer_maximalIdeal P t ht))

/-- THEOREM. Differentiation with respect to a uniformizer preserves the actual
valuation ring. Its coefficient is read from the proved local Kähler basis.
Locator: Silverman II, §4, the local expression `a dt`; the Kähler localization map. -/
theorem uniformizer_derivative_integral {k F : Type*} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (P : Place k F) {t : F}
    (ht : P.valuation.IsUniformizer t) (a : P.integers) :
    let httr := uniformizer_transcendental P ht
    letI := hF.finiteDimensional_adjoin httr
    derivativeOfSeparating httr (a : F) ∈ P.integers := by
  let httr := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin httr
  have htmem : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr
    (by rw [P.isUniformizer_iff_ord_eq_one.mp ht]; norm_num)
  let t₀ : P.integers := ⟨t, htmem⟩
  obtain ⟨b, hb⟩ := uniformizerBasis hF P t₀ ht
  let c : P.integers := b.repr (D k P.integers a) ()
  have hlocal : c • D k P.integers t₀ = D k P.integers a := by
    simpa only [c, Fintype.sum_unique, hb] using b.sum_repr (D k P.integers a)
  have h := congrArg (KaehlerDifferential.map k k P.integers F) hlocal
  rw [map_smul, KaehlerDifferential.map_D, KaehlerDifferential.map_D] at h
  have hFcoef : (c : F) • D k F t = D k F (a : F) :=
    (algebraMap_smul F c (D k F t)).trans h
  have hc : (c : F) = derivativeOfSeparating httr (a : F) :=
    eq_derivativeOfSeparating httr (a : F) (c : F) hFcoef
  change derivativeOfSeparating httr (a : F) ∈ P.integers
  rw [← hc]
  exact c.2

/-- THEOREM. In characteristic zero, differentiating a function of positive
order with respect to a uniformizer reduces its order by exactly one.
The unit coefficient cannot cancel the leading positive integer coefficient.
Locator: the local parameter derivative calculation in Silverman II, §4. -/
theorem uniformizer_derivative_order_pos {k F : Type*} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (P : Place k F) {t : F}
    (ht : P.valuation.IsUniformizer t) {z : F} (hz : 0 < P.ord z) :
    let httr := uniformizer_transcendental P ht
    letI := hF.finiteDimensional_adjoin httr
    derivativeOfSeparating httr z ≠ 0 ∧
      P.ord (derivativeOfSeparating httr z) = P.ord z - 1 := by
  let httr := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin httr
  let d := derivativeOfSeparating httr
  have ht0 : t ≠ 0 := httr.ne_zero
  have hz0 : z ≠ 0 := by
    intro h
    rw [h, P.ord_zero] at hz
    omega
  have htord : P.ord t = 1 := P.isUniformizer_iff_ord_eq_one.mp ht
  have htmem : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr (by omega)
  let t₀ : P.integers := ⟨t, htmem⟩
  have htres : residue P.integers t₀ = 0 :=
    (P.residue_eq_zero_iff_ord_pos ht0).mpr (by change 0 < P.ord t; omega)
  obtain ⟨u, hu⟩ := P.exists_eq_zpow_mul_unit ht hz0
  let n : ℕ := (P.ord z).toNat
  have hncast : (n : ℤ) = P.ord z := Int.toNat_of_nonneg hz.le
  have hn : 0 < n := by omega
  have hzu : z = t ^ n * (u : F) := by
    rw [← hncast, zpow_natCast] at hu
    exact hu
  have hdu : d (u : F) ∈ P.integers := uniformizer_derivative_integral hF P ht (u : P.integers)
  let du : P.integers := ⟨d (u : F), hdu⟩
  let v : P.integers := (n : P.integers) * (u : P.integers) + t₀ * du
  haveI : CharZero (ResidueField P.integers) :=
    charZero_of_injective_algebraMap (algebraMap k (ResidueField P.integers)).injective
  have hresv : residue P.integers v = (n : ResidueField P.integers) *
      residue P.integers (u : P.integers) := by
    simp only [v, map_add, map_mul, map_natCast, htres, zero_mul, add_zero]
  have hresu : residue P.integers (u : P.integers) ≠ 0 :=
    ((Units.isUnit u).map (residue P.integers)).ne_zero
  have hvunit : IsUnit v := by
    by_contra h
    have hres0 : residue P.integers v = 0 := (residue_eq_zero_iff _).mpr h
    rw [hresv] at hres0
    exact mul_ne_zero (Nat.cast_ne_zero.mpr hn.ne') hresu hres0
  have hv0 : (v : F) ≠ 0 := by
    intro h
    exact hvunit.ne_zero (Subtype.ext h)
  have hvord : P.ord (v : F) = 0 := (P.isUnit_iff_ord_eq_zero hv0).mp hvunit
  have hdt : d t = 1 := derivativeOfSeparating_self httr
  have hpow : d (t ^ n) = (n : F) * t ^ (n - 1) := by
    have h := d.map_aeval (X ^ n : k[X]) t
    simpa only [map_pow, aeval_X, derivative_X_pow, map_mul, aeval_C, map_natCast,
      smul_eq_mul, hdt, mul_one] using h
  have htn : t ^ n = t ^ (n - 1) * t := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hder : d z = t ^ (n - 1) * (v : F) := by
    rw [hzu, d.leibniz, smul_eq_mul, smul_eq_mul, hpow, htn]
    change t ^ (n - 1) * t * d (u : F) +
      (u : F) * ((n : F) * t ^ (n - 1)) =
        t ^ (n - 1) * ((n : F) * (u : F) + t * d (u : F))
    ring
  refine ⟨by rw [hder]; exact mul_ne_zero (pow_ne_zero _ ht0) hv0, ?_⟩
  rw [hder, P.ord_mul (pow_ne_zero _ ht0) hv0, P.ord_pow, htord, hvord, add_zero, mul_one]
  omega

/-- THEOREM. A separable polynomial vanishing at a place has derivative a
unit there. This is a residue-field computation, with no global differential
comparison involved.
Locator: Silverman II, §4, separable local parameters; Mathlib
`Polynomial.Separable.aeval_derivative_ne_zero`. -/
theorem polynomial_derivative_order_zero {k F : Type*} [Field k] [Field F] [Algebra k F]
    (P : Place k F) (r : P.integers) (p : k[X]) (hp : p.Separable)
    (hord : 0 < P.ord (aeval (r : F) p)) :
    aeval (r : F) p.derivative ≠ 0 ∧ P.ord (aeval (r : F) p.derivative) = 0 := by
  have hval : ∀ q : k[X], (aeval r q : F) = aeval (r : F) q :=
    fun q => (aeval_algebraMap_apply F r q).symm
  have hne : (aeval r p : F) ≠ 0 := by
    intro h
    rw [← hval p, h, P.ord_zero] at hord
    omega
  have hroot : aeval (residue P.integers r) p = 0 := by
    have heq := aeval_algebraMap_apply (ResidueField P.integers) r p
    change aeval (residue P.integers r) p = residue P.integers (aeval r p) at heq
    exact heq.trans ((P.residue_eq_zero_iff_ord_pos hne).mpr
      (by rw [hval]; exact hord))
  have hu : IsUnit (aeval r p.derivative) := by
    by_contra h
    have hz : residue P.integers (aeval r p.derivative) = 0 := (residue_eq_zero_iff _).mpr h
    have heq := aeval_algebraMap_apply (ResidueField P.integers) r p.derivative
    exact hp.aeval_derivative_ne_zero hroot (heq.trans hz)
  have hn : (aeval r p.derivative : F) ≠ 0 := by
    intro h
    exact hu.ne_zero (Subtype.ext h)
  exact ⟨(hval _).symm ▸ hn, by
    rw [← hval]
    exact (P.isUnit_iff_ord_eq_zero hn).mp hu⟩

/-- THEOREM. The two rational coordinate derivatives attached to separating
parameters are reciprocal. This is the Kähler chain rule and does not assert
anything about a Weil comparison.
Locator: `Derivation.apply_eq_derivativeOfSeparating_smul` and the defining derivative basis. -/
theorem coordinate_derivative_reciprocal {k F : Type*} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) {x t : F}
    (hx : Transcendental k x) (ht : Transcendental k t) :
    letI := hF.finiteDimensional_adjoin hx
    letI := hF.finiteDimensional_adjoin ht
    derivativeOfSeparating hx t = (derivativeOfSeparating ht x)⁻¹ := by
  haveI := hF.finiteDimensional_adjoin hx
  haveI := hF.finiteDimensional_adjoin ht
  have h := (derivativeOfSeparating ht).apply_eq_derivativeOfSeparating_smul hx t
  rw [derivativeOfSeparating_self, smul_eq_mul] at h
  exact eq_inv_of_mul_eq_one_left h.symm

/-- THEOREM. The local order of normalized `dx` equals the order of its
coefficient with respect to a local uniformizer. The proof combines the tame
different exponent with the proved local Kähler derivative calculation.
Locator: Silverman II, §4; Stichtenoth Theorem III.5.1 and the cotrace divisor formula. -/
theorem separatingDifferential_order_uniformizer {k F : Type*} [Field k] [Field F]
    [Algebra k F] [CharZero k] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {x t : F} (hx : Transcendental k x) (P : Place k F) (ht : P.valuation.IsUniformizer t) :
    letI := hF.finiteDimensional_adjoin hx
    let httr := uniformizer_transcendental P ht
    letI := hF.finiteDimensional_adjoin httr
    weilDifferentialOrder hF hex
      (ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating hF hx).2
      (by simpa using ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating_ne_zero hF hx)
      P = P.ord (derivativeOfSeparating httr x) := by
  haveI := hF.finiteDimensional_adjoin hx
  let httr := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin httr
  let d := derivativeOfSeparating httr
  letI := ratFuncAlgebraOfTranscendental hx
  haveI := isScalarTower_ratFuncAlgebraOfTranscendental hx
  haveI := isFunctionField_iff_functionField.mp hF
  haveI := isSeparable_ratFuncAlgebraOfTranscendental hx
  let Q := P.restrict k (RatFunc k)
  let e : ℕ := Place.ramificationIdx (RatFunc k) P
  let de : ℕ := Place.differentExponent k (RatFunc k) P
  have he : e = de + 1 :=
    (Place.ramificationIdx_eq_differentExponent_add_one_iff k (RatFunc k) P).mpr
      (Place.isTame_of_charZero k (RatFunc k) P)
  have hxmap : algebraMap (RatFunc k) F RatFunc.X = x :=
    algebraMap_ratFuncAlgebraOfTranscendental_X hx
  have horder := congrArg (fun D₀ : Divisor k F => TauCeti.AlgebraicGeometry.WeilDivisor.coeff D₀ P)
    (ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating_divisor hF hex hx)
  simp only [TauCeti.AlgebraicGeometry.WeilDivisor.coeff_add,
    TauCeti.AlgebraicGeometry.WeilDivisor.coeff_zsmul, Divisor.coeff_poles,
    Units.val_mk0, Divisor.coeff_different] at horder
  change weilDifferentialOrder hF hex
      (ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating hF hx).2 _ P =
    (-2 : ℤ) * (-P.ord x ⊔ 0) + (de : ℤ) at horder
  have hdx0 : d x ≠ 0 := derivativeOfSeparating_ne_zero httr hx
  dsimp only
  change _ = P.ord (d x)
  by_cases hxp : 0 ≤ P.ord x
  · have hXi : RatFunc.X ∈ Q.integers := by
      rw [Place.mem_integers_restrict_iff, hxmap]
      exact P.mem_integers_iff_ord_nonneg.mpr hxp
    have hQnot : Q ≠ Place.infty k := by
      intro h
      exact (Place.X_notMem_integers_iff_eq_infty.mpr h) hXi
    obtain ⟨q, hq⟩ := (Q.eq_infty_or_exists_eq_ofPrime).resolve_left hQnot
    obtain ⟨p, ⟨hpm, hpi, hpq⟩, -⟩ := q.existsUnique_monic_irreducible_span
    let R₀ : RatFunc k := algebraMap k[X] (RatFunc k) p
    have hRunif : Q.valuation.IsUniformizer R₀ := by
      rw [hq]
      exact Place.isUniformizer_ofPrime_algebraMap k (RatFunc k) q hpq
    have hRord : Q.ord R₀ = 1 := Q.isUniformizer_iff_ord_eq_one.mp hRunif
    have hRp : algebraMap (RatFunc k) F R₀ = aeval x p := by
      rw [algebraMap_ratFuncAlgebraOfTranscendental_apply,
        RatFunc.algEquivOfTranscendental_algebraMap]
      exact IntermediateField.AdjoinSimple.coe_aeval_gen_apply k x p
    have hpord : P.ord (aeval x p) = e := by
      rw [← hRp, Place.ord_algebraMap_restrict k (RatFunc k) P]
      change (e : ℤ) * Q.ord R₀ = e
      rw [hRord, mul_one]
    have hepos : 0 < e := Place.ramificationIdx_pos (RatFunc k) P
    have hpordpos : 0 < P.ord (aeval x p) := by rw [hpord]; exact_mod_cast hepos
    let x₀ : P.integers := ⟨x, P.mem_integers_iff_ord_nonneg.mpr hxp⟩
    have hpsep : p.Separable := PerfectField.separable_of_irreducible hpi
    obtain ⟨hp'0, hp'ord⟩ := polynomial_derivative_order_zero P x₀ p hpsep hpordpos
    have hDp := uniformizer_derivative_order_pos hF P ht hpordpos
    change d (aeval x p) ≠ 0 ∧ P.ord (d (aeval x p)) = P.ord (aeval x p) - 1 at hDp
    have hchain : d (aeval x p) = aeval x p.derivative * d x := by
      simpa only [smul_eq_mul] using d.map_aeval p x
    have horddx : P.ord (d x) = (e : ℤ) - 1 := by
      rw [hpord, hchain, P.ord_mul hp'0 hdx0, hp'ord, zero_add] at hDp
      exact hDp.2
    rw [horder, horddx, sup_eq_right.mpr (by omega)]
    omega
  · have hxn : P.ord x < 0 := lt_of_not_ge hxp
    have hXnot : RatFunc.X ∉ Q.integers := by
      rw [Place.mem_integers_restrict_iff, hxmap, P.mem_integers_iff_ord_nonneg]
      exact hxp
    have hQ : Q = Place.infty k := Place.X_notMem_integers_iff_eq_infty.mp hXnot
    have hQinv : Q.ord (RatFunc.X⁻¹ : RatFunc k) = 1 := by
      rw [hQ]
      exact (Place.infty k).isUniformizer_iff_ord_eq_one.mp Place.isUniformizer_infty
    have hxe : -P.ord x = e := by
      have h := Place.ord_algebraMap_restrict k (RatFunc k) P (RatFunc.X⁻¹ : RatFunc k)
      rw [map_inv₀, hxmap, P.ord_inv] at h
      change -P.ord x = (e : ℤ) * Q.ord (RatFunc.X⁻¹ : RatFunc k) at h
      rwa [hQinv, mul_one] at h
    have hDinv := uniformizer_derivative_order_pos hF P ht (z := x⁻¹)
      (by rw [P.ord_inv]; omega)
    change d x⁻¹ ≠ 0 ∧ P.ord (d x⁻¹) = P.ord x⁻¹ - 1 at hDinv
    have hrelation : d x = -(x ^ 2) * d x⁻¹ := by
      have h := d.leibniz x x⁻¹
      rw [mul_inv_cancel₀ hx.ne_zero, d.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
      have h' := congrArg (fun z : F => x * z) h
      simp only [mul_zero, mul_add, ← mul_assoc, mul_inv_cancel₀ hx.ne_zero,
        one_mul, ← pow_two] at h'
      have hneg : d x = -(x ^ 2 * d x⁻¹) :=
        eq_neg_of_add_eq_zero_left (by simpa only [add_comm] using h'.symm)
      simpa only [neg_mul] using hneg
    have horddx : P.ord (d x) = P.ord x - 1 := by
      rw [hrelation, P.ord_mul (neg_ne_zero.mpr (pow_ne_zero _ hx.ne_zero)) hDinv.1,
        P.ord_neg, P.ord_pow, hDinv.2, P.ord_inv]
      ring
    rw [horder, horddx, sup_eq_left.mpr (by omega)]
    omega

/-- THEOREM. The normalized comparison image of a uniformizer differential has
order zero at that place for every separating parameter. This discharges the
local order fact without assuming the Weil parameter-change chain rule.
Locator: the cotrace divisor formula and `separatingDifferential_order_uniformizer`. -/
theorem uniformizerResidueOrder : UniformizerResidueOrder := by
  intro k F _ _ _ _ hF hex x hx _ P t ht
  letI := weilDifferentialSpaceModule hF
  let httr := uniformizer_transcendental P ht
  haveI := hF.finiteDimensional_adjoin httr
  have hcoeff0 : derivativeOfSeparating hx t ≠ 0 := derivativeOfSeparating_ne_zero hx httr
  have hsep0 : (ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating hF hx :
      Module.Dual k ↥(repartitionSpace k F)) ≠ 0 := by
    simpa using ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating_ne_zero hF hx
  have hformula : (comparison hF hex hx (D k F t) : Module.Dual k ↥(repartitionSpace k F)) =
      repartitionDualMul hF (derivativeOfSeparating hx t)
        (ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating hF hx) := by
    rw [comparison_eq_divisorZero,
      ZInQ.Contrib.RC53Assist.InvariantDifferential.comparison_D,
      coe_weilDifferentialSpaceModule_smul]
  rw [weilDifferentialOrder_eq_ord_add_of_eq_repartitionDualMul hF hex
    (comparison hF hex hx (D k F t)).2 (comparison_uniformizer_ne_zero hF hex hx P ht)
    (ZInQ.Contrib.RC53Assist.InvariantDifferential.differentialOfSeparating hF hx).2 hsep0
    hcoeff0 hformula P,
    separatingDifferential_order_uniformizer hF hex hx P ht,
    coordinate_derivative_reciprocal hF hx httr, P.ord_inv]
  omega

/-- THEOREM. The original regular differential comparison input is now proved
without any local comparison hypotheses. This removes input (2) from the S2a
reduction, independently of parameter independence of the intrinsic map.
Locator: Silverman II, §§4–5; the proved local basis and order theorems above. -/
theorem regularDifferentialComparison :
    ZInQ.Contrib.RC53Assist.AbelianCurve.RegularDifferentialComparison :=
  regularDifferentialComparison_of_uniformizer_inputs localUniformizerBasis uniformizerResidueOrder

/-- THEOREM. The normalized comparison family is injective, has exact image
Ω(0), and is natural for curve isomorphisms when the parameter is transported.
Neither local fact remains an input to this map-and-naturality theorem.
Locator: `RegularComparison.lean`, the actual generic and sheaf pullback constructions. -/
theorem regularDifferentialComparisonParameterized : RegularDifferentialComparisonParameterized :=
  regularDifferentialComparisonParameterized_of_uniformizer_inputs localUniformizerBasis uniformizerResidueOrder

/-- THEOREM. The holomorphic characterization of the invariant Weierstrass
Kähler differential uses exactly the reconstructed comparison, by the proved
cross-module equality. No genus or holomorphic-dimension assumption is supplied.
Locator: Silverman III.1.5;
`InvariantDifferential/DivisorZero.lean`, `comparison_mem_holomorphic_iff`. -/
theorem comparison_mem_holomorphic_iff {k : Type*} [Field k]
    (W : WeierstrassCurve.Affine k) [W.IsElliptic]
    (η : KaehlerDifferential k W.FunctionField) :
    letI := weilDifferentialSpaceModule W.isFunctionField
    (comparison W.isFunctionField
      (WeierstrassCurve.Affine.isIntegrallyClosedIn_functionField W)
      (WeierstrassCurve.Affine.transcendental_genericX W) η : Module.Dual k
        ↥(repartitionSpace k W.FunctionField)) ∈
      weilDifferentialFiltration (0 : Divisor k W.FunctionField) ↔
      ∃! c : k, c • WeierstrassCurve.Affine.invariantDifferential W = η := by
  letI := weilDifferentialSpaceModule W.isFunctionField
  rw [comparison_eq_divisorZero]
  exact ZInQ.Contrib.RC53Assist.InvariantDifferential.comparison_mem_holomorphic_iff W η

/-- THEOREM (S2a genus consequence). For the actual smooth proper integral
rational group curve, genus one now needs only the original invariant-sheaf
trivialization input. The global regular differential comparison is proved.
Locator: Milne IV.6.4(a)–(b) and IV.6.6; Silverman II, §§4–5. -/
theorem abelian_genus_one_of_trivialization
    (hT : ZInQ.Contrib.RC53Assist.AbelianCurve.InvariantDifferentialTrivialization)
    (G : Over (Spec (.of ℚ))) [CategoryTheory.GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] [IsProper G.hom] [GeometricallyIntegral G.hom]
    (hdim : topologicalKrullDim G.left = 1) :
    letI := ZInQ.Contrib.RC53Assist.AbelianCurve.functionFieldAlgebra G.hom
    TauCeti.genus ℚ G.left.functionField = 1 :=
  ZInQ.Contrib.RC53Assist.AbelianCurve.abelian_genus_one_of_differentials
    hT regularDifferentialComparison G hdim

/-- THEOREM. Two normalized separating-parameter comparisons differ by a
unique nonzero constant-field scalar. Their ratio has order zero at every place,
by the proved uniformizer order theorem, and hence is an exact constant.
This theorem does not assert that the scalar is one.
Locator: the one-dimensional rational differential line and the exact-constants
intersection-of-valuation-rings criterion, Stichtenoth I.1 and IV.3. -/
theorem comparisons_differ_by_constant {k F : Type} [Field k] [Field F] [Algebra k F]
    [CharZero k] (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F)
    {x y : F} (hx : Transcendental k x) (hy : Transcendental k y) :
    letI := hF.finiteDimensional_adjoin hx
    letI := hF.finiteDimensional_adjoin hy
    letI := weilDifferentialSpaceModule hF
    ∃! c : k, c ≠ 0 ∧ ∀ η : KaehlerDifferential k F,
      comparison hF hex hy η = c • comparison hF hex hx η := by
  haveI := hF.finiteDimensional_adjoin hx
  haveI := hF.finiteDimensional_adjoin hy
  letI := weilDifferentialSpaceModule hF
  haveI := isScalarTower_weilDifferentialSpace hF
  let φx := comparison hF hex hx
  let φy := comparison hF hex hy
  let b := kaehlerBasisOfSeparating hx
  let ξ := φx.symm (φy (D k F x))
  let a : F := b.repr ξ ()
  have hξ : a • D k F x = ξ := by
    simpa only [a, b, Fintype.sum_unique, kaehlerBasisOfSeparating_apply] using b.sum_repr ξ
  have hDx : φy (D k F x) = a • φx (D k F x) := by
    rw [← φx.apply_symm_apply (φy (D k F x))]
    change φx ξ = a • φx (D k F x)
    rw [← hξ, φx.map_smul]
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, zero_smul] at hDx
    exact D_ne_zero_of_separating hx (φy.map_eq_zero_iff.mp hDx)
  have hη : ∀ η : KaehlerDifferential k F, φy η = a • φx η := by
    intro η
    let q : F := b.repr η ()
    have hrep : q • D k F x = η := by
      simpa only [q, b, Fintype.sum_unique, kaehlerBasisOfSeparating_apply] using b.sum_repr η
    rw [← hrep, φy.map_smul, φx.map_smul, hDx, smul_smul, smul_smul, mul_comm q a]
  have hintegers : ∀ P : Place k F, a ∈ P.integers := by
    intro P
    obtain ⟨t, ht⟩ := P.exists_isUniformizer
    have httr := uniformizer_transcendental P ht
    haveI := hF.finiteDimensional_adjoin httr
    have htmem : t ∈ P.integers := P.mem_integers_iff_ord_nonneg.mpr
      (by rw [P.isUniformizer_iff_ord_eq_one.mp ht]; norm_num)
    let t₀ : P.integers := ⟨t, htmem⟩
    have hLcX := localComparison_of_uniformizer_facts localUniformizerBasis
      uniformizerResidueOrder k F hF hex x hx P
    have hLcY := localComparison_of_uniformizer_facts localUniformizerBasis
      uniformizerResidueOrder k F hF hex y hy P
    have hmapt : localKaehlerMap P (D k P.integers t₀) = D k F t :=
      KaehlerDifferential.map_D k k P.integers F t₀
    have hregY : RegularAt P (comparison hF hex hy (D k F t)) :=
      (hLcY.2 (D k F t)).mpr ⟨D k P.integers t₀, hmapt⟩
    have hregA : RegularAt P (comparison hF hex hx (a • D k F t)) := by
      rw [(comparison hF hex hx).map_smul]
      change RegularAt P (a • φx (D k F t))
      rw [← hη (D k F t)]
      exact hregY
    obtain ⟨ξ₀, hξ₀⟩ := (hLcX.2 (a • D k F t)).mp hregA
    obtain ⟨b₀, hb₀⟩ := uniformizerBasis hF P t₀ ht
    let c₀ : P.integers := b₀.repr ξ₀ ()
    have hrep : c₀ • D k P.integers t₀ = ξ₀ := by
      simpa only [c₀, Fintype.sum_unique, hb₀] using b₀.sum_repr ξ₀
    have hm := congrArg (KaehlerDifferential.map k k P.integers F) hrep
    rw [map_smul, KaehlerDifferential.map_D] at hm
    have hcoef : (c₀ : F) • D k F t = a • D k F t :=
      (algebraMap_smul F c₀ (D k F t)).trans (hm.trans hξ₀)
    have ha : (c₀ : F) = a :=
      smul_left_injective F (uniformizer_D_ne_zero hF P ht) hcoef
    exact ha ▸ c₀.2
  have halg : IsAlgebraic k a := _root_.mem_algebraicClosure_iff.mp
    ((Place.mem_algebraicClosure_iff_forall_mem_integers hF).mpr hintegers)
  letI := hex
  obtain ⟨c, hc⟩ := IsIntegrallyClosedIn.isIntegral_iff.mp halg.isIntegral
  have hc0 : c ≠ 0 := by
    intro h
    rw [h, map_zero] at hc
    exact ha0 hc.symm
  have hcη : ∀ η : KaehlerDifferential k F, φy η = c • φx η := by
    intro η
    rw [hη η, ← hc, algebraMap_smul F]
  refine ⟨c, ⟨hc0, hcη⟩, ?_⟩
  intro c' hc'
  have hnonzero : φx (D k F x) ≠ 0 := by
    exact fun h => D_ne_zero_of_separating hx (φx.map_eq_zero_iff.mp h)
  let ω : Module.Dual k ↥(repartitionSpace k F) := φx (D k F x)
  have hω : ω ≠ 0 := by
    intro h
    exact hnonzero (Subtype.ext h)
  have hscalar : c' • ω = c • ω := by
    have h := congrArg (fun z : ↥(weilDifferentialSpace k F) =>
      (z : Module.Dual k ↥(repartitionSpace k F)))
        ((hc'.2 (D k F x)).symm.trans (hcη (D k F x)))
    simpa only [Submodule.coe_smul, ω, φx] using h
  exact smul_left_injective k hω hscalar

/-- DEFINITION OF A LOCAL NUMERICAL NORMALIZATION. At a local uniformizer,
the residue functional of the normalized comparison applied to `dt/t` is
`[κ(P):k]`. This concerns one scalar evaluation, not an equality of rational
comparison maps or a global sheaf statement.
Locator: Stichtenoth IV.3.2(d), Remark IV.3.7(d), the trace residue of `dt/t`. -/
def LocalLogarithmicNormalization : Prop :=
  ∀ (k F : Type) [Field k] [Field F] [Algebra k F] [CharZero k]
    (hF : IsFunctionField k F) (hex : IsIntegrallyClosedIn k F) (x : F)
    (hx : Transcendental k x) [Algebra.IsSeparable k⟮x⟯ F]
    (P : Place k F) (t : F) (_ht : P.valuation.IsUniformizer t),
    letI := weilDifferentialSpaceModule hF
    repartitionDualComponent (comparison hF hex hx (D k F t) :
      Module.Dual k ↥(repartitionSpace k F)) P t⁻¹ = (P.degree : k)

/-- THEOREM. The remaining rational cotrace chain rule follows from the
single local logarithmic normalization. The comparisons already differ by
an exact constant, so one nonzero residue value forces that constant to one.
Locator: `comparisons_differ_by_constant` and the trace residue of `dt/t`. -/
theorem separatingCotraceChainRule_of_logarithmicNormalization
    (hN : LocalLogarithmicNormalization) : SeparatingCotraceChainRule := by
  intro k F _ _ _ _ hF hex x y hx hy
  haveI := hF.finiteDimensional_adjoin hx
  haveI := hF.finiteDimensional_adjoin hy
  letI := weilDifferentialSpaceModule hF
  haveI := isScalarTower_weilDifferentialSpace hF
  obtain ⟨c, ⟨hc0, hc⟩, -⟩ := comparisons_differ_by_constant hF hex hx hy
  obtain ⟨P⟩ := Place.nonempty hF
  obtain ⟨t, ht⟩ := P.exists_isUniformizer
  have h := congrArg (fun ω : ↥(weilDifferentialSpace k F) =>
    repartitionDualComponent (ω : Module.Dual k ↥(repartitionSpace k F)) P t⁻¹)
      (hc (D k F t))
  simp only [Submodule.coe_smul, repartitionDualComponent_apply,
    LinearMap.smul_apply, smul_eq_mul] at h
  have hNx := hN k F hF hex x hx P t ht
  have hNy := hN k F hF hex y hy P t ht
  simp only [repartitionDualComponent_apply] at hNx hNy
  rw [hNx, hNy] at h
  have hdeg : (P.degree : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_zero_of_lt (P.one_le_degree_of_isFunctionField hF))
  have hc1 : c = 1 := mul_right_cancel₀ hdeg (by simpa only [one_mul] using h.symm)
  have hDy := hc (D k F y)
  rw [hc1, one_smul, comparison_D_self] at hDy
  rw [← derivativeOfSeparating_smul_D hx y, map_smul, comparison_D_self] at hDy
  exact hDy

end ZInQ.Contrib.RC53Assist.AbelianCurveInputs.LocalFacts
