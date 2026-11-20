import ZInQKernel.Contrib.RC53Assist.AbelianCurve.IdentityPlace
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.Algebra.MvPolynomial.Equiv
import TauCeti.FieldTheory.FunctionField.Differential.Kaehler

/-!
# Smooth group curves and the place of the identity

All scheme-theoretic steps in this file are proved. A smooth integral scheme
of dimension one over the rationals is smooth of relative dimension one.
Every local ring is regular, every closed-point local ring is a discrete
valuation ring, and every local ring is a valuation ring. In particular the
identity of a one-dimensional smooth integral group scheme gives an actual
place of degree one in its function field.

The regularity and local-dimension arguments follow the proofs in
`ZInQKernel/Contrib/CloudW07JacobiansCurves/Jacobian/AlgebraicGeometry/Curve/LocalRing.lean`
and `Curve/Dimension.lean`, with individual Mathlib imports.
-/

set_option maxHeartbeats 800000
set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace ZInQ.Contrib.RC53Assist.AbelianCurve

open AlgebraicGeometry CategoryTheory Limits Order Topology IsLocalRing
open scoped TensorProduct

/-- THEOREM (proved). A flat local homomorphism taking the maximal ideal onto the maximal
ideal preserves regularity. Locator: the vendored Jacobian library,
`RingTheory/RegularLocalRing/Etale.lean`, `IsRegularLocalRing.of_flat_of_map_maximalIdeal_eq`. -/
private theorem regular_of_flat_local {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [IsRegularLocalRing R] [IsLocalRing S] [IsNoetherianRing S]
    [IsLocalHom (algebraMap R S)] [Module.Flat R S]
    (h : (maximalIdeal R).map (algebraMap R S) = maximalIdeal S) :
    IsRegularLocalRing S := by
  apply IsRegularLocalRing.of_spanFinrank_maximalIdeal_le
  haveI : (maximalIdeal S).LiesOver (maximalIdeal R) :=
    ⟨(maximalIdeal_comap (algebraMap R S)).symm⟩
  rw [← h, ← maximalIdeal_height_eq_ringKrullDim,
    Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (maximalIdeal R) (maximalIdeal S)]
  calc (((maximalIdeal R).map (algebraMap R S)).spanFinrank : WithBot ℕ∞)
      ≤ (maximalIdeal R).spanFinrank := by
        exact_mod_cast Ideal.spanFinrank_map_le_of_fg _ (IsNoetherian.noetherian _)
    _ = (maximalIdeal R).height := by
      rw [IsRegularLocalRing.spanFinrank_maximalIdeal, maximalIdeal_height_eq_ringKrullDim]
    _ ≤ _ := by exact_mod_cast le_self_add

/-- THEOREM (proved). Local rings of an étale algebra over a regular ring are regular.
Locator: the vendored Jacobian library, `RingTheory/RegularLocalRing/Etale.lean`,
`IsRegularLocalRing.localization_of_etale`. -/
private theorem regular_localization_etale {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.Etale R S] [IsRegularRing R] (q : Ideal S) [q.IsPrime] :
    IsRegularLocalRing (Localization.AtPrime q) := by
  let p := q.comap (algebraMap R S)
  haveI : q.LiesOver p := ⟨rfl⟩
  letI := Localization.AtPrime.algebraOfLiesOver p q
  haveI : Algebra.EssFiniteType (Localization.AtPrime p) (Localization.AtPrime q) :=
    .of_comp R _ _
  haveI : IsNoetherianRing (Localization.AtPrime q) :=
    Algebra.EssFiniteType.isNoetherianRing (Localization.AtPrime p) _
  haveI : IsLocalHom (algebraMap (Localization.AtPrime p) (Localization.AtPrime q)) :=
    Localization.isLocalHom_localRingHom _ _ _ _
  haveI : Module.Flat (Localization.AtPrime p) (Localization.AtPrime q) :=
    RingHom.Flat.localRingHom (f := algebraMap R S)
      (RingHom.flat_algebraMap_iff.mpr inferInstance) q p rfl
  apply regular_of_flat_local (R := Localization.AtPrime p)
  rw [← Localization.AtPrime.map_eq_maximalIdeal, Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  exact ((Algebra.isUnramifiedAt_iff_map_eq R p q).mp inferInstance).2

/-- THEOREM (proved). An affine étale polynomial chart has regular local rings.
Locator: the vendored Jacobian library, `AlgebraicGeometry/Curve/LocalRing.lean`,
`IsAffineOpen.isRegularLocalRing_stalk_of_etale`. -/
private theorem regular_stalk_of_etale_chart {X : Scheme.{0}} {R : Type} [CommRing R]
    [IsRegularRing R] {U : X.Opens} (hU : IsAffineOpen U)
    (φ : R →+* Γ(X, U)) (hφ : φ.Etale) (x : X) (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  algebraize [φ]
  letI := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  haveI := hU.isLocalization_stalk ⟨x, hx⟩
  haveI := regular_localization_etale (R := R) (hU.primeIdealOf ⟨x, hx⟩).asIdeal
  exact IsRegularLocalRing.of_ringEquiv
    (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
      (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal)
      (X.presheaf.stalk x)).toRingEquiv

/-- THEOREM (proved). Every local ring of a smooth scheme over the rationals is regular.
Locator: Mathlib, `Smooth.exists_isStandardSmooth` and
`RingHom.IsStandardSmooth.exists_etale_mvPolynomial`; the preceding étale-chart proof. -/
theorem smooth_stalk_regular {X : Scheme.{0}} (f : X ⟶ Spec (.of ℚ)) [Smooth f] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨V, _, U, hU, hxU, hUV, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain rfl : V = ⊤ := eq_top_iff.mpr fun y _ =>
    Subsingleton.elim (f x) y ▸ hUV hxU
  obtain ⟨n, φ, _, hφ⟩ := hstd.exists_etale_mvPolynomial
  let e : MvPolynomial (Fin n) ℚ ≃+* MvPolynomial (Fin n) Γ(Spec (.of ℚ), ⊤) :=
    MvPolynomial.mapEquiv _ (Scheme.ΓSpecIso (.of ℚ)).symm.commRingCatIsoToRingEquiv
  exact regular_stalk_of_etale_chart hU (φ.comp e.toRingHom)
    (RingHom.Etale.respectsIso.2 _ _ hφ) x hxU

/-- THEOREM (proved). The Kähler differentials of a one-variable rational function field have
function-field dimension one. This is not its holomorphic genus.
Locator: `TauCeti.finrank_kaehlerDifferential_eq_one_of_separating`. -/
theorem functionField_kaehler_rank_one {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [LocallyOfFiniteType f] (hdim : topologicalKrullDim X = 1) :
    letI := functionFieldAlgebra f
    Module.finrank X.functionField (KaehlerDifferential ℚ X.functionField) = 1 := by
  letI := functionFieldAlgebra f
  have hF := isFunctionField_of_dimension_one f hdim
  obtain ⟨t, ht⟩ := hF.exists_transcendental
  haveI := hF.finiteDimensional_adjoin ht
  exact TauCeti.finrank_kaehlerDifferential_eq_one_of_separating ht

/-- THEOREM (proved). A smooth integral one-dimensional scheme over the rationals is smooth
of relative dimension one, with the actual Mathlib chart definition.
Locator: Mathlib, `Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth`,
localization of Kähler differentials; `functionField_kaehler_rank_one` above. -/
theorem smooth_relativeDimension_one {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (hdim : topologicalKrullDim X = 1) :
    SmoothOfRelativeDimension 1 f := by
  letI := functionFieldAlgebra f
  refine ⟨fun x => ?_⟩
  obtain ⟨V, _, U, hU, hxU, hUV, hstd⟩ := Smooth.exists_isStandardSmooth f x
  obtain rfl : V = ⊤ := eq_top_iff.mpr fun y _ =>
    Subsingleton.elim (f x) y ▸ hUV hxU
  haveI : Nonempty U := ⟨⟨x, hxU⟩⟩
  letI := sectionsAlgebra f U
  haveI : Algebra.IsStandardSmooth ℚ Γ(X, U) := by
    have hbase : RingHom.IsStandardSmooth (Scheme.ΓSpecIso (.of ℚ)).inv.hom :=
      (RingHom.IsStandardSmoothOfRelativeDimension.equiv
        (Scheme.ΓSpecIso (.of ℚ)).symm.commRingCatIsoToRingEquiv).isStandardSmooth _
    exact hstd.comp hbase
  haveI := sections_functionField_tower f U
  haveI := functionField_isFractionRing_of_isAffineOpen X U hU
  have hn : Module.finrank Γ(X, U) (KaehlerDifferential ℚ Γ(X, U)) = 1 := by
    have hloc := Module.finrank_of_isLocalizedModule_of_free X.functionField
      (nonZeroDivisors Γ(X, U))
      (KaehlerDifferential.map ℚ ℚ Γ(X, U) X.functionField)
    exact hloc.symm.trans (functionField_kaehler_rank_one f hdim)
  have hrank : Module.rank Γ(X, U) (KaehlerDifferential ℚ Γ(X, U)) = 1 := by
    rw [← Module.finrank_eq_rank, hn]
    rfl
  have hrel : Algebra.IsStandardSmoothOfRelativeDimension 1 ℚ Γ(X, U) :=
    (Algebra.IsStandardSmoothOfRelativeDimension.iff_of_isStandardSmooth 1).mpr hrank
  have hrel' : RingHom.IsStandardSmoothOfRelativeDimension 1
      ((f.appLE ⊤ U hUV).hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom) := hrel
  have h₀ : RingHom.IsStandardSmoothOfRelativeDimension 0 (Scheme.ΓSpecIso (.of ℚ)).hom.hom :=
    RingHom.IsStandardSmoothOfRelativeDimension.equiv
      (Scheme.ΓSpecIso (.of ℚ)).commRingCatIsoToRingEquiv
  have hf := hrel'.comp h₀
  have hcomp : ((f.appLE ⊤ U hUV).hom.comp (Scheme.ΓSpecIso (.of ℚ)).inv.hom).comp
      (Scheme.ΓSpecIso (.of ℚ)).hom.hom = (f.appLE ⊤ U hUV).hom := by
    ext a
    simp
  rw [hcomp, add_zero] at hf
  exact ⟨⊤, isAffineOpen_top _, U, hU, hxU, hUV, hf⟩

/-- THEOREM (proved). Étale scheme morphisms are locally quasi-finite.
Locator: the vendored Jacobian library, `AlgebraicGeometry/Curve/Dimension.lean`,
`LocallyQuasiFinite.of_etale`. -/
private theorem locallyQuasiFinite_etale {X Y : Scheme.{0}} (f : X ⟶ Y) [Etale f] :
    LocallyQuasiFinite f := by
  rw [HasRingHomProperty.iff_appLE (P := @LocallyQuasiFinite)]
  intro U V e
  have h := HasRingHomProperty.appLE (P := @Etale) f inferInstance U V e
  algebraize [(f.appLE U V e).hom]
  exact RingHom.quasiFinite_algebraMap.mpr inferInstance

/-- THEOREM (proved). Flat locally quasi-finite morphisms preserve the codimension of points.
Locator: the vendored Jacobian library, `AlgebraicGeometry/Curve/Dimension.lean`,
`Scheme.Hom.coheight_apply_of_flat`. -/
private theorem coheight_flat_quasifinite {X Y : Scheme.{0}} (f : X ⟶ Y) [Flat f]
    [LocallyQuasiFinite f] (x : X) : coheight (f x) = coheight x := by
  have hstrict : StrictMono f := by
    intro a b hab
    rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab ⊢
    refine ⟨hab.1.map f.continuous, fun hba => hab.2 ?_⟩
    have hsame : f b = f a := (hba.antisymm (hab.1.map f.continuous)).eq.symm
    haveI : DiscreteTopology (f ⁻¹' {f a}) := (f.isDiscrete_preimage_singleton (f a)).to_subtype
    have hspec : (⟨b, hsame⟩ : f ⁻¹' {f a}) ⤳ ⟨a, rfl⟩ :=
      IsInducing.subtypeVal.specializes_iff.mp hab.1
    have heq : b = a := congrArg Subtype.val hspec.eq
    rw [heq]
  refine (coheight_eq_of_strictMono f hstrict (fun a b hab => ?_) x).symm
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes] at hab
  obtain ⟨a', ha', rfl⟩ := Flat.generalizingMap f hab.1
  refine ⟨a', ?_, rfl⟩
  rw [lt_iff_le_not_ge, Scheme.le_iff_specializes, Scheme.le_iff_specializes]
  exact ⟨ha', fun h => hab.2 (h.map f.continuous)⟩

/-- THEOREM (proved). Maximal ideals in a polynomial ring over a field have the expected
height. Locator: `ZInQKernel/Contrib/Dim/MvPolynomial.lean`,
`height_eq_natCard_of_isMaximal_mvPolynomial`. -/
private theorem maximal_polynomial_height (k : Type) [Field k] :
    ∀ (ι : Type) [Finite ι] (m : Ideal (MvPolynomial ι k)) [m.IsMaximal],
      m.height = Nat.card ι := by
  intro ι _
  induction ι using Finite.induction_empty_option with
  | of_equiv e ih =>
    intro m _
    let e' := (MvPolynomial.renameEquiv k e).toRingEquiv
    haveI : (m.map e'.symm).IsMaximal := Ideal.map_isMaximal_of_equiv e'.symm
    rw [← e'.symm.height_map m, ih, Nat.card_congr e]
  | h_empty =>
    intro m _
    have h := Ideal.height_le_ringKrullDim_of_ne_top (I := m) Ideal.IsPrime.ne_top'
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field] at h
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero, add_zero] at h
    simp only [Nat.card_of_isEmpty, CharP.cast_eq_zero]
    exact_mod_cast nonpos_iff_eq_zero.mp (by exact_mod_cast h)
  | @h_option α _ ih =>
    intro m _
    let e := (MvPolynomial.optionEquivLeft k α).toRingEquiv
    let p := m.map e
    haveI : p.IsMaximal := Ideal.map_isMaximal_of_equiv e
    let q := p.comap (Polynomial.C : MvPolynomial α k →+* _)
    haveI : q.IsMaximal := Polynomial.isMaximal_comap_C_of_isJacobsonRing p
    haveI : p.LiesOver q := ⟨rfl⟩
    rw [← e.height_map m, Polynomial.height_eq_height_add_one q p, ih q]
    simp [Nat.card_eq_fintype_card, Fintype.card_option]

/-- THEOREM (proved). Closed points of an étale polynomial chart have the expected codimension.
Locator: the vendored Jacobian library, `AlgebraicGeometry/Curve/Dimension.lean`,
`coheight_le_of_etale_mvPolynomial`, closed-point part. -/
private theorem coheight_closed_etale_polynomial {k : Type} [Field k] {R : CommRingCat.{0}}
    {n : ℕ} (φ : MvPolynomial (Fin n) k →+* R) (hφ : φ.Etale) (x : Spec R)
    (hx : IsClosed {x}) : coheight x = n := by
  let g := Spec.map (CommRingCat.ofHom φ)
  haveI : Etale g := HasRingHomProperty.Spec_iff.mpr hφ
  haveI : LocallyQuasiFinite g := locallyQuasiFinite_etale g
  rw [← coheight_flat_quasifinite g x, ← idealHeight_eq_coheight]
  haveI : (g x).asIdeal.IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp
      (g.closedPoints_subset_preimage_closedPoints hx)
  simpa using maximal_polynomial_height k (Fin n) (g x).asIdeal

/-- THEOREM (proved). The local ring at a closed point of a smooth relative curve has dimension
one. Locator: the vendored Jacobian library, `AlgebraicGeometry/Curve/Dimension.lean`,
`Scheme.ringKrullDim_stalk_eq_one_of_isClosed`. -/
theorem closed_stalk_dimension_one {X : Scheme.{0}} (f : X ⟶ Spec (.of ℚ))
    [SmoothOfRelativeDimension 1 f] {x : X} (hx : IsClosed {x}) :
    ringKrullDim (X.presheaf.stalk x) = 1 := by
  obtain ⟨V, _, U, hU, hxU, hUV, hstd⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension (n := 1) (f := f) x
  obtain rfl : V = ⊤ := eq_top_iff.mpr fun y _ =>
    Subsingleton.elim (f x) y ▸ hUV hxU
  obtain ⟨φ, _, hφ⟩ := hstd.exists_etale_mvPolynomial
  let e : MvPolynomial (Fin 1) ℚ ≃+* MvPolynomial (Fin 1) Γ(Spec (.of ℚ), ⊤) :=
    MvPolynomial.mapEquiv _ (Scheme.ΓSpecIso (.of ℚ)).symm.commRingCatIsoToRingEquiv
  let φ' := φ.comp e.toRingHom
  have hφ' : φ'.Etale := RingHom.Etale.respectsIso.2 _ _ hφ
  let y := hU.primeIdealOf ⟨x, hxU⟩
  have hy : hU.fromSpec y = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hyc : IsClosed ({y} : Set (Spec Γ(X, U))) := by
    have heq : hU.fromSpec ⁻¹' {x} = {y} := by
      ext z
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => hU.fromSpec.isOpenEmbedding.injective (h.trans hy.symm),
        fun h => h ▸ hy⟩
    rw [← heq]
    exact hx.preimage hU.fromSpec.continuous
  rw [ringKrullDim_stalk_eq_coheight, ← hy, coheight_eq_of_isOpenImmersion]
  exact_mod_cast coheight_closed_etale_polynomial φ' hφ' y hyc

/-- THEOREM (proved). A closed-point local ring on a smooth integral rational curve is a DVR.
Locator: Mathlib, `IsLocalRing.finrank_CotangentSpace_eq_one_iff`;
`smooth_stalk_regular` and `closed_stalk_dimension_one` above. -/
theorem closed_stalk_discreteValuationRing {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (hdim : topologicalKrullDim X = 1)
    {x : X} (hx : IsClosed {x}) : IsDiscreteValuationRing (X.presheaf.stalk x) := by
  haveI := smooth_relativeDimension_one f hdim
  haveI := smooth_stalk_regular f x
  apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
  have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := X.presheaf.stalk x)).mp
    (inferInstance : IsRegularLocalRing (X.presheaf.stalk x))
  rw [closed_stalk_dimension_one f hx] at h
  exact_mod_cast h

/-- THEOREM (proved). Every local ring of a smooth integral rational curve is a valuation ring.
Locator: the vendored Jacobian library, `AlgebraicGeometry/Curve/Dimension.lean`,
`Scheme.valuationRing_stalk`; the generic local ring is a field. -/
theorem smooth_curve_valuation_stalk {X : Scheme.{0}} [IsIntegral X]
    (f : X ⟶ Spec (.of ℚ)) [Smooth f] (hdim : topologicalKrullDim X = 1) (x : X) :
    ValuationRing (X.presheaf.stalk x) := by
  haveI := smooth_stalk_regular f x
  have hle : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
    rw [ringKrullDim_stalk_eq_coheight]
    have h := Order.coheight_le_krullDim x
    have heq : topologicalKrullDim X = Order.krullDim X :=
      Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := X))
    rw [← heq, hdim] at h
    exact_mod_cast h
  by_cases h₁ : ringKrullDim (X.presheaf.stalk x) = 1
  · haveI : IsDiscreteValuationRing (X.presheaf.stalk x) := by
      apply IsLocalRing.finrank_CotangentSpace_eq_one_iff.mp
      have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := X.presheaf.stalk x)).mp
        (inferInstance : IsRegularLocalRing (X.presheaf.stalk x))
      rw [h₁] at h
      exact_mod_cast h
    infer_instance
  · have h₀ : ringKrullDim (X.presheaf.stalk x) ≤ 0 :=
      ENat.WithBot.lt_add_one_iff.mp (lt_of_le_of_ne hle h₁)
    haveI : Ring.KrullDimLE 0 (X.presheaf.stalk x) := ⟨by exact_mod_cast h₀⟩
    letI := (Ring.KrullDimLE.isField_of_isDomain (R := X.presheaf.stalk x)).toField
    infer_instance

/-- THEOREM (proved). The identity local ring of a smooth one-dimensional integral group
scheme is a DVR. Locator: `identityPoint_closed` and `closed_stalk_discreteValuationRing`. -/
theorem identity_stalk_discreteValuationRing (G : Over (Spec (.of ℚ))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1) :
    IsDiscreteValuationRing (G.left.presheaf.stalk (identityPoint G)) :=
  closed_stalk_discreteValuationRing G.hom hdim (identityPoint_closed G)

/-- DEFINITION. The place of the identity of a smooth integral group curve, with its local
DVR condition proved rather than assumed. Locator: `identityPlace` and
`identity_stalk_discreteValuationRing`. -/
def smoothIdentityPlace (G : Over (Spec (.of ℚ))) [GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.Place ℚ G.left.functionField := by
  haveI := identity_stalk_discreteValuationRing G hdim
  exact identityPlace G

/-- THEOREM (proved, S2a part 3). The identity of the actual group scheme gives a place of
degree one. Locator: `identityPlace_degree`; the local DVR condition is proved above. -/
theorem smoothIdentityPlace_degree (G : Over (Spec (.of ℚ))) [GrpObj G] [IsIntegral G.left]
    [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1) :
    letI := functionFieldAlgebra G.hom
    (smoothIdentityPlace G hdim).degree = 1 := by
  haveI := identity_stalk_discreteValuationRing G hdim
  exact identityPlace_degree G

/-- THEOREM (proved). The degree-one divisor of the identity is the last condition in the
elliptic-function-field predicate once the genus is one. Locator:
`TauCeti.IsEllipticFunctionField`; `TauCeti.Divisor.degree_ofPoint`.
This is a conditional dictionary theorem, not a printed genus assertion. -/
theorem ellipticFunctionField_of_genus_one (G : Over (Spec (.of ℚ))) [GrpObj G]
    [IsIntegral G.left] [Smooth G.hom] (hdim : topologicalKrullDim G.left = 1)
    (hg : letI := functionFieldAlgebra G.hom
      TauCeti.genus ℚ G.left.functionField = 1) :
    letI := functionFieldAlgebra G.hom
    TauCeti.IsEllipticFunctionField ℚ G.left.functionField := by
  letI := functionFieldAlgebra G.hom
  refine ⟨hg, TauCeti.AlgebraicGeometry.WeilDivisor.ofPoint (smoothIdentityPlace G hdim), ?_⟩
  rw [TauCeti.Divisor.degree_ofPoint, smoothIdentityPlace_degree G hdim]
  norm_num

end ZInQ.Contrib.RC53Assist.AbelianCurve
