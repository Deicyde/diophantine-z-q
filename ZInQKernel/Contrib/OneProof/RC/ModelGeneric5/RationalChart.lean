import ZInQKernel.Contrib.OneProof.RC.ModelGeneric5.AtkinField
import ZInQKernel.Contrib.OneProof.RC.ModelGeneric5.IntegralTransfer
import ZInQKernel.Contrib.OneProof.RC.ModelNeron.Source

/-! The rational Atkin–Lehner involution preserves the pinned rational open.

The ring `Y0RationalAlgebra h₂` of the rational open is integrally closed with fraction
field `modularFunctionField N` (`ratToField`), and finite over `ℚ[j]`. The rational
pullback `AtkinRational.pullback hQ` sends `j` to `j_Q`, a root of the monic modular
polynomial `Φ_Q(X, j)`; so it maps the ring into its integral closure, which is the ring
itself (Atiyah–Macdonald 1969, Ch. 5, UNVERIFIED). This gives `atkinRat hQ`, an
endomorphism of `Y0RationalAlgebra h₂` with `ratToField ∘ atkinRat = pullback ∘ ratToField`.

`atkinRat_openImmersion`: `Spec(atkinRat) ≫ rationalOpenImmersion =
rationalOpenImmersion ≫ (rationalAtkin hQ).hom`. Both maps agree at the generic point
(the actual rational Atkin–Lehner map acts on the function field by `pullback hQ`,
`AtkinRational.exists_modelMap`), the source is reduced and the target separated.
Provenance: on the spot (c); the involution is the matrix `W_Q` of Atkin–Lehner, Math.
Ann. 185 (1970) (UNVERIFIED). -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false
set_option synthInstance.maxHeartbeats 100000

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ModularCurve Polynomial
open scoped TauCeti.ExactDivisor
open WeierstrassCurve.ModelLevels WeierstrassCurve.ModelLevels.ModelGeneric
  WeierstrassCurve.ModelLevels.ModelGeneric2
open ZInQ.Manuscript.RC.AtkinRational

namespace ZInQ.Manuscript.RC.ModelGeneric5

open private rationalAlgebra_isDomain rationalAlgebra_isIntegrallyClosed genericJ_isFractionRing
  from ZInQKernel.Contrib.OneProof.RC.ModelGeneric2.AffineComparison
open private section_fieldComparison from
  ZInQKernel.Contrib.OneProof.RC.ModelGeneric3.ChartCoordinates
open private finiteChart_affine chart_mem_finiteChart from
  ZInQKernel.Contrib.OneProof.RC.X0Model3.AffineEval

attribute [local instance] Algebra.TensorProduct.rightAlgebra
attribute [local instance] X0Model.jAlgebra X0Model.finite_jAlgebra

variable {N Q : ℕ} [NeZero N] (h₂ : 2 ≤ N)

/-- The function-field embedding of the pinned rational ring, through the actual field
comparison `genericModularFieldEquiv` used by `ModelNeron.chartField`. -/
def ratToField : Y0RationalAlgebra h₂ →+* modularFunctionField N :=
  (genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N))).toRingHom.comp
    (Y0RationalGenericJInclusion h₂)

theorem ratToField_injective : Function.Injective (ratToField h₂) :=
  (genericModularFieldEquiv h₂ _).injective.comp (Y0RationalGenericJInclusion_injective h₂)

theorem ratToField_J : ratToField h₂ (Y0RationalJ h₂) = ⟨jq, jq_mem N⟩ := by
  have h := ModelNeron.chart_sourceJ h₂
  simp only [ModelNeron.chartField, ModelNeron.sourceJ, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply] at h
  exact h

theorem ratToField_isFractionRing :
    letI := (ratToField h₂).toAlgebra
    IsFractionRing (Y0RationalAlgebra h₂) (modularFunctionField N) := by
  let B : Type := Y0RationalAlgebra h₂
  let E := Y0RationalGenericJ h₂
  let F := modularFunctionField N
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  letI : Field E := genericJField h₂
  letI : IsFractionRing B E := genericJ_isFractionRing h₂
  let e := genericModularFieldEquiv h₂ (Classical.choice (nonempty_modularPolynomialData N))
  letI : Algebra B F := (ratToField h₂).toAlgebra
  let e' : E ≃ₐ[B] F := AlgEquiv.ofRingEquiv (f := e.toRingEquiv) fun _ => rfl
  exact IsFractionRing.of_algEquiv e'

/-- `j_Q` is integral over the rational ring: a root of `Φ_Q(X, j)`, monic over `ℤ[j]`. -/
theorem isIntegral_jqN (hQ : Q ∥ N) :
    letI := (ratToField h₂).toAlgebra
    letI := neZero_of_exact hQ
    IsIntegral (Y0RationalAlgebra h₂)
      (⟨jqN Q, jqN_mem_of_dvd hQ.dvd⟩ : modularFunctionField N) := by
  letI := (ratToField h₂).toAlgebra
  letI := neZero_of_exact hQ
  let data := Classical.choice (nonempty_modularPolynomialData Q)
  let g := eval₂RingHom (Int.castRingHom (Y0RationalAlgebra h₂)) (Y0RationalJ h₂)
  refine ⟨data.Φ.map g, data.monic.map g, ?_⟩
  rw [eval₂_map]
  have hg : (algebraMap (Y0RationalAlgebra h₂) (modularFunctionField N)).comp g =
      eval₂RingHom (Int.castRingHom (modularFunctionField N)) ⟨jq, jq_mem N⟩ := by
    apply Polynomial.ringHom_ext
    · intro a
      exact RingHom.congr_fun (Subsingleton.elim
        (((algebraMap (Y0RationalAlgebra h₂) (modularFunctionField N)).comp g).comp C)
        ((eval₂RingHom (Int.castRingHom (modularFunctionField N)) ⟨jq, jq_mem N⟩).comp C)) a
    · change ratToField h₂ (g X) = _
      simp only [g, coe_eval₂RingHom, eval₂_X]
      exact ratToField_J h₂
  rw [hg]
  exact modularPolynomial_eval_field hQ.dvd data

/-- The pullback of every element of the rational ring is integral over it. -/
theorem isIntegral_pullback_ratToField (hQ : Q ∥ N) (a : Y0RationalAlgebra h₂) :
    letI := (ratToField h₂).toAlgebra
    IsIntegral (Y0RationalAlgebra h₂) (pullback hQ (ratToField h₂ a)) := by
  letI := (ratToField h₂).toAlgebra
  letI := neZero_of_exact hQ
  let A := Y0RationalAlgebra h₂
  letI := (Y0RationalJMap h₂).toRingHom.toAlgebra
  have hfin : (Y0RationalJMap h₂).toRingHom.Finite :=
    RingHom.finite_algebraMap.mpr (Y0RationalJMap_finite h₂)
  refine isIntegral_of_finite (A := A) (Y0RationalJMap h₂).toRingHom hfin
    ((pullback hQ).comp (ratToField h₂)) (fun f => ?_) a
  -- the composite on `ℚ[X]` is evaluation at `j_Q`
  let φ : Polynomial ℚ →+* modularFunctionField N :=
    ((pullback hQ).comp (ratToField h₂)).comp (Y0RationalJMap h₂).toRingHom
  change IsIntegral A (φ f)
  have hX : φ X = ⟨jqN Q, jqN_mem_of_dvd hQ.dvd⟩ := by
    change pullback hQ (ratToField h₂ (Y0RationalJMap h₂ X)) = _
    rw [show Y0RationalJMap h₂ X = Y0RationalJ h₂ from aeval_X _, ratToField_J]
    exact pullback_jq hQ
  have hC : ∀ c : ℚ, IsIntegral A (φ (C c)) := by
    intro c
    have : φ (C c) = algebraMap A (modularFunctionField N) (Y0RationalJMap h₂ (C c)) := by
      have h := RingHom.congr_fun (Subsingleton.elim (φ.comp C)
        ((algebraMap A (modularFunctionField N)).comp ((Y0RationalJMap h₂).toRingHom.comp C))) c
      exact h
    rw [this]
    exact isIntegral_algebraMap
  induction f using Polynomial.induction_on with
  | C c => exact hC c
  | add p q hp hq => rw [map_add]; exact hp.add hq
  | monomial n c _ =>
    rw [map_mul, map_pow, hX]
    exact (hC c).mul ((isIntegral_jqN h₂ hQ).pow _)

theorem exists_atkinRat (hQ : Q ∥ N) (a : Y0RationalAlgebra h₂) :
    ∃ b, ratToField h₂ b = pullback hQ (ratToField h₂ a) := by
  letI := (ratToField h₂).toAlgebra
  letI := rationalAlgebra_isDomain h₂
  letI := rationalAlgebra_isIntegrallyClosed h₂
  letI := ratToField_isFractionRing h₂
  exact IsIntegrallyClosed.isIntegral_iff.mp (isIntegral_pullback_ratToField h₂ hQ a)

/-- **The rational Atkin–Lehner map on the pinned rational ring**: the restriction of the
function-field pullback `AtkinRational.pullback hQ` (which `rationalAtkin hQ` induces on
the generic point). -/
def atkinRat (hQ : Q ∥ N) : Y0RationalAlgebra h₂ →+* Y0RationalAlgebra h₂ :=
  ((RingEquiv.ofBijective (ratToField h₂).rangeRestrict
      ⟨fun _ _ h => ratToField_injective h₂ (congrArg Subtype.val h),
        (ratToField h₂).rangeRestrict_surjective⟩).symm.toRingHom).comp
    (((pullback hQ).comp (ratToField h₂)).codRestrict (ratToField h₂).range
      fun a => (RingHom.mem_range).mpr (exists_atkinRat h₂ hQ a))

theorem ratToField_atkinRat (hQ : Q ∥ N) (a : Y0RationalAlgebra h₂) :
    ratToField h₂ (atkinRat h₂ hQ a) = pullback hQ (ratToField h₂ a) := by
  let e := RingEquiv.ofBijective (ratToField h₂).rangeRestrict
    ⟨fun _ _ h => ratToField_injective h₂ (congrArg Subtype.val h),
      (ratToField h₂).rangeRestrict_surjective⟩
  let y : (ratToField h₂).range := ⟨pullback hQ (ratToField h₂ a),
    (RingHom.mem_range).mpr (exists_atkinRat h₂ hQ a)⟩
  change ratToField h₂ (e.symm y) = y.val
  exact congrArg Subtype.val (e.apply_symm_apply y)

theorem atkinRat_J (hQ : Q ∥ N) :
    letI := neZero_of_exact hQ
    ratToField h₂ (atkinRat h₂ hQ (Y0RationalJ h₂)) = ⟨jqN Q, jqN_mem_of_dvd hQ.dvd⟩ := by
  rw [ratToField_atkinRat, ratToField_J]
  exact pullback_jq hQ

/-! ### The generic point of the rational open -/

private theorem sectionMap_factor {X : Scheme.{0}} {R : Type} [CommRing R]
    (p : Spec (.of R) ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hp : ⊤ ≤ p ⁻¹ᵁ U) :
    Spec.map (X0Model.sectionMap p U hp) ≫ hU.fromSpec = p := by
  change Spec.map (p.appLE U ⊤ hp ≫ (Scheme.ΓSpecIso (.of R)).hom) ≫ hU.fromSpec = p
  rw [Spec.map_comp, Category.assoc, IsAffineOpen.SpecMap_appLE_fromSpec p _
    (isAffineOpen_top _) hp, IsAffineOpen.fromSpec_top, ← Scheme.isoSpec_Spec_hom,
    Iso.hom_inv_id_assoc]

private theorem generic_hits_open (U : (X0Model.curve N).Opens)
    [Nonempty U] {K : Type} [Field K] (e : modularFunctionField N →+* K) :
    ⊤ ≤ (X0Model.genericMap N e) ⁻¹ᵁ U := by
  intro z _
  have hz : X0Model.genericMap N e z = genericPoint (X0Model.curve N) := by
    rw [Subsingleton.elim z (IsLocalRing.closedPoint K)]
    dsimp only [X0Model.genericMap]
    erw [Scheme.Hom.comp_apply, Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  change X0Model.genericMap N e z ∈ U
  rw [hz]
  exact ((genericPoint_spec (X0Model.curve N)).mem_open_set_iff U.isOpen).mpr
    (by rw [Set.univ_inter]; exact Set.nonempty_coe_sort.mp ‹Nonempty U›)

/-- The generic point of the pinned rational open, through `ratToField`, is the generic
point of the fixed curve. -/
theorem genericMap_eq_chart :
    Spec.map (CommRingCat.ofHom ((ratToField h₂).comp (rationalChartSections h₂).val.toRingHom)) ≫
      (finiteChart_affine N).fromSpec = X0Model.genericMap N (RingHom.id _) := by
  let U := X0Model3.finiteChart N
  letI : Nonempty U := ⟨⟨_, chart_mem_finiteChart N default⟩⟩
  have hu := generic_hits_open U (RingHom.id (modularFunctionField N))
  have hs : X0Model.sectionMap (X0Model.genericMap N (RingHom.id _)) U hu =
      CommRingCat.ofHom ((ratToField h₂).comp (rationalChartSections h₂).val.toRingHom) := by
    rw [X0Model.sectionMap_generic N (RingHom.id _) U hu]
    refine CommRingCat.hom_ext (RingHom.ext fun s => ?_)
    change X0Model.functionField N ((X0Model.curve N).germToFunctionField U s) =
      ratToField h₂ ((rationalChartSections h₂).val s)
    rw [section_fieldComparison h₂ s]
    rfl
  rw [← hs]
  exact sectionMap_factor (X0Model.genericMap N (RingHom.id _)) (finiteChart_affine N) hu

private theorem spec_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    Spec.map (CommRingCat.ofHom g) ≫ Spec.map (CommRingCat.ofHom f) =
      Spec.map (CommRingCat.ofHom (g.comp f)) := by
  rw [← Spec.map_comp]
  rfl

private theorem spec_to_rat_eq {R : Type} [CommRing R]
    (u v : Spec (.of R) ⟶ Spec (.of ℚ)) : u = v := by
  apply Spec.homEquiv.injective
  exact CommRingCat.hom_ext (Subsingleton.elim _ _)

/-- **The rational Atkin–Lehner involution restricts to the pinned rational open**, as the
actual morphism `Spec (atkinRat hQ)`. -/
theorem atkinRat_openImmersion (hQ : Q ∥ N) :
    Spec.map (CommRingCat.ofHom (atkinRat h₂ hQ)) ≫ rationalOpenImmersion h₂ =
      rationalOpenImmersion h₂ ≫ (rationalAtkin hQ).hom := by
  letI := rationalAlgebra_isDomain h₂
  haveI : IsProper (X0Model.overQ N) := X0Model.proper N
  haveI : IsDominant (Spec.map (CommRingCat.ofHom (ratToField h₂))) :=
    letI := ZInQ.Contrib.NeronC.isSchemeTheoreticallyDominant_spec_map
      (CommRingCat.ofHom (ratToField h₂)) (ratToField_injective h₂)
    inferInstance
  apply ext_of_isDominant_of_isSeparated (X0Model.overQ N) (spec_to_rat_eq _ _)
    (Spec.map (CommRingCat.ofHom (ratToField h₂)))
  let w := (rationalAtkin hQ).hom
  have hw : (X0Model.curve N).fromSpecFunctionField ≫ w =
      X0Model.genericMap N ((X0Model.functionField N).symm.toRingHom.comp (pullback hQ)) :=
    (exists_modelMap hQ).choose_spec.2
  let ρ := (rationalChartSections h₂).val.toRingHom
  have hgen := genericMap_eq_chart h₂
  unfold rationalOpenImmersion
  -- left side: the generic point moved by the pullback
  have hL : Spec.map (CommRingCat.ofHom (ratToField h₂)) ≫
      Spec.map (CommRingCat.ofHom (atkinRat h₂ hQ)) ≫ Spec.map (CommRingCat.ofHom ρ) ≫
        (finiteChart_affine N).fromSpec =
      Spec.map (CommRingCat.ofHom (pullback hQ)) ≫ X0Model.genericMap N (RingHom.id _) := by
    rw [← hgen, ← Category.assoc, ← Category.assoc, spec_comp, spec_comp, ← Category.assoc,
      spec_comp]
    congr 2
    exact congrArg CommRingCat.ofHom (RingHom.ext fun s => ratToField_atkinRat h₂ hQ (ρ s))
  have hR : Spec.map (CommRingCat.ofHom (ratToField h₂)) ≫ Spec.map (CommRingCat.ofHom ρ) ≫
        (finiteChart_affine N).fromSpec ≫ w =
      Spec.map (CommRingCat.ofHom (pullback hQ)) ≫ X0Model.genericMap N (RingHom.id _) := by
    rw [← Category.assoc, spec_comp, ← Category.assoc, hgen]
    unfold X0Model.genericMap
    rw [Category.assoc]
    change _ ≫ (X0Model.curve N).fromSpecFunctionField ≫ w = _
    rw [hw]
    unfold X0Model.genericMap
    rw [← Category.assoc, ← Category.assoc, spec_comp, spec_comp]
    congr 2
    refine congrArg CommRingCat.ofHom (RingHom.ext fun x => ?_)
    change X0Model.functionField N ((X0Model.functionField N).symm
      (pullback hQ (X0Model.functionField N x))) = pullback hQ (X0Model.functionField N x)
    rw [RingEquiv.apply_symm_apply]
  simp only [Category.assoc] at hL hR ⊢
  exact hL.trans hR.symm

#print axioms ratToField
#print axioms ratToField_J
#print axioms ratToField_isFractionRing
#print axioms isIntegral_jqN
#print axioms isIntegral_pullback_ratToField
#print axioms atkinRat
#print axioms ratToField_atkinRat
#print axioms atkinRat_J
#print axioms genericMap_eq_chart
#print axioms atkinRat_openImmersion

end ZInQ.Manuscript.RC.ModelGeneric5
