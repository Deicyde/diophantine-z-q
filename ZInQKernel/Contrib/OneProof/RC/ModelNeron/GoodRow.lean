import ZInQKernel.Contrib.OneProof.RC.ModelNeron.Source
import ZInQKernel.Contrib.OneProof.RC.PMWire.Model

/-! Supply the pinned generic source and the Néron extension for tex 8476–8479.
Identification of the chosen comparison on this compact model is on the spot (c). -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open WeierstrassCurve.ModelTorsion WeierstrassCurve.ModelLevels
  WeierstrassCurve.ModelLevels.ModelGeneric2
open ZInQ.Contrib.RC53Assist.AbelianCurve

namespace ZInQ.Manuscript.RC.ModelNeron

open PMWire (GenericSource rationalSource ellipticTarget)
open GoodReduction (generic)

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {ell N : ℕ} [Fact ell.Prime] [NeZero N]
  (h₅ : 5 ≤ ell) (htame : ¬ ell ∣ N * N.totient) (h₂ : 2 ≤ N)

/-- The generic source of `GoodRow` on the pinned integral model. -/
def source : GenericSource ((generic (LocalIntegers ell) ℚ).obj
    (Pinned.Y0Level h₅ htame h₂)) N where
  compact := rationalSource N
  incl := incl h₅ htame h₂
  openIncl := openIncl h₅ htame h₂
  denseIncl := denseIncl h₅ htame h₂
  integral := (X0Branch.model N).integral
  proper := (X0Branch.model N).proper
  smooth := (X0Branch.model N).smooth
  dimension := ParamAtScale.model_dimension (X0Branch.model N)
  sourceJ := sourceJ h₂
  quotientJ := quotientJ h₂
  chartField := chartField h₂
  chart_sourceJ := chart_sourceJ h₂
  chart_quotientJ := chart_quotientJ h₂

/-- The compact comparison is the identity since it has the identity pullback. -/
theorem compactIso_hom : (source h₅ htame h₂).compactIso.hom = 𝟙 (rationalSource N) := by
  let D := source h₅ htame h₂
  let X := rationalSource N
  letI : IsIntegral X.left := (X0Branch.model N).integral
  letI : IsProper X.hom := (X0Branch.model N).proper
  have hfield : D.pullbackField = RingEquiv.refl X.left.functionField := by
    change (X0Model.functionField N).trans (chartField h₂).symm = _
    rw [chartField_eq]
    exact RingEquiv.self_trans_symm (X0Model.functionField N)
  apply Over.OverMorphism.ext
  change D.compactIso.hom.left = 𝟙 X.left
  apply eq_of_generic_agreement X.hom X.hom _ _ (Over.w D.compactIso.hom) (Category.id_comp _)
  have he := D.compactIso_generic
  rw [hfield] at he
  change fromFunctionField X.left ≫ D.compactIso.hom.left =
    Spec.map (𝟙 (CommRingCat.of X.left.functionField)) ≫ fromFunctionField X.left at he
  exact he.trans ((congrArg (fun f => f ≫ fromFunctionField X.left)
    (AlgebraicGeometry.Spec.map_id (CommRingCat.of X.left.functionField))).trans
      ((Category.id_comp _).trans (Category.comp_id _).symm))

/-- The `jX` derived by the consumer is exactly the actual pinned open immersion. -/
theorem jX_eq_incl : (source h₅ htame h₂).jX = incl h₅ htame h₂ := by
  change incl h₅ htame h₂ ≫ (source h₅ htame h₂).compactIso.hom = _
  rw [compactIso_hom, Category.comp_id]

variable {E₀ : WeierstrassCurve ℚ}
  (π : rationalSource N ⟶ ellipticTarget E₀)
  {E : Over (Spec (.of (LocalIntegers ell)))}
  (neron : CToPrinted.IsNeronModelOver (LocalIntegers ell) ℚ E)
  (jE : (generic (LocalIntegers ell) ℚ).obj E ≅ ellipticTarget E₀)

/-- The Néron lift of `jX ≫ (π ≫ jE.inv)`, with the same defining choice as `GoodRow.πInt`. -/
def πInt : Pinned.Y0Level h₅ htame h₂ ⟶ E :=
  letI := Pinned.Y0Level_smooth h₅ htame h₂
  ((neron.2.2.2.2 (Pinned.Y0Level h₅ htame h₂)).surjective
    ((source h₅ htame h₂).jX ≫ (π ≫ jE.inv))).choose

theorem hInt : (generic (LocalIntegers ell) ℚ).map (πInt h₅ htame h₂ π neron jE) =
    (source h₅ htame h₂).jX ≫ (π ≫ jE.inv) :=
  letI := Pinned.Y0Level_smooth h₅ htame h₂
  ((neron.2.2.2.2 (Pinned.Y0Level h₅ htame h₂)).surjective
    ((source h₅ htame h₂).jX ≫ (π ≫ jE.inv))).choose_spec

/-- On the fixed rational target the restriction is the original map on the pinned open. -/
theorem hInt_target :
    ((generic (LocalIntegers ell) ℚ).map (πInt h₅ htame h₂ π neron jE) ≫ jE.hom).left =
      (genericIso h₅ htame h₂).hom.left ≫ restrictParametrization h₂ π.left := by
  rw [hInt, jX_eq_incl]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Over.comp_left, incl_left,
    restrictParametrization]

#print axioms source
#print axioms compactIso_hom
#print axioms jX_eq_incl
#print axioms πInt
#print axioms hInt
#print axioms hInt_target

end ZInQ.Manuscript.RC.ModelNeron
