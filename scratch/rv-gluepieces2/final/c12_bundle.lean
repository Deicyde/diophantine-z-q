import Check_c1_g10
import Check_c2_proved
import Check_c3_swan
import Check_c4_dirichlet
import Check_c5_g12det
import Check_c6_metrization
import Check_c7_heightbc
import Check_c8_fibrecover
import Check_c9_pin_transfer
import Check_c10_g9
import Check_c11_burnside

/-! ## rv-gluepieces2 (l): `GluePieces3`, the 27 fields of `GluePieces2` after this review

Over the pinned `Leaves.lean` (post pin-apply) and g0-assemble's parts (TailBase), with the checks
c1-c11 imported. Removed (proved on G0Assemble's own constants): 3 `finiteDescends`,
6 `metrizationDimUnique`, 14 `unramifiedSup`, 15 `burnsideAbsIrred`, 22 `dirichletOfFinite` (from the
bundle's `t17`), 24-26 `swanIndependent`, `swanIntegral`, `adaptedExists`. Replaced: 18 `g10Glue` by
g10-odd's strictly smaller `ConjTwistNontrivial`. The six pin-dependent fields (4, 10, 12, 13, 27, 28)
are asked for ONE triple satisfying the repaired clauses (`qmAt`), plus pin-apply's `MobiusGlue`.
15 fields instead of 27. -/

namespace HSyn

structure GluePieces3 : Prop where
  mulIsogeny : G0FibreSimple.MulIsogeny
  rigidityHom : G0FibreSimple.RigidityHom
  analyticUniformizationUnique : ZInQ.DefFaltings.AnalyticUniformizationUnique
  metrizationExists : ZInQ.G0HeightAdd.MetrizationExists
  productMetrizationGeo : ZInQ.G0HeightAdd.ProductMetrizationGeo
  hodgeLineBaseChange : G0StableBC.HodgeLineBaseChange
  thetaRatiosAlgebraic : G0Split.ThetaPt.ThetaRatiosAlgebraic
  r14Det : G0Galois.R14Det
  g9Glue : G0Galois.G9Glue
  conjTwistNontrivial : G0Galois.ConjTwistNontrivial
  g12Weight : G0Galois.G12Weight
  detTate : G0Galois.DetTate
  carayolR17 : LadicCond.CarayolR17'
  mobius : LeafQM.AV.Pin.MobiusGlue
  qmAt : ∃ (Y : CategoryTheory.Over (AlgebraicGeometry.Spec (CommRingCat.of ℚ)))
      (Φ : LeafQM.AV.PtEquiv Y) (π : LeafQM.AV.ToP1 Y.left),
    LeafQM.AV.R1fpProps Y Φ ∧ LeafQM.AV.R2fpProps Y Φ π ∧
    G0FibreSimple.FibreComTrivialAt Y Φ π ∧ G0Split.ThetaPt.FibreQMPeriodAt Y Φ π ∧
    G0ModField.FibreCoverExistsAt Y Φ π ∧ G0ModField.KernelFieldExistsAt Y Φ π ∧
    G0AssembleMod.ModelG3G6At Y Φ π ∧ G0AssembleMod.LinkedTateDataAt Y Φ π

theorem gluePieces2_of_3 (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces3) :
    GluePieces2 := by
  obtain ⟨Y, Φ, π, h1, h2, a, b, c, d, e, f⟩ := gp.qmAt
  have hQM := LeafAdopt.R1R2fp_of_rep r.r1r2
  exact
    { mulIsogeny := gp.mulIsogeny
      rigidityHom := gp.rigidityHom
      finiteDescends := RvGP2.finiteDescends
      fibreComTrivial := G0FibreSimple.fibreComTrivial_of_at gp.mobius hQM h1 h2 a
      analyticUniformizationUnique := gp.analyticUniformizationUnique
      metrizationDimUnique := RvGP2.metrizationDimUnique
      metrizationExists := gp.metrizationExists
      productMetrizationGeo := gp.productMetrizationGeo
      hodgeLineBaseChange := gp.hodgeLineBaseChange
      fibreQMPeriod := G0Split.ThetaPt.fibreQMPeriod_of_at gp.mobius hQM h1 h2 b
      thetaRatiosAlgebraic := gp.thetaRatiosAlgebraic
      fibreCoverExists := G0ModField.fibreCoverExists_of_at gp.mobius hQM h1 h2 c
      kernelFieldExists := G0ModField.kernelFieldExists_of_at gp.mobius hQM h1 h2 d
      unramifiedSup := RvGP2.unramifiedSup
      burnsideAbsIrred := RvGP2.burnsideAbsIrred
      r14Det := gp.r14Det
      g9Glue := gp.g9Glue
      g10Glue := G0Galois.g10Glue_of_conjTwist_new gp.conjTwistNontrivial
      g12Weight := gp.g12Weight
      detTate := gp.detTate
      dirichletOfFinite := RvGP2.dirichletOfFinite t
      carayolR17 := gp.carayolR17
      swanIndependent := RvGP2.swanIndependent
      swanIntegral := RvGP2.swanIntegral
      adaptedExists := RvGP2.adaptedExists
      modelG3G6 := G0AssembleMod.modelG3G6_of_at gp.mobius hQM h1 h2 e
      linkedTateData := G0AssembleMod.linkedTateData_of_at gp.mobius hQM h1 h2 f }

/-- **G0 after rv-gluepieces2** (over the pinned leaves): the two leaf bundles and the 15 fields of
`GluePieces3` imply `ZInQ.SixContactMin`. -/
theorem sixContactMin_of_leaves3 (r : ResearchLeaves) (t : TextbookLeaves) (gp : GluePieces3) :
    ZInQ.SixContactMin :=
  sixContactMin_of_leaves2 r t (gluePieces2_of_3 r t gp)

end HSyn

#print axioms HSyn.gluePieces2_of_3
#print axioms HSyn.sixContactMin_of_leaves3
