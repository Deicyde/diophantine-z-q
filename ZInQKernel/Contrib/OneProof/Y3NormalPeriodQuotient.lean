import ZInQKernel.Contrib.OneProof.Y3RepresentedFibres
import ZInQKernel.Contrib.OneProof.Y3QuotientNormal
import ZInQKernel.Contrib.OneProof.Y3ComplexQuotient
import ZInQKernel.Contrib.OneProof.DeligneComponentsY3Used

/-! The actual normal rational quotient and its period map on one witness of
the printed fine-moduli problem. -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open LeafQM LeafQM.AV LeafQM.AV.R1UnivRigid
open HDec.QMSplit.Moduli HDec.HSyn.G0Split.FibreQM.PeriodMapH
open Y3Fix Y3RouteA

namespace Y3P1j

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

/-- The printed integral model and Deligne period data give an actual normal
proper integral quotient curve, with its exact geometric fibres and period
map. -/
theorem exists_normal_period_quotient_of_z30
    (hI : Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hL : QMTwistLattice) :
    ∃ (Y : Over (Spec (CommRingCat.of ℚ))) (Φ : PtEquiv Y)
      (Z : Over (Spec (CommRingCat.of ℚ))) (π : Y ⟶ Z)
      (F : UpperHalfPlane → (fieldPt ℂ ⟶ Z)),
      R1fpPropsAbP Y Φ ∧ IsProper Z.hom ∧ IsIntegral Z.left ∧
      ZInQ.Contrib.CurvesG.IsNormalScheme Z.left ∧ topologicalKrullDim Z.left = 1 ∧
      IsFinite π.left ∧ Surjective π.left ∧
      (∀ (K : Type) [Field K] [Algebra ℚ K] (y y' : fieldPt K ⟶ Y) (P Q : QML3 K),
        Φ K y = M3.mk P → Φ K y' = M3.mk Q →
          (y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q))) ∧
      Function.Surjective F ∧ ShimuraSplit.IsHolFamily (fun τ => (F τ).left) ∧
      ∀ τ τ', F τ = F τ' ↔ ∃ g ∈ HDec.PkgI1.GammaStar, g • τ = τ' := by
  obtain ⟨Y, 𝒜, hp, hs, hU⟩ := y3RepresentableQ_of_z30 hI
  have hT := AvSplit.torsionStructure_of_mumford
    ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof
  obtain ⟨Φ, hΦ, hΦfib⟩ := Y3Audit.exists_fineModuliAt_of_rep hT hp hs hU
  obtain ⟨Ψ, hB, -⟩ := Y3Hodge.deligneH_of_print hD Y Φ hΦ
  have : ConnectedSpace Y.left := DCY3Used.connected_of_body (body_of_H hB)
  have hYI := HDec.TSHecke.irreducibleSpace_of_connected Y.hom hp hs
  obtain ⟨Z, π, hπ, hfin, hZP, hsur, hInt, hNorm, hDim, hsections⟩ :=
    exists_normal_twistMark_scheme_quotient hp hs hU hYI
  have : Surjective π.left := ⟨hsur⟩
  have hN := Y3Audit.isLocallyNoetherian_of_smooth_Q Y hs
  have : Finite (twistMarkGroup hU hN) := twistMarkGroup_finite hU hN
  have hfib (K : Type) [Field K] [Algebra ℚ K] (y y' : fieldPt K ⟶ Y) (P Q : QML3 K)
      (hP : Φ K y = M3.mk P) (hQ : Φ K y' = M3.mk Q) :
      y ≫ π = y' ≫ π ↔ ∃ α : O ≃+* O, Nonempty (QMIso (P.q.twist α) Q.q) := by
    have hOrb := InvariantSchemePoints.point_orbit_iff (twistMarkSchemeAction hU hN) Y.hom
      (fun g => g.val.asIso.hom.w) π.left hπ hsections y'.left y.left y'.w y.w
    rw [← twistMarkGroup_orbit_iff hU hN y y' P Q ((hΦfib K y P).mp hP) ((hΦfib K y' Q).mp hQ)]
    constructor
    · intro h
      obtain ⟨g, hg⟩ := hOrb.mp (congrArg CommaMorphism.left h.symm)
      exact ⟨g, Over.OverMorphism.ext hg⟩
    · rintro ⟨g, hg⟩
      exact Over.OverMorphism.ext (hOrb.mpr ⟨g, congrArg CommaMorphism.left hg⟩).symm
  obtain ⟨F, hF, hhol, horb⟩ := exists_complex_quotient_period_map π (hfib ℂ) hΦ hD hL
  exact ⟨Y, Φ, Z, π, F, hΦ, hZP, hInt, hNorm, hDim, hfin, ‹_›, hfib, hF, hhol, horb⟩

end Y3P1j

#print axioms Y3P1j.exists_normal_period_quotient_of_z30
