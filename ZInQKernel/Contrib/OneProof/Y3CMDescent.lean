import ZInQKernel.Contrib.OneProof.Y3CMClosedPoints
import ZInQKernel.Contrib.OneProof.Y3ComplexAL
import ZInQKernel.Contrib.OneProof.Y3CMBaseChangeReflection

/-! # CM descent from the printed level-three model and the analytic Hauptmodul -/

open LeafQM LeafQM.AV HDec RayClassCFT Y3RouteA
open HDec.HSyn.G0Split.FibreQM.PeriodMapH

namespace Y3P1j

/-- Descent to ℚ̄ for each of the distinguished CM types follows from the
fine-moduli scheme, its level action and the analytic Hauptmodul. -/
theorem cmDescends_of_z30 (hI : Y3FullThreeRepZ30) (hD : Y3Hodge.DeligneCanonicalModelY3EveryPrint)
    (hCentral : QMSplit.Aut.QMCentralizerCMC) (hA : CMAnalytic) (hH : PkgI1.QMHauptmodul)
    (hT : PkgI2.TorsionStructure.{0}) (hU : ZInQ.LeafPush2.UniformizationExists)
    (hC : HDec.HomUnify.HomLatticeCorr) (hR : ZInQ.LeafPush2.T11b_Rigidity) : CMDescends := by
  have hAL : ComplexALFixedPoints := fun P => QMSplit.Aut.alFixedPoints_complex_of hCentral P.A P.surface P.q
  intro Q
  have h (hcm : HasCM4 Q.q ∨ HasCM3 Q.q ∨ HasCM24 Q.q) :
      ∃ (ιe : Qbar →+* ℂ) (P : QML3 Qbar) (Q' : QML3 ℂ),
        IsBaseChangeOf ιe P Q' ∧ Nonempty (QMIso Q.q Q'.q) ∧
        (HasCM4 Q.q → HasCM4 P.q) ∧ (HasCM3 Q.q → HasCM3 P.q) ∧
        (HasCM24 Q.q → HasCM24 P.q) := by
    obtain ⟨ιe, P, Q', hBC, ⟨e⟩⟩ := cm_point_of_z30 hI hD hAL hA hH hT hU hC Q hcm
    obtain ⟨h4, h3, h24⟩ := cm_reflect_of_baseChange hR ιe P Q' hBC
    let eQM : QMIso Q.q Q'.q := ⟨e.φ, e.ψ, e.left, e.right, e.equivariant⟩
    exact ⟨ιe, P, Q', hBC, ⟨eQM⟩, fun h => h4 (HasCM4.of_iso eQM h),
      fun h => h3 (HasCM3.of_iso eQM h), fun h => h24 (HasCM24.of_iso eQM h)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h4
    obtain ⟨ιe, P, Q', hBC, he, h', -⟩ := h (Or.inl h4)
    exact ⟨ιe, P, Q', hBC, h' h4, he⟩
  · intro h3
    obtain ⟨ιe, P, Q', hBC, he, _, h', -⟩ := h (Or.inr (Or.inl h3))
    exact ⟨ιe, P, Q', hBC, h' h3, he⟩
  · intro h24
    obtain ⟨ιe, P, Q', hBC, he, _, _, h'⟩ := h (Or.inr (Or.inr h24))
    exact ⟨ιe, P, Q', hBC, h' h24, he⟩

end Y3P1j

#print axioms Y3P1j.cmDescends_of_z30
