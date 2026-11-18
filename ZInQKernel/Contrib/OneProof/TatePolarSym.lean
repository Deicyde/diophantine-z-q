import ZInQKernel.Contrib.OneProof.TatePolarSymTate
import ZInQKernel.Contrib.OneProof.HodgeFil1
import ZInQKernel.Contrib.TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Map

/-! Cyclotomic self-duality and the resulting Hodge number in degree one. -/

noncomputable section

namespace HodgeFil1

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

set_option maxHeartbeats 1500000
set_option synthInstance.maxHeartbeats 250000

/-- Every abelian variety over a finite extension of `ℚ_p` has a nondegenerate
bilinear form on its rational Tate module with cyclotomic multiplier. -/
theorem tatePolarizationSymmetry_proof : TatePolarizationSymmetry := by
  intro p _ F _ _ _ A
  have : CharZero F := charZero_of_injective_algebraMap (algebraMap ℚ_[p] F).injective
  let A₀ := DeRhamPrint.toKer A
  obtain ⟨D⟩ := TatePolar.exists_nativePolarization A₀
  obtain ⟨B, hnd, hB⟩ := TatePolar.rational_form D p
  refine ⟨B, hnd, ?_⟩
  intro σ x y
  have hcyc :
      cyclotomicCharacter (PadicAlgCl p) p (gfToGqp p F σ).toRingEquiv =
        cyclotomicCharacter (AlgebraicClosure F) p σ.toRingEquiv :=
    TauCeti.localCyclotomicCharacter_map p (algebraMap ℚ_[p] F) σ
  rw [DeRhamScholze.TT.cycPow_one_eq, hcyc]
  exact hB σ x y

/-- The current degree-one row follows from de Rhamness, its filtration range
and the existing Tate duality statement, in every dimension. -/
theorem scholzeH1AbVar_of_dR (hDR : ScholzeH1AbVarDR) (hT : T10Etale.T10_TateDuality) :
    DeRhamScholze.HTMerge.ScholzeH1AbVar :=
  fil1_of_dR hDR hT tatePolarizationSymmetry_proof

#print axioms tatePolarizationSymmetry_proof
#print axioms scholzeH1AbVar_of_dR

end HodgeFil1
