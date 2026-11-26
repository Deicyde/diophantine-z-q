import ZInQKernel.Contrib.OneProof.C8DeRham.CheckedLocalGlue

/-! # C8 with internal comparison lemmas supplied

The weight match comes after the finite ray-class factorization. The final
receivers keep the literature propositions explicit; they do not add them as
axioms or postulate a de Rhamness result about an arbitrary attached model.
-/

noncomputable section

namespace HDec.G0Galois.C8Conrad.Manuscript

open _root_.PkgI4 (GaloisRep)

/-- The exact manuscript-order receiver, with the original Conrad citation. -/
theorem g12Out_of_kato_conrad
    (hKato : C8Kato.NewformGeometricComparison) (hR : HSyn.EigenformRepExists)
    (hDS : HSyn.DeligneSerreConseq) (hPB : PkgI4.PanBerger) (hConrad : Bridges.ConradAppBPrint)
    (r : GaloisRep 5 2) (T : Finset ℕ) (hirr : r.IsIrreducible) (h9 : G9Out r)
    (h10 : G10Out r) (h11 : G11Out T r) : G12Out r :=
  g12Out_from_kato_conrad deRhamExtends_proof deRhamHasRows_proof conjOfTraceIrredFive_proof
    hKato hR hDS hPB hConrad r T hirr h9 h10 h11

/-- The alternative local literature interface is the existing Serre
specialization that implies the Conrad interface, not a second premise. -/
theorem g12Out_of_kato_serre
    (hKato : C8Kato.NewformGeometricComparison) (hR : HSyn.EigenformRepExists)
    (hDS : HSyn.DeligneSerreConseq) (hPB : PkgI4.PanBerger)
    (hSerre : SerreAppB.LocalArtin.serreA6OnIntegerUnits)
    (r : GaloisRep 5 2) (T : Finset ℕ) (hirr : r.IsIrreducible) (h9 : G9Out r)
    (h10 : G10Out r) (h11 : G11Out T r) : G12Out r :=
  g12Out_from_kato_serre deRhamExtends_proof deRhamHasRows_proof conjOfTraceIrredFive_proof
    hKato hR hDS HSyn.frobeniusDense_proved hPB hSerre r T hirr h9 h10 h11

end HDec.G0Galois.C8Conrad.Manuscript
