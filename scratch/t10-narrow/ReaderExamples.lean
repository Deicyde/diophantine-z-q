import ZInQKernel.Contrib.OneProof.T10NarrowReaders

/-! Each example has the original reader's statement and proves it via the local one. -/

set_option linter.style.longLine false
set_option linter.unusedSectionVars false
set_option synthInstance.maxHeartbeats 400000

namespace DeRhamScholze.HTMerge

open CategoryTheory AlgebraicGeometry
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamScholze.HT
open scoped TensorProduct

noncomputable section

section One

variable (p : ℕ) [Fact p.Prime] {F : Type} [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]

example (hT : T10Etale.T10_TateDuality) (hM : AvSplit.MumfordTorsionAlgClosed)
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (n : ℕ)
    (h : IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = n) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 ∧
      finrank ℚ_[p] (filD p (fun σ => (A.galRep p).dual σ) 1) = n :=
  dual_of_H1_loc p (T10Etale.t10Local_of_tateDuality hT) hM A n h

example (hT : T10Etale.T10_TateDuality) (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ)
    (hg : A.dim = (g : WithBot ℕ∞))
    (h : IsDeRhamFam p (F := F) (rhoH A.X p 1) ∧ HodgeRange p (F := F) (rhoH A.X p 1) 1 ∧
      finrank ℚ_[p] (filD p (F := F) (rhoH A.X p 1) 1) = finrank ℚ_[p] F * g) :
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k))) :=
  htDecomp_of_H1_loc p (T10Etale.t10Local_of_tateDuality hT) A g hg h

end One

example (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) (p : ℕ) [Fact p.Prime]
    (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) :
    IsDeRhamFam p (fun σ => (A.galRep p).dual σ) ∧ HodgeRange p (fun σ => (A.galRep p).dual σ) 1 :=
  dual_deRham_of_scholzeH1_loc hN (T10Etale.t10Local_of_tateDuality hT) hM p F A

example (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) : DeRhamPrint.Direct.DeRhamVpAbVarDirect :=
  deRhamVpAbVarDirect_of_scholzeH1_loc hN (T10Etale.t10Local_of_tateDuality hT) hM

example (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality) :
    DeRhamPrint.Direct.DeRhamVpAbVarDirect :=
  deRhamVpAbVarDirect_of_scholzeH1Milne_loc hN (T10Etale.t10Local_of_tateDuality hT)

example (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality)
    (hM : AvSplit.MumfordTorsionAlgClosed) (hW : DeRhamHodgeTate01) : ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom :=
  hodgeTateDecompHom_of_scholzeH1_loc hN (T10Etale.t10Local_of_tateDuality hT) hM hW

example (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality) :
    ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  hodgeTateDecompOr_of_scholzeH1Milne_loc hN (T10Etale.t10Local_of_tateDuality hT)

example (hN : ScholzeH1AbVar) (hT : T10Etale.T10_TateDuality) :
    HodgeTateDecompAbVar :=
  hodgeTateDecompAbVar_of_scholzeH1_loc hN (T10Etale.t10Local_of_tateDuality hT)

example (hS : ScholzeDeRhamAlg) (hT : T10Etale.T10_TateDuality)
    (hH : DeRhamScholze.HTAbVar.HodgeNumberH1AbVar) : HodgeTateDecompAbVar :=
  hodgeTateDecompAbVar_of_old_loc hS (T10Etale.t10Local_of_tateDuality hT) hH

example (hN : ScholzeH1AbSurf) (hT : T10Etale.T10_TateDuality) :
    HodgeTateDecompAbSurf :=
  hodgeTateDecompAbSurf_of_scholzeH1AbSurf_loc hN (T10Etale.t10Local_of_tateDuality hT)

end

end DeRhamScholze.HTMerge
