import ZInQKernel.Contrib.OneProof.ScholzeH1AbVar

/-! ht-merge: statement checks and axioms. The conclusions of the four re-proved theorems are the tree's Props
(`DeRhamPrint.Direct.DeRhamVpAbVarDirect`, `HodgeTateOr.HodgeTateDecompHom`, `HodgeTateOr.HodgeTateDecompOr`,
`HodgeSplit.HodgeTateDecompAbVar`); the H field is copied verbatim from `ZInQKernel/OneProof/H/TailS.lean` L347 and
checked `Iff.rfl`. Each old theorem and its new counterpart are shown to have the same conclusion type. -/

open scoped TensorProduct
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit

noncomputable section

def HodgeTateDecompAbVarCopy : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

example : HodgeTateDecompAbVarCopy ↔ ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar := Iff.rfl

-- old theorem (two leaves) and new theorem (one leaf): same conclusions
example : DeRhamScholze.ScholzeDeRhamAlg → T10Etale.T10_TateDuality → AvSplit.MumfordTorsionAlgClosed →
    DeRhamPrint.Direct.DeRhamVpAbVarDirect := DeRhamScholze.deRhamVpAbVarDirect_of_scholze
example : DeRhamScholze.HTMerge.ScholzeH1AbVar → T10Etale.T10_TateDuality → AvSplit.MumfordTorsionAlgClosed →
    DeRhamPrint.Direct.DeRhamVpAbVarDirect := DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1

example : DeRhamScholze.ScholzeDeRhamAlg → T10Etale.T10_TateDuality → AvSplit.MumfordTorsionAlgClosed →
    DeRhamScholze.DeRhamHodgeTate01 → ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom :=
  DeRhamScholze.hodgeTateDecompHom_of_scholze
example : DeRhamScholze.HTMerge.ScholzeH1AbVar → T10Etale.T10_TateDuality → AvSplit.MumfordTorsionAlgClosed →
    DeRhamScholze.DeRhamHodgeTate01 → ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom :=
  DeRhamScholze.HTMerge.hodgeTateDecompHom_of_scholzeH1

example : DeRhamScholze.ScholzeDeRhamAlg → T10Etale.T10_TateDuality → ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  DeRhamScholze.TT.hodgeTateDecompOr_of_scholzeMilne
example : DeRhamScholze.HTMerge.ScholzeH1AbVar → T10Etale.T10_TateDuality →
    ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr :=
  DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne

example : DeRhamScholze.ScholzeDeRhamAlg → T10Etale.T10_TateDuality → DeRhamScholze.HTAbVar.HodgeNumberH1AbVar →
    HodgeTateDecompAbVarCopy := DeRhamScholze.HTAbVar.hodgeTateDecompAbVar_of_scholze
example : DeRhamScholze.HTMerge.ScholzeH1AbVar → T10Etale.T10_TateDuality → HodgeTateDecompAbVarCopy :=
  DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1

-- nothing lost: old pair → new leaf; new leaf → g = 2 form, and → the Hodge-number leaf
example : DeRhamScholze.ScholzeDeRhamAlg → DeRhamScholze.HTAbVar.HodgeNumberH1AbVar →
    DeRhamScholze.HTMerge.ScholzeH1AbVar := DeRhamScholze.HTMerge.scholzeH1AbVar_of_old

end

#print axioms DeRhamScholze.HTMerge.scholzeH1AbVar_of_old
#print axioms DeRhamScholze.HTMerge.scholzeH1AbSurf_of_abVar
#print axioms DeRhamScholze.HTMerge.hodgeNumberH1AbVar_of_scholzeH1
#print axioms DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1
#print axioms DeRhamScholze.HTMerge.deRhamVpAbVarDirect_of_scholzeH1Milne
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompHom_of_scholzeH1
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompOr_of_scholzeH1Milne
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_scholzeH1
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompAbVar_of_old
#print axioms DeRhamScholze.HTMerge.hodgeTateDecompAbSurf_of_scholzeH1AbSurf
