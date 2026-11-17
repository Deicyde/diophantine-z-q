import ZInQKernel.OneProof.H.TailS

/-! The field, copied verbatim from `ZInQKernel/OneProof/H/TailS.lean` l. 347 (task hodgetate-from-dr), and
checked `Iff.rfl` against the original. -/

namespace ZInQ.Contrib.HodgeSplit.HodgetateFromDRCopy

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open scoped TensorProduct

def HodgeTateDecompAbVar : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
    ∃ e : ℂ_[p] ⊗[ℚ_[p]] A.V p ≃ₗ[ℂ_[p]] (Fin g → ℂ_[p]) × (Fin g → ℂ_[p]),
      ∀ (σ : Field.absoluteGaloisGroup F) (x : ℂ_[p] ⊗[ℚ_[p]] A.V p),
        e (TensorProduct.map (cpLin p (gfToGqp p F σ)) (A.galRep p σ) x) =
          ((fun k => cycPow p (gfToGqp p F σ) 1 • cpAct p (gfToGqp p F σ) ((e x).1 k)),
            (fun k => cpAct p (gfToGqp p F σ) ((e x).2 k)))

example : HodgeTateDecompAbVar ↔ ZInQ.Contrib.HodgeSplit.HodgeTateDecompAbVar := Iff.rfl

end ZInQ.Contrib.HodgeSplit.HodgetateFromDRCopy
