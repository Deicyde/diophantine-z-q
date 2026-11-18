import ZInQKernel.Contrib.OneProof.DeRhamRange
import ZInQKernel.Contrib.OneProof.HodgeTateDecompOrH1

/-! derham-scholze: verbatim copies of the two research fields (with the definitions they use from the tree),
checked `Iff.rfl` against the tree's constants. -/

set_option linter.style.longLine false

namespace DeRhamScholzeStatement

open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4 ZInQ.Contrib.HodgeSplit Module
open DeRhamPrint.Direct ZInQ.Contrib.HodgeTateFromPairing
open scoped TensorProduct

/-- Copy of `DeRhamPrint.Direct.DeRhamVpAbVarDirect` (`ZInQKernel/Contrib/OneProof/DeRhamPrintDirect.lean` L187). -/
def DeRhamVpAbVarDirect : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
      finrank (fieldF p F) (ddrF p (A.galRep p)) = finrank ℚ_[p] (A.V p)

/-- Copy of `ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom` (`HodgeTateDecompOr.lean` L48). -/
def HodgeTateDecompHom : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : Type) [Field F] [Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F]
    (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F),
    ∃ (a b : ℕ) (e : (A.V p →ₗ[ℚ_[p]] ℂ_[p]) ≃ₗ[ℂ_[p]] (Fin a → ℂ_[p]) × (Fin b → ℂ_[p])),
      ∀ (σ : Field.absoluteGaloisGroup F) (f : A.V p →ₗ[ℚ_[p]] ℂ_[p]),
        e (cpLin p (gfToGqp p F σ) ∘ₗ f ∘ₗ A.galRep p σ⁻¹) =
          ((fun k => cpAct p (gfToGqp p F σ) ((e f).1 k)),
            (fun k => cycPow p (gfToGqp p F σ) (-1) • cpAct p (gfToGqp p F σ) ((e f).2 k)))

/-- Copy of `ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr` (`HodgeTateDecompOr.lean` L62); its first disjunct is
`HodgeTateFromPairing.HodgeTateDecompExists` (`HodgeTatePairingDecomp.lean` L44). -/
def HodgeTateDecompOr : Prop :=
  HodgeTateDecompExists ∨ HodgeTateDecompHom

theorem direct_iff : DeRhamVpAbVarDirect ↔ DeRhamPrint.Direct.DeRhamVpAbVarDirect := Iff.rfl

theorem hom_iff : HodgeTateDecompHom ↔ ZInQ.Contrib.HodgeTateOr.HodgeTateDecompHom := Iff.rfl

theorem or_iff : HodgeTateDecompOr ↔ ZInQ.Contrib.HodgeTateOr.HodgeTateDecompOr := Iff.rfl

end DeRhamScholzeStatement
