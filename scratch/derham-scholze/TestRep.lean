import ZInQKernel.HDecomp.Textbook.T10Etale
import ZInQKernel.Contrib.OneProof.DeRhamRange

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ZInQ.Contrib.G9 ZInQ.Contrib.G9.PkgI4

variable (p : ℕ) [Fact p.Prime]

theorem t1 {F : Type} [Field F] (A : ZInQ.Contrib.G9.PkgI4.I3.AbVar F) (σ : Field.absoluteGaloisGroup F)
    (v : A.V p) : A.galRep p σ v = ((DeRhamPrint.toKer A).galRep p σ : (DeRhamPrint.toKer A).V p → (DeRhamPrint.toKer A).V p) v :=
  ZInQ.Contrib.AbVarBC.vToI4_galRep p (DeRhamPrint.toKer A) σ v

theorem t2 {K : Type} [Field K] (A : PkgI3.AbVar K) (σ : Field.absoluteGaloisGroup K) :
    (A.galRep p σ : A.V p →ₗ[ℚ_[p]] A.V p) = (A.galT (ℓ := p) σ).baseChange ℚ_[p] := rfl
