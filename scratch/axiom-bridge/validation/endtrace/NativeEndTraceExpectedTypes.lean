import TateFreeness
import StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.CharPoly
import Mathlib.LinearAlgebra.Charpoly.BaseChange
import Mathlib.LinearAlgebra.Trace

/-
UNRUN PRIVATE SPECIFICATION, not a production supplier.

Expected propositions are independently spelled from original Objects, the
existing actual point/Tate construction, and the pinned Stacks rational
polynomial definition. This file does not import NativeEndTrace or obtain an
expected proposition from its declaration metadata. Compile it separately before
fresh-import comparisons so generated specification auxiliaries are present.
The stronger original integer-polynomial predicate is not asserted here.
-/

noncomputable section

namespace NativeEndTraceChecks

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
open scoped MonObj

/-- Specification-side rational polynomial from the SAME original pulled-back
endomorphism. No new provider theorem or desired trace assertion is used. -/
def expectedPolynomial {k : Type} [Field k] (A : PkgI3.AbVar k)
    (φ : PkgI3.AbVar.End A) : Polynomial ℚ := by
  letI := AxiomBridge.TateConsumer.geometric_isAbelianVariety A
  letI : IsMonHom (show (A.baseChange (AlgebraicClosure k)).X ⟶
      (A.baseChange (AlgebraicClosure k)).X from (baseChangedHom A A φ).hom.hom) :=
    (baseChangedHom A A φ).hom.isMonHom_hom
  exact Stacks.Groupoids.endCharPoly (A.baseChange (AlgebraicClosure k)).X
    (baseChangedHom A A φ).hom.hom

def expectedNaturality : Prop :=
  ∀ {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime] (x : A.T ℓ),
    letI : IsMonHom (show (A.baseChange (AlgebraicClosure k)).X ⟶
        (A.baseChange (AlgebraicClosure k)).X from (baseChangedHom A A φ).hom.hom) :=
      (baseChangedHom A A φ).hom.isMonHom_hom
    geometricTateEquiv A ℓ (PkgI3.AbVar.homT φ x) =
      Stacks.Groupoids.tateModuleMap ℓ (baseChangedHom A A φ).hom.hom
        (geometricTateEquiv A ℓ x)

def expectedConjugacy : Prop :=
  ∀ {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime],
    letI : IsMonHom (show (A.baseChange (AlgebraicClosure k)).X ⟶
        (A.baseChange (AlgebraicClosure k)).X from (baseChangedHom A A φ).hom.hom) :=
      (baseChangedHom A A φ).hom.isMonHom_hom
    (geometricTateEquiv A ℓ).conj (PkgI3.AbVar.homT (ℓ := ℓ) φ) =
      Stacks.Groupoids.tateModuleMap ℓ (baseChangedHom A A φ).hom.hom

def expectedMonic : Prop :=
  ∀ {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A),
    (expectedPolynomial A φ).Monic

def expectedRationalCharPoly : Prop :=
  ∀ {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    ∀ {I : Type*} [Fintype I] [DecidableEq I]
      (b : Module.Basis I ℚ_[ℓ] (A.V ℓ)),
    (LinearMap.toMatrix b b
      ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ])).charpoly =
        (expectedPolynomial A φ).map (algebraMap ℚ ℚ_[ℓ])

def expectedRationalTrace : Prop :=
  ∀ {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    LinearMap.trace ℚ_[ℓ] (A.V ℓ)
      ((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]) =
        ((-(expectedPolynomial A φ).nextCoeff : ℚ) : ℚ_[ℓ])

def expectedScalarTrace : Prop :=
  ∀ {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
    ∀ (L : Type) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L],
    LinearMap.trace L (TensorProduct ℚ_[ℓ] L (A.V ℓ))
      (((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange L) =
        ((-(expectedPolynomial A φ).nextCoeff : ℚ) : L)

/-- The actual bounded common-coefficient input. The rational witness is not
claimed integer; coefficient fields and maps remain genuine consumer data. -/
def expectedCommonCoefficient : Prop :=
  ∀ {k : Type} [Field k] (A : PkgI3.AbVar k) (φ : PkgI3.AbVar.End A)
    (C : Type) [Field C] [CharZero C],
    ∃ c : C, ∀ (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : k) ≠ 0 →
      ∀ (L : Type) [Field L] [CharZero L] [Algebra ℚ_[ℓ] L] (j : C →+* L),
      LinearMap.trace L (TensorProduct ℚ_[ℓ] L (A.V ℓ))
        (((PkgI3.AbVar.homT (ℓ := ℓ) φ).baseChange ℚ_[ℓ]).baseChange L) = j c

end NativeEndTraceChecks
