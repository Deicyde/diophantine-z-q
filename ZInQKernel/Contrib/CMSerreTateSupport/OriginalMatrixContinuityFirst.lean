import ZInQKernel.Contrib.CMSerreTateSupport.OriginalDivisionMatrixScalarImage

/-!
# Continuity of the original adic Tate matrix representation

The actual finite division-field restrictions give all finite-level
continuity. The embedding into the genuine adic residue product gives
continuity of the original whole integral matrix representation.
-/

noncomputable section
set_option autoImplicit false

namespace NativeTateCongruence

open CategoryTheory AlgebraicGeometry MonObj Topology Matrix

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
variable [CharZero K] [IsAlgClosure K Ω]
variable {d : Type*} [Fintype d] [DecidableEq d]

theorem originalTateMatrix_continuous (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime]
    (b : Module.Basis d ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))))
    [∀ n : ℕ, Finite (ActualFiniteLevel.torsionSubgroup A Ω (ell ^ (n + 1)))] :
    Continuous (originalTateMatrix A ell b) := by
  apply (IntegralCongruence.allLevels_isClosedEmbedding (d := d) ell).isInducing.continuous_iff.mpr
  apply continuous_pi
  intro n
  change Continuous (matrixLevel A ell b n)
  exact matrixLevel_continuous A ell b n

#check originalTateMatrix_continuous
#print axioms originalTateMatrix_continuous

end NativeTateCongruence
