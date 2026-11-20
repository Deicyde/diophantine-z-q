import ZInQKernel.Contrib.CMSerreTateSupport.OriginalWildTateImageBound
import ZInQKernel.Contrib.CMSerreTateSupport.OriginalMatrixContinuityFirst

/-!
# The original finite-free Tate lattice and continuous Galois action

Both the finite basis and the continuous original matrix representation
are produced from the original geometric torsion and compatible Tate
objects. No caller basis, rank or representation is supplied.
-/

noncomputable section
set_option autoImplicit false

namespace OriginalWildTateImage

open CategoryTheory AlgebraicGeometry MonObj Matrix
open NativeTateCongruence ActualFiniteLevel

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
variable [CharZero K] [IsAlgClosure K Ω]

theorem original_tate_finite_free (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime] :
    Module.Free ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))) ∧
    Module.Finite ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))) := by
  obtain ⟨r, ⟨E⟩⟩ := original_tate_basis (Ω := Ω) A ell
  exact ⟨Module.Free.of_equiv E.symm, Module.Finite.equiv E.symm⟩

theorem original_continuous_tate_basis (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime] :
    ∃ r : ℕ, ∃ b : Module.Basis (Fin r) ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))),
      Continuous (originalTateMatrix A ell b) := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap K Ω).injective
  obtain ⟨r, ⟨E⟩⟩ := original_tate_basis (Ω := Ω) A ell
  let b : Module.Basis (Fin r) ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))) :=
    (Pi.basisFun ℤ_[ell] (Fin r)).map E.symm
  haveI : ∀ n : ℕ, Finite (torsionSubgroup A Ω (ell ^ (n + 1))) := fun n =>
    original_torsion_finite A (ell ^ (n + 1)) (by
      rw [Nat.cast_pow]
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : ell.Prime).ne_zero))
  exact ⟨r, b, originalTateMatrix_continuous A ell b⟩

#check original_tate_finite_free
#print axioms original_tate_finite_free
#check original_continuous_tate_basis
#print axioms original_continuous_tate_basis

end OriginalWildTateImage
