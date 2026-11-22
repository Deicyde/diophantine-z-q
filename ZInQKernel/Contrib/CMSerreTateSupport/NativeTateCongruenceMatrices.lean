import ZInQKernel.Contrib.CMSerreTateSupport.CompatibleTateCountsProvenance
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Original Tate action and projection congruences

The representation below is the original Spec-precomposition Galois
action on the literal compatible-point Tate module. Projection kernels
are exactly powers of ell times that module.
-/

noncomputable section
set_option autoImplicit false

namespace NativeTateCongruence

open CategoryTheory AlgebraicGeometry MonObj

section Sequences

variable {ell : ℕ} [Fact ell.Prime] {M : Type*} [AddCommGroup M]

/-- The integral scalar ell^n acts by the literal integer multiplication
on every component of the original sequence object. -/
theorem scalar_power_apply (t : PkgI3.Tate.T ell M) (n k : ℕ) :
    (((ell : ℤ_[ell]) ^ n) • t).1 k = (ell ^ n) • t.1 k := by
  exact PkgI3.Tate.smulSeq_congr t.2 k (c := ell ^ n) (by simp)

/-- Zero at level n is exactly divisibility by ell^n in the original
Tate module. The quotient element is constructed by shifting points. -/
theorem projection_zero_iff_divisible (t : PkgI3.Tate.T ell M) (n : ℕ) :
    t.1 n = 0 ↔ ∃ s : PkgI3.Tate.T ell M, t = (ell : ℤ_[ell]) ^ n • s := by
  constructor
  · intro ht
    let s : PkgI3.Tate.T ell M := ⟨fun k => t.1 (k + n), by simpa using ht, fun k => by
      simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using t.2.2 (k + n)⟩
    refine ⟨s, Subtype.ext (funext fun k => ?_)⟩
    rw [scalar_power_apply]
    exact (OriginalCompatibleTate.pow_smul_add t.2 k n).symm
  · rintro ⟨s, rfl⟩
    rw [scalar_power_apply]
    exact PkgI3.Tate.pow_smul_eq_zero s.2 n

/-- Projection of the actual Tate sequence to its original torsion point. -/
def projectPointTate (n : ℕ) : PkgI3.Tate.T ell M →+ OriginalCompatibleTate.tb ell M n where
  toFun t := ⟨t.1 n, OriginalCompatibleTate.mem_tb.mpr (PkgI3.Tate.pow_smul_eq_zero t.2 n)⟩
  map_zero' := rfl
  map_add' _ _ := rfl

end Sequences

section OriginalAction

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

/-- The original integral representation, for the original algebraic
closure object rather than a caller-provided representation. -/
def originalTateRep (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime] :
    Representation ℤ_[ell] (Ω ≃ₐ[K] Ω) (PkgI3.Tate.T ell (Additive (A.Pt Ω))) where
  toFun σ := PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct σ))
  map_one' := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext n
    change Additive.ofMul (PkgI3.AbVar.galHom (1 : Ω ≃ₐ[K] Ω) ≫ Additive.toMul (t.1 n)) = t.1 n
    rw [PkgI3.AbVar.galHom_one, Category.id_comp]
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro t
    apply Subtype.ext
    funext n
    change Additive.ofMul (PkgI3.AbVar.galHom (σ * τ) ≫ Additive.toMul (t.1 n)) =
      Additive.ofMul (PkgI3.AbVar.galHom σ ≫ PkgI3.AbVar.galHom τ ≫ Additive.toMul (t.1 n))
    rw [PkgI3.AbVar.galHom_mul, Category.assoc]

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Matrix coordinates of the actual action, once a basis has been
constructed from the genuine compatible torsion counts. -/
def originalTateMatrix (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime]
    (b : Module.Basis d ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω)))) :
    (Ω ≃ₐ[K] Ω) →* Matrix.GeneralLinearGroup d ℤ_[ell] :=
  (Units.map (LinearMap.toMatrixAlgEquiv b).toRingHom.toMonoidHom).comp
    (originalTateRep A ell).asGroupHom

theorem original_matrix_entry (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime]
    (b : Module.Basis d ℤ_[ell] (PkgI3.Tate.T ell (Additive (A.Pt Ω))))
    (σ : Ω ≃ₐ[K] Ω) (i j : d) :
    (originalTateMatrix A ell b σ).val i j = b.repr (originalTateRep A ell σ (b j)) i := by
  simp [originalTateMatrix, Representation.asGroupHom_apply, LinearMap.toMatrixAlgEquiv_apply]

/-- At the distinguished algebraic closure the representation is the
original integral action already used by the rational Tate representation. -/
theorem original_rep_eq_galT (A : PkgI3.AbVar K) (ell : ℕ) [Fact ell.Prime]
    (σ : Field.absoluteGaloisGroup K) : originalTateRep A ell σ = A.galT σ := rfl

end OriginalAction

#check projection_zero_iff_divisible
#print axioms projection_zero_iff_divisible
#check originalTateMatrix
#print axioms originalTateRep
#print axioms original_matrix_entry

end NativeTateCongruence
