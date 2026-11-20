import ZInQKernel.Contrib.CloudR2CM.SerreTate.ArithmeticInputStatements
import ZInQKernel.Contrib.CMSerreTateSupport.OriginalWildImageContracts
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The original Tate inclusion and reflection of operator commutation

An actual integral basis gives an injective rationalization map. Operator
comparison is then reflected through that same map, without a rank formula
or a finite-image premise. The rational Galois operators are the scalar
extensions of the original integral operators.
-/

set_option autoImplicit false

noncomputable section

open scoped CategoryTheory.MonObj
open scoped TensorProduct

namespace HDec.CMSerreTate.P1

/-- The canonical inclusion of the original integral Tate module into its
original rational Tate module. -/
def tateToRational {K : Type} [Field K] (A : _root_.PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] : A.T ℓ →ₗ[ℤ_[ℓ]] A.V ℓ :=
  _root_.TensorProduct.mk ℤ_[ℓ] ℚ_[ℓ] (A.T ℓ) 1

/-- Rationalization of the actual integral Tate module is injective. The
basis is derived from the original torsion, with no supplied rank. -/
theorem tateToRational_injective {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (tateToRational A ℓ) := by
  obtain ⟨r, ⟨e⟩⟩ := _root_.OriginalWildTateImage.original_tate_basis
    (Ω := AlgebraicClosure K) A ℓ
  let b : Module.Basis (Fin r) ℤ_[ℓ] (A.T ℓ) :=
    (Pi.basisFun ℤ_[ℓ] (Fin r)).map e.symm
  intro x y hxy
  apply b.repr.injective
  ext i : 1
  apply PadicInt.ext
  have hi := congrArg
    (fun z : A.V ℓ => (_root_.Algebra.TensorProduct.basis ℚ_[ℓ] b).repr z i) hxy
  simpa only [tateToRational, TensorProduct.mk_apply, _root_.Algebra.TensorProduct.basis_repr_tmul,
    one_smul, Finsupp.mapRange_apply, PadicInt.algebraMap_apply] using hi

/-- Scalar extension reflects equality of original integral Tate
endomorphisms, through the actual injective inclusion. -/
theorem baseChangeTate_injective {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    Function.Injective (fun f : A.T ℓ →ₗ[ℤ_[ℓ]] A.T ℓ => f.baseChange ℚ_[ℓ]) := by
  intro f g hfg
  apply LinearMap.ext
  intro x
  apply tateToRational_injective A ℓ
  have hx := congrArg (fun u : A.V ℓ →ₗ[ℚ_[ℓ]] A.V ℓ => u (tateToRational A ℓ x)) hfg
  change (f.baseChange ℚ_[ℓ]) ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) =
    (g.baseChange ℚ_[ℓ]) ((1 : ℚ_[ℓ]) ⊗ₜ[ℤ_[ℓ]] x) at hx
  rw [LinearMap.baseChange_tmul, LinearMap.baseChange_tmul] at hx
  exact hx

/-- Rational Galois commutation gives commutation of the same original
integral Tate operators, not of an unrelated representation. -/
theorem galT_commute_of_galRep_commute {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (σ τ : Field.absoluteGaloisGroup K)
    (h : Commute (A.galRep ℓ σ) (A.galRep ℓ τ)) :
    Commute (_root_.ReductSplit.galTΩ A ℓ σ) (_root_.ReductSplit.galTΩ A ℓ τ) := by
  change A.galT (ℓ := ℓ) σ * A.galT (ℓ := ℓ) τ =
    A.galT (ℓ := ℓ) τ * A.galT (ℓ := ℓ) σ
  apply baseChangeTate_injective A ℓ
  change Commute ((A.galT (ℓ := ℓ) σ).baseChange ℚ_[ℓ])
    ((A.galT (ℓ := ℓ) τ).baseChange ℚ_[ℓ]) at h
  simpa only [LinearMap.baseChange_mul] using h.eq

/-- Whole-image rational commutation is reflected to the exact
whole-image integral predicate. -/
theorem galoisImageAbelian_of_galRep_commutation {K : Type} [Field K] [NumberField K]
    (A : _root_.PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (h : ∀ σ τ : Field.absoluteGaloisGroup K,
      Commute (A.galRep ℓ σ) (A.galRep ℓ τ)) :
    HDec.CMSerreTate.GaloisImageAbelian A ℓ := by
  intro σ τ
  exact galT_commute_of_galRep_commute A ℓ σ τ (h σ τ)

end HDec.CMSerreTate.P1
