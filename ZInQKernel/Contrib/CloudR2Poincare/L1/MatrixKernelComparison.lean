import ZInQKernel.Contrib.CloudR2Poincare.L1.SplitKernelBaseChange
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.LinearAlgebra.Matrix.ComplementaryMinors
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-! Actual matrix splitting gives canonical kernel preservation. This is the
adapter from the already proved reduced constant-rank matrix data to the
actual kernelComparison, not an assertion of generic exactness. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits
open scoped Matrix

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Split degree-zero matrix homology gives an isomorphism of the ACTUAL
canonical kernel comparison under every additive functor. -/
theorem isIso_kernelComparison_of_matrix_split
    {R : Type u} [CommRing R] {D : Type*} [Category* D] [Preadditive D] [HasKernels D]
    (F : ModuleCat.{u} R ⥤ D) [F.Additive]
    {a m n k : Type u} [Fintype a] [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k]
    (A : Matrix m n R) (h : Matrix.HasSplitHomology (0 : Matrix n a R) A k) :
    IsIso (kernelComparison (ModuleCat.ofHom A.mulVecLin) F) := by
  obtain ⟨I, P, σ, τ, _, hAI, _, hsum⟩ := h
  have hs : I * P + τ * A = 1 := by simpa only [Matrix.zero_mul, add_zero] using hsum
  let f : ModuleCat.of R (n → R) ⟶ ModuleCat.of R (m → R) := ModuleCat.ofHom A.mulVecLin
  let i : ModuleCat.of R (k → R) ⟶ ModuleCat.of R (n → R) := ModuleCat.ofHom I.mulVecLin
  let p : ModuleCat.of R (n → R) ⟶ ModuleCat.of R (k → R) := ModuleCat.ofHom P.mulVecLin
  let t : ModuleCat.of R (m → R) ⟶ ModuleCat.of R (n → R) := ModuleCat.ofHom τ.mulVecLin
  have hi : i ≫ f = 0 := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    change (A *ᵥ (I *ᵥ x)) j = 0
    rw [Matrix.mulVec_mulVec, hAI, Matrix.zero_mulVec]
    rfl
  have ht : p ≫ i + f ≫ t = 𝟙 (ModuleCat.of R (n → R)) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    funext j
    change (I *ᵥ (P *ᵥ x) + τ *ᵥ (A *ᵥ x)) j = x j
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.add_mulVec, hs, Matrix.one_mulVec]
  exact isIso_kernelComparison_of_contracting_split F f i p t hi ht

end ZInQ.Contrib.CloudR2Poincare.L1
