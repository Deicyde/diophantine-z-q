import ZInQKernel.Contrib.CloudR2Poincare.L1.MatrixKernelComparison
import ZInQKernel.Contrib.CloudR2Poincare.L1.UniversalKernelComparison
import ZInQKernel.Contrib.CloudR2Poincare.L1.ScalarKernelComparisons
import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedKernelSplit
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# Actual scalar-extension kernels of constant-rank matrices

This is the ring-valued counterpart of the certified reduced sheaf-model
kernel theorem. Coordinates of scalar extension are computed on actual
pure tensors; a flat affine neighborhood and contracting matrix data then
preserve the ACTUAL kernelComparison along any field-valued ring map.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry TensorProduct
open scoped Matrix

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Literal coordinates on the scalar extension of a finite-coordinate free module. -/
def extendScalarsCoordinates (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (n : Type u) [Fintype n] :
    (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (n → R)) ≃ₗ[S] (n → S) :=
  (ModuleCat.tensorEquivExtendScalars R S (ModuleCat.of R (n → R))).symm.trans
    (Algebra.TensorProduct.basis S (Pi.basisFun R n)).equivFun

/-- The coordinate of a pure tensor is the actual scalar times its mapped coordinate. -/
theorem extendScalarsCoordinates_tmul (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    (n : Type u) [Fintype n] (s : S) (v : n → R) (i : n) :
    extendScalarsCoordinates R S n
      (ModuleCat.tensorEquivExtendScalars R S (ModuleCat.of R (n → R)) (s ⊗ₜ[R] v)) i =
      s * algebraMap R S (v i) := by
  classical
  simp only [extendScalarsCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply,
    Module.Basis.equivFun_apply, Algebra.TensorProduct.basis_repr_tmul]
  simp only [Finsupp.smul_apply, Finsupp.mapRange_apply, Pi.basisFun_repr,
    Finsupp.equivFunOnFinite_apply]
  rfl

/-- The ACTUAL scalar-extended matrix map is its scalar-mapped matrix in these coordinates. -/
theorem extendScalarsCoordinates_matrix (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
    {m n : Type u} [Fintype m] [Fintype n] (A : Matrix m n R)
    (v : (ModuleCat.extendScalars (algebraMap R S)).obj (ModuleCat.of R (n → R))) :
    extendScalarsCoordinates R S m
      ((ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom A.mulVecLin) v) =
    A.map (algebraMap R S) *ᵥ extendScalarsCoordinates R S n v := by
  classical
  obtain ⟨v, rfl⟩ := (ModuleCat.tensorEquivExtendScalars R S (ModuleCat.of R (n → R))).surjective v
  induction v using TensorProduct.induction_on with
  | zero => simp only [map_zero, Matrix.mulVec_zero]
  | add x y hx hy => simp only [map_add, Matrix.mulVec_add, hx, hy]
  | tmul s x =>
      rw [ModuleCat.tensorEquivExtendScalars_naturality, LinearMap.baseChange_tmul]
      funext j
      rw [extendScalarsCoordinates_tmul]
      have hc : extendScalarsCoordinates R S n
          (ModuleCat.tensorEquivExtendScalars R S (ModuleCat.of R (n → R)) (s ⊗ₜ[R] x)) =
          fun i ↦ s * algebraMap R S (x i) :=
        funext (extendScalarsCoordinates_tmul R S n s x)
      rw [hc]
      change s * algebraMap R S (∑ i, A j i * x i) =
        ∑ i, algebraMap R S (A j i) * (s * algebraMap R S (x i))
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul]
      ring

/-- Canonical scalar-extension kernel preservation transfers from its actual matrix coordinates. -/
theorem isIso_kernelComparison_extended_matrix_of_split
    (R S B : Type u) [CommRing R] [CommRing S] [CommRing B] [Algebra R S] [Algebra S B]
    {a m n k : Type u} [Fintype a] [Fintype m] [Fintype n] [Fintype k]
    [DecidableEq n] [DecidableEq k] (A : Matrix m n R)
    (h : Matrix.HasSplitHomology (0 : Matrix n a S) (A.map (algebraMap R S)) k) :
    IsIso (kernelComparison
      ((ModuleCat.extendScalars (algebraMap R S)).map (ModuleCat.ofHom A.mulVecLin))
      (ModuleCat.extendScalars (algebraMap S B))) := by
  let E := ModuleCat.extendScalars (algebraMap R S)
  let F := ModuleCat.extendScalars (algebraMap S B)
  let en := (extendScalarsCoordinates R S n).toModuleIso
  let em := (extendScalarsCoordinates R S m).toModuleIso
  let d : ModuleCat.of S (n → S) ⟶ ModuleCat.of S (m → S) :=
    ModuleCat.ofHom (A.map (algebraMap R S)).mulVecLin
  have hc : d ≫ em.inv = en.inv ≫ E.map (ModuleCat.ofHom A.mulVecLin) := by
    apply (cancel_mono em.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change A.map (algebraMap R S) *ᵥ v =
      extendScalarsCoordinates R S m
        (E.map (ModuleCat.ofHom A.mulVecLin) ((extendScalarsCoordinates R S n).symm v))
    rw [extendScalarsCoordinates_matrix, LinearEquiv.apply_symm_apply]
  exact isIso_kernelComparison_of_universal_model_map F d (E.map (ModuleCat.ofHom A.mulVecLin))
    en.inv em.inv hc (by infer_instance) (by infer_instance)
    (isIso_kernelComparison_of_matrix_split F _ h)

end ZInQ.Contrib.CloudR2Poincare.L1
