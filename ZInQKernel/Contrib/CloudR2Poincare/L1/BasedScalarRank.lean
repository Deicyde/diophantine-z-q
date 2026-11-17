import ZInQKernel.Contrib.CloudR2Poincare.L1.ReducedScalarKernel
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Scalar-extended basis coordinates identify the actual model d0 kernel
with the kernel of its scalar-mapped matrix. Rank-nullity is proved in the
actual field module, without equating sheaf and ring scalar comparisons. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry
open scoped Matrix

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- Matrix rank is unchanged by an actual field embedding, by the nonzero-minor criterion. -/
theorem rank_map_field_embedding {K L : Type u} [Field K] [Field L]
    {m n : Type u} [Fintype m] [Fintype n] (A : Matrix m n K) (ψ : K →+* L) :
    (A.map ψ).rank = A.rank := by
  apply le_antisymm
  · obtain ⟨rows, cols, h⟩ := Matrix.exists_submatrix_det_ne_zero_of_le_rank (A.map ψ) le_rfl
    have h' : (A.submatrix rows cols).det ≠ 0 := by
      intro hz
      rw [Matrix.submatrix_map, ← RingHom.mapMatrix_apply, ← RingHom.map_det, hz, map_zero] at h
      exact h rfl
    exact Matrix.le_rank_of_submatrix_det_ne_zero A rows cols h'
  · obtain ⟨rows, cols, h⟩ := Matrix.exists_submatrix_det_ne_zero_of_le_rank A le_rfl
    exact (Matrix.le_rank_map_iff A ψ A.rank).mpr
      ⟨rows, cols, fun hz ↦ h (ψ.injective (hz.trans (map_zero ψ).symm))⟩

/-- An actual morphism is its actual matrix in chosen basis coordinates. -/
theorem based_morphism_matrix_square
    {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
    {m n : Type u} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (bm : Module.Basis n R M) (bn : Module.Basis m R N) (d : M ⟶ N) :
    d ≫ bn.equivFun.toModuleIso.hom = bm.equivFun.toModuleIso.hom ≫
      ModuleCat.ofHom (LinearMap.toMatrix bm bn d.hom).mulVecLin := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (LinearMap.toMatrix_mulVec_repr bm bn d.hom x).symm

/-- Rank-nullity for the ACTUAL scalar-extended differential in its original basis. -/
theorem scalar_matrix_rank_add_kernel_finrank
    (R K : Type u) [CommRing R] [Field K] [Algebra R K]
    {M N : ModuleCat.{u} R} {m n : Type u} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (bm : Module.Basis n R M) (bn : Module.Basis m R N) (d : M ⟶ N) :
    ((LinearMap.toMatrix bm bn d.hom).map (algebraMap R K)).rank +
      Module.finrank K (kernel ((ModuleCat.extendScalars (algebraMap R K)).map d) : ModuleCat.{u} K) =
      Fintype.card n := by
  let F := ModuleCat.extendScalars (algebraMap R K)
  let A := LinearMap.toMatrix bm bn d.hom
  let a : ModuleCat.of R (n → R) ⟶ ModuleCat.of R (m → R) := ModuleCat.ofHom A.mulVecLin
  let aK : ModuleCat.of K (n → K) ⟶ ModuleCat.of K (m → K) := ModuleCat.ofHom (A.map (algebraMap R K)).mulVecLin
  let eM := bm.equivFun.toModuleIso
  let eN := bn.equivFun.toModuleIso
  let cn := (extendScalarsCoordinates R K n).toModuleIso
  let cm := (extendScalarsCoordinates R K m).toModuleIso
  have hb : d ≫ eN.hom = eM.hom ≫ a := based_morphism_matrix_square bm bn d
  have hc : F.map a ≫ cm.hom = cn.hom ≫ aK := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact extendScalarsCoordinates_matrix R K A x
  have h : F.map d ≫ (F.mapIso eN ≪≫ cm).hom = (F.mapIso eM ≪≫ cn).hom ≫ aK := by
    simp only [Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← F.map_comp, hb, F.map_comp, Category.assoc, hc]
    simp only [Category.assoc]
  let iso := kernel.mapIso (F.map d) aK (F.mapIso eM ≪≫ cn) (F.mapIso eN ≪≫ cm) h ≪≫
    ModuleCat.kernelIsoKer aK
  have hk : Module.finrank K (kernel (F.map d) : ModuleCat.{u} K) = Module.finrank K (LinearMap.ker aK.hom) :=
    iso.toLinearEquiv.finrank_eq
  have hn := (A.map (algebraMap R K)).mulVecLin.finrank_range_add_finrank_ker
  rw [Module.finrank_fintype_fun_eq_card] at hn
  rw [hk]
  exact hn

/-- Constant rank-one scalar kernels give the actual canonical scalar
kernelComparison isomorphism for a finite-free differential over a reduced ring. -/
theorem isIso_based_kernelComparison_of_field_kernel_rank_one
    (R : Type u) [CommRing R] [_root_.IsReduced R]
    {M N : ModuleCat.{u} R} {m n : Type u} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (bm : Module.Basis n R M) (bn : Module.Basis m R N) (d : M ⟶ N)
    (h : ∀ (K : Type u) [Field K] (ψ : R →+* K),
      Module.finrank K (kernel ((ModuleCat.extendScalars ψ).map d) : ModuleCat.{u} K) = 1)
    (K : Type u) [Field K] (ψ : R →+* K) :
    IsIso (kernelComparison d (ModuleCat.extendScalars ψ)) := by
  let A := LinearMap.toMatrix bm bn d.hom
  have hr : ∀ (B : Type u) [Field B] (β : R →+* B), (A.map β).rank = Fintype.card n - 1 := by
    intro B _ β
    letI : Algebra R B := β.toAlgebra
    have hh := scalar_matrix_rank_add_kernel_finrank R B bm bn d
    change (A.map β).rank + Module.finrank B (kernel ((ModuleCat.extendScalars β).map d) : ModuleCat.{u} B) =
      Fintype.card n at hh
    rw [h B β] at hh
    omega
  let F := ModuleCat.extendScalars ψ
  let a : ModuleCat.of R (n → R) ⟶ ModuleCat.of R (m → R) := ModuleCat.ofHom A.mulVecLin
  let eM := bm.equivFun.toModuleIso
  let eN := bn.equivFun.toModuleIso
  have hs : d ≫ eN.hom = eM.hom ≫ a := based_morphism_matrix_square bm bn d
  have hc : a ≫ eN.inv = eM.inv ≫ d := by
    apply (cancel_mono eN.hom).mp
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hs, Iso.inv_hom_id_assoc]
  exact isIso_kernelComparison_of_universal_model_map F a d eM.inv eN.inv hc
    (by infer_instance) (by infer_instance)
    (isIso_matrix_kernelComparison_of_constant_fieldRank R A (Fintype.card n - 1) hr K ψ)

end ZInQ.Contrib.CloudR2Poincare.L1
