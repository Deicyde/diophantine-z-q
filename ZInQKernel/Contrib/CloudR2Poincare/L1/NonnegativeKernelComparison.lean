import ZInQKernel.Contrib.CloudR2Poincare.L1.UniversalKernelComparison

/-! Canonical degree-zero kernels for actual nonnegative INTEGER-indexed
models. This retains the actual map before and after scalar extension;
it does not use an arbitrarily chosen H0 object isomorphism. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits

namespace ZInQ.Contrib.CloudR2Poincare.L1

@[simps]
def cyclesKernelZeroIntIso {C : Type*} [Category* C] [Abelian C]
    (K : CochainComplex C ℤ) : K.cycles 0 ≅ kernel (K.d 0 1) where
  hom := kernel.lift (K.d 0 1) (K.iCycles 0) (K.iCycles_d 0 1)
  inv := K.liftCycles (kernel.ι (K.d 0 1)) 1 (by simp) (kernel.condition _)
  hom_inv_id := by
    apply (cancel_mono (K.iCycles 0)).mp
    simp only [Category.assoc, HomologicalComplex.liftCycles_i, kernel.lift_ι, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (kernel.ι (K.d 0 1))).mp
    simp only [Category.assoc, kernel.lift_ι, HomologicalComplex.liftCycles_i, Category.id_comp]

/-- An actual quasi-isomorphism induces an isomorphism on d0 kernels when
both integer complexes have a zero negative term. -/
theorem isIso_kernelMap_zeroInt_of_quasiIso
    {C : Type*} [Category* C] [Abelian C]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ]
    (hK : IsZero (K.X (-1))) (hL : IsZero (L.X (-1))) :
    IsIso (kernel.map (K.d 0 1) (L.d 0 1) (φ.f 0) (φ.f 1) (φ.comm 0 1).symm) := by
  haveI : IsIso (K.homologyπ 0) := K.isIso_homologyπ (-1) 0 (by simp) (hK.eq_of_src _ _)
  haveI : IsIso (L.homologyπ 0) := L.isIso_homologyπ (-1) 0 (by simp) (hL.eq_of_src _ _)
  haveI : IsIso (HomologicalComplex.homologyMap φ 0) := inferInstance
  have hc := HomologicalComplex.homologyπ_naturality φ 0
  haveI : IsIso (HomologicalComplex.cyclesMap φ 0 ≫ L.homologyπ 0) := by
    rw [← hc]
    infer_instance
  haveI : IsIso (HomologicalComplex.cyclesMap φ 0) :=
    IsIso.of_isIso_comp_right _ (L.homologyπ 0)
  let eK := cyclesKernelZeroIntIso K
  let eL := cyclesKernelZeroIntIso L
  have h : eK.hom ≫ kernel.map (K.d 0 1) (L.d 0 1) (φ.f 0) (φ.f 1) (φ.comm 0 1).symm =
      HomologicalComplex.cyclesMap φ 0 ≫ eL.hom := by
    apply (cancel_mono (kernel.ι (L.d 0 1))).mp
    simp only [Category.assoc, kernel.map, kernel.lift_ι, kernel.lift_ι_assoc,
      eK, eL, cyclesKernelZeroIntIso_hom]
    exact (HomologicalComplex.cyclesMap_i φ 0).symm
  haveI : IsIso (eK.hom ≫ kernel.map (K.d 0 1) (L.d 0 1) (φ.f 0) (φ.f 1) (φ.comm 0 1).symm) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_left eK.hom _

/-- Transport canonical kernel preservation along an ACTUAL universal
nonnegative model map, using its actual quasi-isomorphism on both sides. -/
theorem isIso_kernelComparison_of_universal_nonnegative_map
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.PreservesZeroMorphisms]
    {K L : CochainComplex C ℤ} (φ : K ⟶ L) [QuasiIso φ]
    [QuasiIso ((F.mapHomologicalComplex _).map φ)]
    (hK : IsZero (K.X (-1))) (hL : IsZero (L.X (-1)))
    (hF : IsIso (kernelComparison (K.d 0 1) F)) :
    IsIso (kernelComparison (L.d 0 1) F) := by
  have ha := isIso_kernelMap_zeroInt_of_quasiIso φ hK hL
  have hb := isIso_kernelMap_zeroInt_of_quasiIso ((F.mapHomologicalComplex _).map φ)
    (F.map_isZero hK) (F.map_isZero hL)
  exact isIso_kernelComparison_of_universal_model_map F (K.d 0 1) (L.d 0 1)
    (φ.f 0) (φ.f 1) (φ.comm 0 1).symm ha hb hF

end ZInQ.Contrib.CloudR2Poincare.L1
