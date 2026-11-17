import ZInQKernel.Contrib.CloudR2Poincare.L1.FieldFibreSections
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.DirectImage.CechBaseChange

/-! Actual scalar extensions of the original Čech zero kernel have dimension
one on every field-valued test when all actual residue fibres are trivial.
This is dimension information, derived through true Čech base change; it
assumes no preservation of the canonical zero kernel comparison. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2Poincare.L1

/-- The kernel of d0 of an extended Nat complex is canonically the original d0 kernel. -/
def extendZeroKernelIso {C : Type*} [Category* C] [Abelian C]
    (F : C ⥤ C) [F.PreservesZeroMorphisms] (K : CochainComplex C ℕ) :
    kernel (F.map ((K.extend ComplexShape.embeddingUpNat).d 0 1)) ≅
      kernel (F.map (K.d 0 1)) := by
  let e0 := K.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl
  let e1 := K.extendXIso ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl
  have h : (K.extend ComplexShape.embeddingUpNat).d 0 1 ≫ e1.hom = e0.hom ≫ K.d 0 1 := by
    rw [K.extend_d_eq ComplexShape.embeddingUpNat (i := 0) (j := 1)
      (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
    simp only [e0, e1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact kernel.mapIso _ _ (F.mapIso e0) (F.mapIso e1)
    (by simp only [Functor.mapIso_hom]; rw [← F.map_comp, ← F.map_comp, h])

/-- The actual original module-valued Čech complex has zero-kernel dimension
one after each field-valued scalar extension. -/
theorem finrank_scalarCech_zeroKernel_field_eq_one
    {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) [IsProper f] [GeometricallyIntegral f]
    (M : X.Modules) [M.IsInvertible]
    (hM : ∀ y : Y, Scheme.Pic.map (f.fiberι y) (Scheme.Pic.mk M) = 1)
    {ι : Type u} [Finite ι] (U : ι → X.Opens) (hcover : ⨆ i, U i = ⊤)
    (hU : ∀ (q : ℕ) (t : Fin (q + 1) → ι), IsAffineOpen (⨅ l, U (t l)))
    (K : Type u) [Field K] (g : Spec (.of K) ⟶ Y)
    [Algebra Γ(Y, ⊤) Γ(Spec (.of K), ⊤)]
    (hg : algebraMap Γ(Y, ⊤) Γ(Spec (.of K), ⊤) = g.appTop.hom) :
    Module.finrank Γ(Spec (.of K), ⊤)
      (kernel ((ModuleCat.extendScalars (algebraMap Γ(Y, ⊤) Γ(Spec (.of K), ⊤))).map
        ((Scheme.Modules.cechModuleComplex f M U).d 0 1)) : ModuleCat.{u} Γ(Spec (.of K), ⊤)) = 1 := by
  let F := ModuleCat.extendScalars (algebraMap Γ(Y, ⊤) Γ(Spec (.of K), ⊤))
  let C := Scheme.Modules.cechModuleComplexNat f M U
  let D := Scheme.Modules.cechModuleComplexNat (pullback.snd f g)
    ((Scheme.Modules.pullback (pullback.fst f g)).obj M) (fun i ↦ (pullback.fst f g) ⁻¹ᵁ U i)
  let e0 := C.extendXIso ComplexShape.embeddingUpNat (i := 0) (i' := (0 : ℤ)) rfl
  let e1 := C.extendXIso ComplexShape.embeddingUpNat (i := 1) (i' := (1 : ℤ)) rfl
  have h : (C.extend ComplexShape.embeddingUpNat).d 0 1 ≫ e1.hom = e0.hom ≫ C.d 0 1 := by
    rw [C.extend_d_eq ComplexShape.embeddingUpNat (i := 0) (j := 1)
      (i' := (0 : ℤ)) (j' := (1 : ℤ)) rfl rfl]
    simp only [e0, e1, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  let k0 := kernel.mapIso (F.map ((C.extend ComplexShape.embeddingUpNat).d 0 1))
    (F.map (C.d 0 1)) (F.mapIso e0) (F.mapIso e1)
    (by simp only [Functor.mapIso_hom]; rw [← F.map_comp, ← F.map_comp, h])
  let ec := Scheme.Modules.cechModuleComplexNatBaseChangeIso (IsPullback.of_hasPullback f g) M hg U hU
  let k1 := kernel.mapIso (F.map (C.d 0 1)) (D.d 0 1)
    (asIso (ec.hom.f 0)) (asIso (ec.hom.f 1)) (ec.hom.comm 0 1).symm
  exact (k0 ≪≫ k1).toLinearEquiv.finrank_eq.trans
    (finrank_cechKernel_fieldBaseChange_eq_one f M hM K g U hcover)

end ZInQ.Contrib.CloudR2Poincare.L1
