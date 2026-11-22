import ZInQKernel.Contrib.CloudR2Poincare.Skeleton
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Cohomology.Isomorphism
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Tensor
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.Invertible

/-!
# C1: actual shear isomorphism and cohomology comparison

The shear (x,y) -> (x,xy) is an actual isomorphism of group-object products.
For a line bundle whose multiplication pullback is the actual tensor of its
two projection pullbacks, the two coefficient objects N external-tensor N
and O external-tensor N have equal native cohomology ranks in every degree.
No Kunneth identity or Picard-zero vanishing is assumed in this theorem.
The multiplicative bundle isomorphism is an ordinary concrete argument;
C1MultiplicativeSeesaw derives it from translation invariance and ONE named
existing normalized-seesaw input.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option linter.style.haveILetI false

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped AlgebraicGeometry.Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L5

section Category

variable {C : Type*} [Category* C] [CartesianMonoidalCategory C]

/-- The literal product shear; its inverse is (x,y) -> (x,x^{-1}y).
No abelian-variety complement or retraction is assumed. -/
def productSumShear (B : C) [GrpObj B] : B ⊗ B ≅ B ⊗ B where
  hom := lift (fst B B) (fst B B * snd B B)
  inv := lift (fst B B) ((fst B B)⁻¹ * snd B B)
  hom_inv_id := by
    ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv, ← mul_assoc]
  inv_hom_id := by
    ext <;> simp [MonObj.comp_mul, GrpObj.comp_inv, ← mul_assoc]

@[reassoc (attr := simp)]
theorem productSumShear_hom_fst (B : C) [GrpObj B] :
    (productSumShear B).hom ≫ fst B B = fst B B := by simp [productSumShear]

@[reassoc (attr := simp)]
theorem productSumShear_hom_snd (B : C) [GrpObj B] :
    (productSumShear B).hom ≫ snd B B = μ[B] := by
  simp [productSumShear, CategoryTheory.Hom.mul_def]

end Category

universe u

/-- The actual native all-degree rank comparison of N external-tensor N and
O external-tensor N via the shear. No product Kunneth statement is an input. -/
theorem native_product_rank_eq_of_multiplicative_pullback
    {k : Type u} [Field k] (B : PkgI3.AbVar k)
    (N : B.X.left.Modules)
    (multiplicative : Nonempty ((Scheme.Modules.pullback μ[B.X].left).obj N ≅
      (Scheme.Modules.pullback (fst B.X B.X).left).obj N ⊗
        (Scheme.Modules.pullback (snd B.X B.X).left).obj N)) (q : ℕ) :
    letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
    ((Scheme.Modules.pullback (fst B.X B.X).left).obj N ⊗
      (Scheme.Modules.pullback (snd B.X B.X).left).obj N).finrankH k q =
    ((Scheme.Modules.pullback (fst B.X B.X).left).obj
        (SheafOfModules.unit B.X.left.ringCatSheaf) ⊗
      (Scheme.Modules.pullback (snd B.X B.X).left).obj N).finrankH k q := by
  letI : (B.X ⊗ B.X).left.Over (Spec (.of k)) := ⟨(B.X ⊗ B.X).hom⟩
  let e := productSumShear B.X
  let p := (fst B.X B.X).left
  let r := (snd B.X B.X).left
  let F := (Scheme.Modules.pullback r).obj N
  haveI : IsIso e.hom.left := inferInstanceAs
    (IsIso ((Over.forget (Spec (.of k))).map e.hom))
  have composite : e.hom.left ≫ r = μ[B.X].left := by
    rw [← Over.comp_left]
    exact congrArg Over.Hom.left (productSumShear_hom_snd B.X)
  let pullbackComparison : (Scheme.Modules.pullback e.hom.left).obj F ≅
      (Scheme.Modules.pullback μ[B.X].left).obj N :=
    (Scheme.Modules.pullbackComp e.hom.left r).app N ≪≫
      (Scheme.Modules.pullbackCongr composite).app N
  let unitComparison :
      (Scheme.Modules.pullback p).obj (SheafOfModules.unit B.X.left.ringCatSheaf) ⊗ F ≅ F :=
    (tensorRight F).mapIso (Scheme.Modules.pullbackObjUnitIso p) ≪≫ λ_ F
  have shearRank : ((Scheme.Modules.pullback e.hom.left).obj F).finrankH k q = F.finrankH k q := by
    have heOver : e.hom.left ≫ (B.X ⊗ B.X).hom = (B.X ⊗ B.X).hom := Over.w e.hom
    have h := Scheme.Modules.finrankH_pullback_of_isIso
      e.hom.left (B.X ⊗ B.X).hom F q
    rw [heOver] at h
    exact h
  obtain ⟨multiplicativeIso⟩ := multiplicative
  calc
    _ = ((Scheme.Modules.pullback μ[B.X].left).obj N).finrankH k q :=
      Scheme.Modules.finrankH_congr k multiplicativeIso.symm q
    _ = ((Scheme.Modules.pullback e.hom.left).obj F).finrankH k q :=
      Scheme.Modules.finrankH_congr k pullbackComparison.symm q
    _ = F.finrankH k q := shearRank
    _ = _ := (Scheme.Modules.finrankH_congr k unitComparison q).symm

end ZInQ.Contrib.CloudR2Poincare.L5
