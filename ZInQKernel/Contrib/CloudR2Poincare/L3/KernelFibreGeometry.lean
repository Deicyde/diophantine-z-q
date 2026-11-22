import ZInQKernel.Contrib.CloudR2Poincare.L3.KernelGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L4.ProductGeometry
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# The actual fibre of a homomorphism over its rational unit

Reuse credit: L4's proved rationalPointResidueIso and its compatibility with the
closed rational section. The fibre is identified SCHEME-THEORETICALLY with L3's
pullback kernel, not merely by a homeomorphism. This makes local-ring regularity
and the quotient-stalk bridge composable without a fibre-dimension axiom.
-/

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances

set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

section Fibre
#cloudR2LocalInstances
variable {k : Type} [Field k] {A B : _root_.PkgI3.AbVar k} (h : A.X ⟶ B.X) [IsMonHom h]

/-- The composite of the source unit with h is exactly the target unit section. -/
theorem sourceUnit_comp : (η[A.X]).left ≫ h.left = (η[B.X]).left := by
  exact congrArg Over.Hom.left (IsMonHom.one_hom h)

/-- The actual h-fibre through the rational source unit is the pullback kernel. -/
noncomputable def kernelUnitFibreIso (x : Spec (.of k)) :
    h.left.fiber (h.left ((η[A.X]).left x)) ≅ (kerOver h).left := by
  let i : Spec (.of k) ⟶ B.X.left := (η[A.X]).left ≫ h.left
  have hi : i = (η[B.X]).left := sourceUnit_comp h
  haveI : IsClosedImmersion i := by rw [hi]; infer_instance
  let e := ZInQ.Contrib.CloudR2Poincare.L4.rationalPointResidueIso i x
  let m := pullback.map h.left (B.X.left.fromSpecResidueField (i x))
    h.left i (𝟙 A.X.left) e.hom (𝟙 B.X.left)
    (by simp) (by simpa using (ZInQ.Contrib.CloudR2Poincare.L4.rationalPointResidueIso_hom_i i x).symm)
  haveI hm : IsIso m := pullback.map_isIso _ _ _ _ _ _ _ _ _
  change pullback h.left (B.X.left.fromSpecResidueField (i x)) ≅ _
  exact asIso m ≪≫ pullback.congrHom rfl hi

@[reassoc]
theorem kernelUnitFibreIso_hom (x : Spec (.of k)) :
    (kernelUnitFibreIso h x).hom ≫ (kerι h).left =
      h.left.fiberι (h.left ((η[A.X]).left x)) := by
  simp [kernelUnitFibreIso, pullback.map, pullback.congrHom, kerι, Scheme.Hom.fiberι]

/-- The kernel unit maps to the source unit. -/
theorem ker_unit_point (x : Spec (.of k)) :
    (kerι h).left ((η[kerOver h]).left x) = (η[A.X]).left x := by
  have H := congrArg Over.Hom.left (IsMonHom.one_hom (kerι h))
  simp only [Over.comp_left] at H
  simpa only [Scheme.Hom.comp_apply] using congrArg (fun f => f x) H

/-- The distinguished ePt is the unit section evaluated at any point of Spec k. -/
theorem ePt_eq_unit (x : Spec (.of k)) : ePt h = (η[kerOver h]).left x := by
  unfold ePt
  congr 1
  exact Subsingleton.elim _ _

/-- The fibre point through the source unit is carried to the kernel's unit point. -/
theorem kernelUnitFibreIso_point (x : Spec (.of k)) :
    (kernelUnitFibreIso h x).hom (h.left.asFiber ((η[A.X]).left x)) = ePt h := by
  apply (kerι h).left.isClosedEmbedding.injective
  calc
    (kerι h).left ((kernelUnitFibreIso h x).hom (h.left.asFiber ((η[A.X]).left x))) =
        (h.left.fiberι _ ≫ 𝟙 A.X.left) (h.left.asFiber ((η[A.X]).left x)) := by
      rw [← Scheme.Hom.comp_apply, kernelUnitFibreIso_hom, Category.comp_id]
    _ = (η[A.X]).left x := by simp
    _ = (kerι h).left (ePt h) := by rw [ePt_eq_unit h x, ker_unit_point]

end Fibre
end ZInQ.Contrib.CloudR2Poincare.L3
