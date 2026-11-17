import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.ReducedClosedKernel
import ZInQKernel.Contrib.CloudB3W17bGraphScout.AlgebraicGraphTail
import ZInQKernel.Contrib.CloudB3W17bReduced.ComplexProduct

/-!
Consume the published PR41 reduced-product theorem on the exact native reduced
closed over-object. Group structure and the inclusion homomorphism are constructed;
no reduced-product, smoothness, or group-structure premise on the kernel is added.
The final realization consumer still requires the actual point-kernel support and
original-carrier graph formulas; it does not close H-105 without their GAGA supplier.
-/

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cptObj)

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

/-- Actual native reduced closed kernel group, consuming PR41 rather than assuming
reducedness of its self-product. -/
@[reducible] def reducedClosedSupportKernelGrpOfComplex
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : TopologicalSpace.Closeds P.left)
    {K : Type*} [Group K] (H : SchemeCPoints P →* K)
    (hker : ∀ u : SchemeCPoints P, H u = 1 ↔ u.left (IsLocalRing.closedPoint ℂ) ∈ Z) :
    GrpObj (reducedClosedOver P Z) :=
  letI := ZInQ.Contrib.CloudB3W17bReduced.isReduced_complex_tensor
    (reducedClosedOver P Z) (reducedClosedOver P Z)
  reducedClosedSupportKernelGrp P Z H hker

/-- The same actual closed inclusion is a homomorphism for the constructed group. -/
theorem isMonHom_reducedClosedSupportKernelGrpOfComplex
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : TopologicalSpace.Closeds P.left)
    {K : Type*} [Group K] (H : SchemeCPoints P →* K)
    (hker : ∀ u : SchemeCPoints P, H u = 1 ↔ u.left (IsLocalRing.closedPoint ℂ) ∈ Z) :
    letI := reducedClosedSupportKernelGrpOfComplex P Z H hker
    IsMonHom (reducedClosedι P Z) := by
  letI := ZInQ.Contrib.CloudB3W17bReduced.isReduced_complex_tensor
    (reducedClosedOver P Z) (reducedClosedOver P Z)
  exact isMonHom_reducedClosedSupportKernelGrp P Z H hker

/-- Original-carrier graph realization from the exact reduced closed native kernel.
Both missing point formulas remain explicit; no GAGA or analytic model is assumed. -/
theorem exists_scheme_realization_of_reduced_closed_kernel_graph
    (A B : AbVar ℂ) (F : CPts A (RingHom.id ℂ) →* CPts B (RingHom.id ℂ))
    (Z : TopologicalSpace.Closeds (A.X ⊗ B.X).left)
    {K : Type*} [Group K] (H : SchemeCPoints (A.X ⊗ B.X) →* K)
    (hker : ∀ u : SchemeCPoints (A.X ⊗ B.X),
      H u = 1 ↔ u.left (IsLocalRing.closedPoint ℂ) ∈ Z)
    (hgraph : ∀ (P : CPts A (RingHom.id ℂ)) (Q : CPts B (RingHom.id ℂ)),
      F P = Q ↔ ∃ t : cptObj (RingHom.id ℂ) ⟶ reducedClosedOver (A.X ⊗ B.X) Z,
        t ≫ (reducedClosedι (A.X ⊗ B.X) Z ≫ fst A.X B.X) = P ∧
        t ≫ (reducedClosedι (A.X ⊗ B.X) Z ≫ snd A.X B.X) = Q) :
    ∃ f : A.X ⟶ B.X, ∀ P : CPts A (RingHom.id ℂ), F P = P ≫ f := by
  haveI : LocallyOfFiniteType (A.X ⊗ B.X).hom := by
    change LocallyOfFiniteType (pullback.fst A.X.hom B.X.hom ≫ A.X.hom)
    infer_instance
  letI := reducedClosedSupportKernelGrpOfComplex (A.X ⊗ B.X) Z H hker
  letI := isMonHom_reducedClosedSupportKernelGrpOfComplex (A.X ⊗ B.X) Z H hker
  exact ZInQ.Contrib.CloudB3W17bGraphScout.exists_scheme_realization_of_concrete_algebraic_graph
    A B F (reducedClosedOver (A.X ⊗ B.X) Z) (reducedClosedι (A.X ⊗ B.X) Z) hgraph

end ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal
