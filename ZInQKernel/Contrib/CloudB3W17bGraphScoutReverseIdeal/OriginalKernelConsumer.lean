import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.ComplexKernelConsumer
import ZInQKernel.Contrib.CloudB3W17Hodge.Bridge

/-!
# Original complex-point consumers of the exact native reduced closed kernel

Use the already proved Hodge ptIso/cptEquiv, whose underlying scheme map is
literally identity. This does not introduce a new point model or dictionary.
Kernel and graph support formulas must be supplied by the actual GAGA extraction,
not a replacement algebraic-map or graph premise in the final H-105 theorem.
-/

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace
open PkgI3 (AbVar)
open ZInQ.LeafPush2 (CPts cptObj)

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section
namespace ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal

/-- Precomposition with the EXISTING actual identity-on-schemes ptIso transports
native points to the unchanged original carrier and respects its group law. -/
def schemePointToOriginalHom (P : Over (Spec (.of ℂ))) [GrpObj P] :
    SchemeCPoints P →* CloudB3W17Hodge.CPt P where
  toFun u := CloudB3W17Hodge.ptIso.hom ≫ u
  map_one' := by rw [MonObj.comp_one]
  map_mul' u v := by rw [MonObj.comp_mul]

/-- Original point membership in the exact reduced closed native support is equivalent
to an actual lift from the SAME original source point object. -/
theorem originalPoint_mem_iff_lift_reducedClosed
    (P : Over (Spec (.of ℂ))) (Z : Closeds P.left) (u : CloudB3W17Hodge.CPt P) :
    u.left (IsLocalRing.closedPoint ℂ) ∈ Z ↔
      ∃ t : CloudB3W17Hodge.CPt (reducedClosedOver P Z), t ≫ reducedClosedι P Z = u := by
  constructor
  · intro hu
    have hn : (CloudB3W17Hodge.cptEquiv P u).left (IsLocalRing.closedPoint ℂ) ∈ Z := hu
    obtain ⟨t, ht⟩ := (complexPoint_mem_iff_lift_reducedClosed P Z _).mp hn
    refine ⟨CloudB3W17Hodge.ptIso.hom ≫ t, ?_⟩
    rw [Category.assoc, ht]
    change CloudB3W17Hodge.ptIso.hom ≫ CloudB3W17Hodge.ptIso.inv ≫ u = u
    simp
  · rintro ⟨t, ht⟩
    have he := congrArg (fun q : CloudB3W17Hodge.CPt P => q.left (IsLocalRing.closedPoint ℂ)) ht
    change (reducedClosedι P Z).left (t.left (IsLocalRing.closedPoint ℂ)) = _ at he
    rw [← he]
    exact reducedClosedι_apply_mem P Z _

/-- Construct the exact closed-kernel group from a homomorphism on ORIGINAL points.
No kernel group or reduced self-product is assumed; PR41 is consumed internally. -/
@[reducible] def reducedClosedOriginalKernelGrp
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : Closeds P.left)
    {K : Type*} [Group K] (H : CloudB3W17Hodge.CPt P →* K)
    (hker : ∀ u : CloudB3W17Hodge.CPt P, H u = 1 ↔ u.left (IsLocalRing.closedPoint ℂ) ∈ Z) :
    GrpObj (reducedClosedOver P Z) :=
  reducedClosedSupportKernelGrpOfComplex P Z (H.comp (schemePointToOriginalHom P))
    (fun u => hker (CloudB3W17Hodge.ptIso.hom ≫ u))

/-- The actual inclusion is a homomorphism for the constructed original-kernel group. -/
theorem isMonHom_reducedClosedOriginalKernelGrp
    (P : Over (Spec (.of ℂ))) [GrpObj P] [LocallyOfFiniteType P.hom] (Z : Closeds P.left)
    {K : Type*} [Group K] (H : CloudB3W17Hodge.CPt P →* K)
    (hker : ∀ u : CloudB3W17Hodge.CPt P, H u = 1 ↔ u.left (IsLocalRing.closedPoint ℂ) ∈ Z) :
    letI := reducedClosedOriginalKernelGrp P Z H hker
    IsMonHom (reducedClosedι P Z) :=
  isMonHom_reducedClosedSupportKernelGrpOfComplex P Z (H.comp (schemePointToOriginalHom P))
    (fun u => hker (CloudB3W17Hodge.ptIso.hom ≫ u))

end ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal
