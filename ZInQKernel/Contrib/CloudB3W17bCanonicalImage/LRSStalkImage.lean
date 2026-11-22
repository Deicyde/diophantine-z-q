import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.CanonicalCoherent
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.AnalyticSpace.PullbackModulesStalk

/-!
Consume the actual canonical locally-ringed-space stalk functor, with no new
stalk model: its object and morphism are the existing canonical presheaf stalk.
The function lane's proven unit equivalence therefore applies to the real object.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

/-- Actual canonical LRS unit stalk is identified with its ring by the proved PM equivalence. -/
def canonical_unitStalkEquivLRS (Y : LocallyRingedSpace.{u}) (y : Y) :
    (Y.stalkFunctor y).obj (SheafOfModules.unit Y.ringSheaf) ≃ₗ[Y.presheaf.stalk y]
      Y.presheaf.stalk y :=
  ZInQ.Contrib.CloudB3W17bAnalyticIdeal.PM.unitStalkEquiv Y.presheaf y

/-- The real canonical LRS stalk map is exactly its existing presheaf stalk map. -/
theorem canonicalLRS_stalkMap_eq (X : Scheme.{u})
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf)
    (i : M ⟶ SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) (x : X) :
    ((X.toLocallyRingedSpace.stalkFunctor x).map i).hom =
      ((PresheafOfModules.stalkFunctor (R := X.presheaf) x).map i.val).hom := rfl

/-- Exact native ideal support versus non-surjectivity of its actual canonical LRS stalk. -/
theorem nativeIdealOfCanonicalCoherentHom_mem_support_iff_LRS
    (X : Scheme.{u}) (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (i : M ⟶ SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) (U : X.affineOpens)
    (x : X) (hx : x ∈ U.1) :
    x ∈ (nativeIdealOfCanonicalCoherentHom X M i).support ↔
      ¬ Function.Surjective ((X.toLocallyRingedSpace.stalkFunctor x).map i) := by
  exact nativeIdealOfCanonicalCoherentHom_mem_support_iff X M i U x hx

end ZInQ.Contrib.CloudB3W17bCanonicalImage
