import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Algebra.Category.ModuleCat.Sheaf.Coherent.Presentation
import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.IdealData

/-!
Actual canonical Oka coherent modules at the native scheme-module spelling.
No new object model or compatibility premise is introduced: canonical coherence
supplies quasi-coherence and the frozen exact-image ideal constructor is consumed.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

variable {X : Scheme.{u}}

/-- Canonical Oka coherence genuinely supplies native quasi-coherence. -/
theorem coherent_native_isQuasicoherent (M : X.Modules) [M.IsCoherent] : M.IsQuasicoherent :=
  SheafOfModules.IsCoherent.isQuasicoherent M

/-- The native exact-image ideal of an actual coherent module morphism into O_X. -/
def coherentHomIdeal (M : X.Modules) [M.IsCoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) : X.IdealSheafData :=
  letI := coherent_native_isQuasicoherent M
  ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal.idealSheafOfQuasicoherentHom i

/-- Every affine component is the actual section image, not an envelope. -/
theorem coherentHomIdeal_affine_image (M : X.Modules) [M.IsCoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) (U : X.affineOpens) :
    (coherentHomIdeal M i).ideal U =
      ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal.sectionImageIdeal i U.1 := rfl

/-- An actual algebraic closed subscheme with exactly those affine image ideals. -/
theorem coherentHom_exists_closedSubscheme (M : X.Modules) [M.IsCoherent]
    (i : M ⟶ SheafOfModules.unit X.ringCatSheaf) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ X), IsClosedImmersion j ∧
      ∀ U : X.affineOpens, j.ker.ideal U =
        ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal.sectionImageIdeal i U.1 := by
  letI := coherent_native_isQuasicoherent M
  exact ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal.exists_closedSubscheme_of_quasicoherentHom i

end ZInQ.Contrib.CloudB3W17bCanonicalImage
