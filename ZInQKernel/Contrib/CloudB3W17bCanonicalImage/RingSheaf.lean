import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules
import ZInQKernel.Contrib.CloudB3W17bGraphScoutReverseIdeal.IdealData

/-!
Actual canonical Oka ring-sheaf spelling compared to the native Mathlib scheme
ring sheaf. The equalities are kernel-checked definitional equalities, not an
identification of different algebraic/analytic spaces or a new object dictionary.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

/-- Oka's actual algebraic ring sheaf on a scheme is the native scheme ring sheaf. -/
theorem canonicalRingSheaf_eq_native (X : Scheme.{u}) :
    X.toLocallyRingedSpace.ringSheaf = X.ringCatSheaf := rfl

/-- The actual unit sheaf has the same native algebraic object, not an invented model. -/
theorem canonicalUnit_eq_native (X : Scheme.{u}) :
    (SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf : X.Modules) =
      SheafOfModules.unit X.ringCatSheaf := rfl

/-- Quasi-coherence crosses the actual ring-sheaf spelling by definitional equality. -/
theorem canonical_quasicoherent_iff_native (X : Scheme.{u})
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) :
    M.IsQuasicoherent ↔ SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf) M := Iff.rfl

/-- Native exact ideal data from an actual canonical algebraic module and actual inclusion.
The quasi-coherence is to be derived from canonical coherence, not added to H-105. -/
def nativeIdealOfCanonicalHom (X : Scheme.{u})
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsQuasicoherent]
    (i : M ⟶ SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) : X.IdealSheafData :=
  let M' : X.Modules := M
  letI : M'.IsQuasicoherent :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.toLocallyRingedSpace.ringSheaf) M)
  ZInQ.Contrib.CloudB3W17bGraphScoutReverseIdeal.idealSheafOfQuasicoherentHom
    (show M' ⟶ SheafOfModules.unit X.ringCatSheaf from i)

/-- Every component is exactly the canonical inclusion's sectionwise linear image. -/
theorem nativeIdealOfCanonicalHom_affine_image (X : Scheme.{u})
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsQuasicoherent]
    (i : M ⟶ SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) (U : X.affineOpens) :
    (nativeIdealOfCanonicalHom X M i).ideal U =
      LinearMap.range (show Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1) from (i.val.app (op U.1)).hom) :=
  rfl

end ZInQ.Contrib.CloudB3W17bCanonicalImage
