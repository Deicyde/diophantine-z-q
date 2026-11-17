import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.CoherentNative
import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.RingSheaf
import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.StalkImage

/-!
Actual canonical coherent algebraic module/inclusion consumption into exact
native Scheme.IdealSheafData and its point support. Quasi-coherence is proved
from canonical coherence, not added as a premise to the algebraization target.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

/-- Canonical algebraic coherence supplies canonical quasi-coherence at the real ring sheaf. -/
theorem canonical_coherent_isQuasicoherent (X : Scheme.{u})
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsCoherent] :
    M.IsQuasicoherent := SheafOfModules.IsCoherent.isQuasicoherent M

/-- Exact native ideal from the actual canonical COHERENT module and actual inclusion.
The only hypothesis is actual coherence, which is supplied by GAGA-3. -/
def nativeIdealOfCanonicalCoherentHom (X : Scheme.{u})
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (i : M ⟶ SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) : X.IdealSheafData :=
  letI := canonical_coherent_isQuasicoherent X M
  nativeIdealOfCanonicalHom X M i

/-- Every affine component is exactly the actual canonical inclusion's section image. -/
theorem nativeIdealOfCanonicalCoherentHom_affine_image (X : Scheme.{u})
    (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (i : M ⟶ SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) (U : X.affineOpens) :
    (nativeIdealOfCanonicalCoherentHom X M i).ideal U =
      LinearMap.range (show Γ(M, U.1) →ₗ[Γ(X, U.1)] Γ(X, U.1) from (i.val.app (op U.1)).hom) :=
  rfl

/-- Native J zeros equal non-surjectivity of the ACTUAL canonical stalk inclusion.
No normalization or commuting diagram is assumed; the unit/germ equality was proved. -/
theorem nativeIdealOfCanonicalCoherentHom_mem_support_iff
    (X : Scheme.{u}) (M : SheafOfModules.{u} X.toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (i : M ⟶ SheafOfModules.unit X.toLocallyRingedSpace.ringSheaf) (U : X.affineOpens)
    (x : X) (hx : x ∈ U.1) :
    x ∈ (nativeIdealOfCanonicalCoherentHom X M i).support ↔
      ¬ Function.Surjective ((PresheafOfModules.stalkFunctor (R := X.presheaf) x).map i.val) := by
  haveI := canonical_coherent_isQuasicoherent X M
  let M' : X.Modules := M
  haveI : M'.IsQuasicoherent :=
    inferInstanceAs (SheafOfModules.IsQuasicoherent (R := X.toLocallyRingedSpace.ringSheaf) M)
  exact nativeIdeal_mem_support_iff_not_surjective_canonicalStalk
    (M := M') (show M' ⟶ SheafOfModules.unit X.ringCatSheaf from i) U x hx

end ZInQ.Contrib.CloudB3W17bCanonicalImage
