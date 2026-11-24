import ZInQKernel.Contrib.CloudB3W17bCanonicalImage.LRSStalkImage
import ZInQKernel.Contrib.CloudB3W17bAnalyticIdeal.InverseImageLocus

/-!
Actual pullback support comparison for the native ideal constructed from a
coherent algebraic inclusion. This consumes the real canonical pullback-stalk
naturality proof and actual unit equivalence from the function lane; no diagram
premise is introduced. Instantiating p with analytification's comparison morphism
is deferred until the real canonical GAGA roots compile.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

noncomputable section
universe u

namespace ZInQ.Contrib.CloudB3W17bCanonicalImage

/-- Native J support pulls back to the actual non-surjectivity locus of the real
pullback module morphism, with no extra unit-stalk or comparison premise. -/
theorem nativeIdeal_pullback_support_eq
    (Y : Scheme.{u}) (M : SheafOfModules.{u} Y.toLocallyRingedSpace.ringSheaf) [M.IsCoherent]
    (i : M ⟶ SheafOfModules.unit Y.toLocallyRingedSpace.ringSheaf)
    (X : LocallyRingedSpace.{u}) (p : X ⟶ Y.toLocallyRingedSpace) :
    p.base ⁻¹' ((nativeIdealOfCanonicalCoherentHom Y M i).support : Set Y) =
      ZInQ.Contrib.CloudB3W17bAnalyticIdeal.vanishingLocus
        (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.invImageMap p i) := by
  ext x
  obtain ⟨U, hU⟩ : ∃ U : Y.affineOpens, p.base x ∈ U.1 :=
    Opens.mem_iSup.mp (by rw [iSup_affineOpens_eq_top]; trivial)
  change p.base x ∈ (nativeIdealOfCanonicalCoherentHom Y M i).support ↔ _
  rw [nativeIdealOfCanonicalCoherentHom_mem_support_iff_LRS Y M i U (p.base x) hU]
  exact (not_congr
    (ZInQ.Contrib.CloudB3W17bAnalyticIdeal.surjective_stalk_invImageMap_iff_stalk p i x)).symm

end ZInQ.Contrib.CloudB3W17bCanonicalImage
