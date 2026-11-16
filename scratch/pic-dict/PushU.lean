import ZInQKernel.Contrib.OneProof.PicDictionary
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Modules.StructureSheaf

noncomputable section
open CategoryTheory AlgebraicGeometry Opposite Limits

namespace PicDict
open PkgI3 PkgI3.AbVar

/-- **`PushforwardUnitUniversal` is a theorem** (vendored
`isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral`, proper geometrically integral over a field). -/
theorem pushforwardUnitUniversal : PushforwardUnitUniversal := by
  intro K _ A T
  letI : A.X.left.Over (Spec (CommRingCat.of K)) := ⟨A.X.hom⟩
  haveI : IsProper (A.X.left ↘ Spec (CommRingCat.of K)) := inferInstanceAs (IsProper A.X.hom)
  haveI : GeometricallyIntegral (A.X.left ↘ Spec (CommRingCat.of K)) :=
    inferInstanceAs (GeometricallyIntegral A.X.hom)
  exact isIso_pushforwardUnitMap_pullback_snd_of_geometricallyIntegral T

end PicDict

#print axioms PicDict.pushforwardUnitUniversal
