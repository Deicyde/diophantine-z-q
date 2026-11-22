import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-! Scheme-level spelling of Mathlib's actual `SheafOfModules.pullbackObjFreeIso`.
The Stacks source calls `Scheme.Modules.pullbackFreeIso`, absent at the fixed
Mathlib pin; this adapter proves the unchanged interface, rather than assuming it.
-/

open CategoryTheory AlgebraicGeometry TopologicalSpace

namespace ZInQ.Contrib.CloudR2Poincare.L3
#cloudR2LocalInstances

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def pullbackFreeIso {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Type u) :
    (Scheme.Modules.pullback f).obj
        (SheafOfModules.free (R := Y.ringCatSheaf) I) ≅
      SheafOfModules.free (R := X.ringCatSheaf) I :=
  SheafOfModules.pullbackObjFreeIso f.toRingCatSheafHom I

end ZInQ.Contrib.CloudR2Poincare.L3
