/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: Definitions.Def_AlgebraicGeometry_IdealSheafModule. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelEffCartierDiv

set_option backward.isDefEq.respectTransparency false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

noncomputable section

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

abbrev Scheme.Hom.unitToPushforwardUnit (f : X ⟶ Y) :
    SheafOfModules.unit Y.ringCatSheaf ⟶
      (SheafOfModules.pushforward f.toRingCatSheafHom).obj (SheafOfModules.unit X.ringCatSheaf) :=
  SheafOfModules.unitToPushforwardObjUnit f.toRingCatSheafHom

namespace Scheme.IdealSheafData

def module (I : X.IdealSheafData) : X.Modules :=
  (kernel I.subschemeι.unitToPushforwardUnit : SheafOfModules X.ringCatSheaf)

def moduleι (I : X.IdealSheafData) : I.module ⟶ 𝟙_ X.Modules :=
  kernel.ι I.subschemeι.unitToPushforwardUnit

def invModule (I : X.IdealSheafData) : X.Modules :=
  Scheme.Modules.fltDual I.module

end Scheme.IdealSheafData

abbrev RelEffCartierDiv.idealModule {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.module

abbrev RelEffCartierDiv.lineBundle {𝒞 S : Scheme.{u}} {f : 𝒞 ⟶ S} {r : ℕ} {T : Scheme.{u}}
    {g : T ⟶ S} (D : RelEffCartierDiv f r g) : (pullback f g).Modules :=
  D.I.invModule

end AlgebraicGeometry

end
