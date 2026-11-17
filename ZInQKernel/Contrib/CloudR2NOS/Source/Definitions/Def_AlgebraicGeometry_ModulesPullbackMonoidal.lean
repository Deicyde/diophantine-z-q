/-
NEW SOURCE EDITION — actual canonical Source pullback constructor preparation.
Not historical port recovery; not native/default/Source-dictionary acceptance.

Source: anthropics/fermats-last-theorem,
6e837e75355538c7f80bab5b956861e86c4eacc2, Definitions/Def_AlgebraicGeometry_ModulesPullbackMonoidal.lean.
Copyright 2026 Anthropic, PBC; Apache-2.0; original LICENSE/ATTRIBUTION kept.
Actual raw SHA256: 26159d778aa7ce010fc71ff9788cfd1314aa3ad7455e155f811eb49d01aa5f26.

NOTICE OF MODIFICATION: only the documented namespace prefix, import rewrite,
namespace/open dual shims and port-utility/compatibility imports are applied.
All actual original definitions, binders, universes, instances, proof terms and
options are kept unchanged; no numeric budget is added. This is a NEW Source
edition with its own C6 review, not an inferred old file from an interface/hash.
Direct and lower imports remain explicit Source-binding gaps, not permission
for a recursive port, compilation, fetch or SourceAll world.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_InternalHom
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_PresheafOfModules_isMonoidal_inverseImage_W_toPresheaf
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_SheafOfModules_Monoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_PullbackMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt

namespace ZInQ.Contrib.CloudW03NeronSurj.FLT

open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory MonoidalCategory Limits TopologicalSpace
r2nos_open_dual "CategoryTheory MonoidalCategory Limits TopologicalSpace"

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules
r2nos_namespace_dual

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

instance preservesBinaryProducts_opensMap :
    PreservesLimitsOfShape (Discrete WalkingPair) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have hinf : K.obj ⟨.left⟩ ⊓ K.obj ⟨.right⟩ ≤ c.pt := leOfHom (hc.lift
          { pt := K.obj ⟨.left⟩ ⊓ K.obj ⟨.right⟩
            π := Discrete.natTrans (fun j => match j with
              | ⟨.left⟩ => homOfLE inf_le_left
              | ⟨.right⟩ => homOfLE inf_le_right) })
        have h₁ : s.pt ≤ (Opens.map f.base).obj (K.obj ⟨.left⟩) := leOfHom (s.π.app ⟨.left⟩)
        have h₂ : s.pt ≤ (Opens.map f.base).obj (K.obj ⟨.right⟩) := leOfHom (s.π.app ⟨.right⟩)
        exact (le_inf h₁ h₂).trans (leOfHom ((Opens.map f.base).map (homOfLE hinf))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩

instance preservesTerminal_opensMap :
    PreservesLimitsOfShape (Discrete PEmpty.{1}) (Opens.map f.base) where
  preservesLimit {K} := ⟨fun {c} hc => ⟨
    { lift := fun s => homOfLE (by
        have htop : (⊤ : Y.Opens) ≤ c.pt := leOfHom (hc.lift
          { pt := ⊤, π := Discrete.natTrans (fun j => j.as.elim) })
        exact le_top.trans (leOfHom ((Opens.map f.base).map (homOfLE htop))))
      fac := fun s j => Subsingleton.elim _ _
      uniq := fun s m _ => Subsingleton.elim _ _ }⟩⟩

instance preservesFiniteProducts_opensMap : PreservesFiniteProducts (Opens.map f.base) :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal _

abbrev pullback₀ : Y.PresheafOfModules ⥤ X.PresheafOfModules :=
  PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base) (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c

instance pullback₀_monoidal : (pullback₀ f).Monoidal :=
  inferInstanceAs (PresheafOfModules.PullbackMonoidal.pb (Opens.map f.base)
    (R := X.sheaf.obj) (S := Y.sheaf.obj) f.c).Monoidal

example : pullback₀ f = PresheafOfModules.pullback f.toRingCatSheafHom.hom := rfl

variable (Y) in
instance sheafify_isLocalization' : (Modules.sheafify Y).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj) :=
  inferInstanceAs ((SheafOfModules.sheafifyFunctor Y.sheaf.obj Y.ringCatSheaf.property).IsLocalization
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj))

instance : Localization.Lifting (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (pullback₀ f ⋙ Modules.sheafify X) (Modules.pullback f) :=
  ⟨SheafOfModules.sheafificationCompPullback f.toRingCatSheafHom⟩

instance pullback_monoidal : (Modules.pullback f).Monoidal :=
  letI := SheafOfModules.presheafW_isMonoidal Y.sheaf.obj Y.ringCatSheaf.property
  Localization.Monoidal.functorMonoidalOfComp (Modules.sheafify Y)
    (SheafOfModules.presheafW (Opens.grothendieckTopology Y) Y.sheaf.obj)
    (Modules.pullback f) (pullback₀ f ⋙ Modules.sheafify X)

def pullbackTensorObjIso (L M : Y.Modules) :
    (Modules.pullback f).obj (L ⊗ M) ≅ (Modules.pullback f).obj L ⊗ (Modules.pullback f).obj M :=
  (Functor.Monoidal.μIso (Modules.pullback f) L M).symm

def pullbackTensorUnitObjIso : (Modules.pullback f).obj (𝟙_ Y.Modules) ≅ 𝟙_ X.Modules :=
  (Functor.Monoidal.εIso (Modules.pullback f)).symm

end AlgebraicGeometry.Scheme.Modules

end

end ZInQ.Contrib.CloudW03NeronSurj.FLT
