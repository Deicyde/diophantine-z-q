/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Geometry.RingedSpace.LocallyRingedSpace.Modules

/-!
# Pseudofunctoriality of the pullback of `𝒪`-modules

For morphisms `f : X ⟶ Y` and `g : Y ⟶ Z` of locally ringed spaces, pulling back along `g` and
then along `f` is pulling back along `f ≫ g`; pullbacks along equal morphisms are isomorphic; and
consequently a commutative square of locally ringed spaces gives an isomorphism between the two
composite pullbacks. This is Mathlib's `SheafOfModules.pullbackComp`, as
`AlgebraicGeometry.Scheme.Modules.pullbackComp` does for schemes.

The *restriction* of a sheaf of modules on `Y` to an open `U` is the pullback along the open
immersion `Y|_U ⟶ Y` (`AlgebraicGeometry.LocallyRingedSpace.restrictModules`).
-/

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable {X Y Z T : LocallyRingedSpace.{u}}

/-- **Pullback of `𝒪`-modules is compatible with composition**:
`f^* ∘ g^* ≅ (f ≫ g)^*`. -/
noncomputable def Hom.pullbackModulesComp (f : X ⟶ Y) (g : Y ⟶ Z) :
    g.pullbackModules ⋙ f.pullbackModules ≅ (f ≫ g).pullbackModules :=
  SheafOfModules.pullbackComp.{u} g.toRingSheafHom f.toRingSheafHom

/-- Pullbacks of `𝒪`-modules along equal morphisms are isomorphic. -/
noncomputable def Hom.pullbackModulesCongr {f g : X ⟶ Y} (h : f = g) :
    f.pullbackModules ≅ g.pullbackModules :=
  eqToIso (h ▸ rfl)

/-- **A commutative square of locally ringed spaces gives an isomorphism of composite
pullbacks**: if `a ≫ b = c ≫ d` then `a^* ∘ b^* ≅ c^* ∘ d^*`. -/
noncomputable def Hom.pullbackModulesCommSqIso {a : X ⟶ Y} {b : Y ⟶ T} {c : X ⟶ Z}
    {d : Z ⟶ T} (h : a ≫ b = c ≫ d) :
    b.pullbackModules ⋙ a.pullbackModules ≅ d.pullbackModules ⋙ c.pullbackModules :=
  Hom.pullbackModulesComp a b ≪≫ Hom.pullbackModulesCongr h ≪≫
    (Hom.pullbackModulesComp c d).symm

variable (Y) in
/-- **The restriction of a sheaf of `𝒪_Y`-modules to an open `U`**, as a sheaf of modules on the
open subspace `Y|_U`: the pullback along the open immersion `Y|_U ⟶ Y`. -/
noncomputable abbrev restrictModules (U : Opens Y) :
    SheafOfModules.{u} Y.ringSheaf ⥤ SheafOfModules.{u} (Y.restrict U.isOpenEmbedding).ringSheaf :=
  (Y.ofRestrict U.isOpenEmbedding).pullbackModules

end AlgebraicGeometry.LocallyRingedSpace
