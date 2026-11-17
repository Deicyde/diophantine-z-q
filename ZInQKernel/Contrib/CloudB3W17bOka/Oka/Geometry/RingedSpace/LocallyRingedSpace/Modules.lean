/-
Copyright (c) 2026 Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuichiro Hoshi, Junnosuke Koizumi, Christian Merten
-/
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
import ZInQKernel.Contrib.CloudB3W17bOka.Oka.Topology.Category.TopCat.Opens

/-!
# Sheaves of modules over the structure sheaf of a locally ringed space

Mathlib has this theory for **schemes** and only for schemes:
`AlgebraicGeometry.Scheme.ringCatSheaf` and `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom` in
`Mathlib/AlgebraicGeometry/Modules/Presheaf.lean`, and pushforward and pullback of
`AlgebraicGeometry.Scheme.Modules` in `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`. A
development that reaches complex-analytic spaces needs the same one level down, at
`AlgebraicGeometry.LocallyRingedSpace`, and that is what this file is. There is no analytic
content in it; see `README.md` on the mirror tree.

## Where this would go upstream, and the two alternatives priced

The declarations here are stated for `AlgebraicGeometry.LocallyRingedSpace`, whose theory lives
under `Mathlib/Geometry/RingedSpace/`, so the mirror path proposes a new file
`Mathlib/Geometry/RingedSpace/LocallyRingedSpace/Modules.lean`, beside the two files that
directory already holds. Being new it costs no existing Mathlib file anything; the Mathlib part
of its own transitive closure is **1852** modules. Both alternatives were measured rather than
dismissed, by breadth-first search over `^(public )?import` in `.lake/packages/mathlib` with
comments masked, counting only modules with a file under `Mathlib/`:

* **into `Mathlib/Geometry/RingedSpace/LocallyRingedSpace.lean`**, which this repository already
  mirrors at `Oka/Geometry/RingedSpace/LocallyRingedSpace.lean`: that file's closure is 1688 and
  `Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree` costs it **164**. `README.md` records 96
  as the figure that once made an upstreaming judged too expensive, so this is the option the
  price rules out, and it is why the material is a new file rather than an addition to the mirror
  file that already exists.
* **into `Mathlib/AlgebraicGeometry/Modules/Sheaf.lean`**, beside the scheme versions: closure
  2264, and the two Mathlib imports below together with the Mathlib target of the third —
  `Oka/Topology/Category/TopCat/Opens.lean` is itself a mirror file — cost it **4**. That is
  cheap, and a Mathlib reviewer who wanted the locally-ringed-space and the scheme statements in
  one place could take it. It is not the choice made here because the namespace, and every other
  file about it, sits under `Mathlib/Geometry/RingedSpace/`.

## Main definitions

- `AlgebraicGeometry.LocallyRingedSpace.ringSheaf`: the structure sheaf as a sheaf of rings
  rather than of commutative rings, which is the form in which `SheafOfModules` applies. **The
  site it is stated over is spelled `↑Y.toPresheafedSpace` and that is load-bearing**; the reason
  is on its own docstring and it is a measurement, not a preference.
- `AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom`: the morphism of sheaves of rings
  induced by a morphism of locally ringed spaces, and
  `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModules`, the pullback of `𝒪`-modules along
  it, with its adjunction `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesAdj`.
- `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesUnitToUnit`: the canonical map from
  the pullback of `𝒪_Y` to `𝒪_X`, which **is an isomorphism** —
  `AlgebraicGeometry.LocallyRingedSpace.isIso_pullbackModulesUnitToUnit` — and with it pullback
  sends free sheaves to free sheaves,
  `AlgebraicGeometry.LocallyRingedSpace.Hom.pullbackModulesFreeIso` and
  `AlgebraicGeometry.LocallyRingedSpace.Hom.freeFunctorCompPullbackModulesIso`.

## Provenance

Split out of `Oka/AnalyticSpace/Relations.lean` for taxis #905, unchanged: no statement, proof or
name here differs from what that file held. What that file kept is the three lines about `ℂ^ι`
that are the only analytic content it ever had.
-/

open CategoryTheory Limits TopologicalSpace Opposite SheafOfModules AlgebraicGeometry

universe u

namespace AlgebraicGeometry.LocallyRingedSpace

variable (Y : LocallyRingedSpace.{u})

/-- The structure sheaf of a locally ringed space, viewed as a sheaf of rings rather than of
commutative rings. This is the form in which the theory of `SheafOfModules` and coherence
applies.

**The site is spelled `↑Y.toPresheafedSpace` rather than `↑Y`, and that is load-bearing.** The
two are definitionally equal, but `TopologicalSpace.Opens.map f.base` — for `f` a morphism of
locally ringed spaces — carries its implicit type arguments in the first spelling, and instance
search does not cross the two. `↑Y` elaborates to `↑Y.toTopCat`, and that is what makes the two
discrimination-tree keys differ, since the key is built from the elaborated implicit arguments;
so with `↑Y` here, Mathlib's

`instance : (Opens.map f).IsContinuous (Opens.grothendieckTopology Y)
  (Opens.grothendieckTopology X)`

is not found for `f.base`. Measured in three sessions.

**The consequence is a cost and not an impossibility, which is a correction of what this
docstring used to say.** The missing instance can be declared by hand — `inferInstanceAs` from
the `↑Y.toPresheafedSpace` spelling of the same statement transports it — and with it
`AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom` below can be stated at the `↑Y` site
after all; without it, it cannot, and that half was measured too. So the old spelling costs one
transported instance, which every consumer would then need, where the spelling used here costs
none and is what `Opens.map` produces anyway. **Do not tidy it back.** -/
noncomputable def ringSheaf :
    Sheaf (Opens.grothendieckTopology ↑Y.toPresheafedSpace) RingCat.{u} :=
  ⟨Y.presheaf ⋙ forget₂ CommRingCat.{u} RingCat.{u},
    (TopCat.Presheaf.isSheaf_iff_isSheaf_comp
      (forget₂ CommRingCat.{u} RingCat.{u}) Y.presheaf).1 Y.IsSheaf⟩

/-- Sheafification is available at the site `AlgebraicGeometry.LocallyRingedSpace.ringSheaf` uses.

Mathlib has this for `Opens.grothendieckTopology ↑Y.toTopCat`. **This instance is load-bearing and
its absence is invisible here**: delete it and this file still elaborates, while `lake build` fails
**3857 modules later, in a different subtree**, at `Oka/Analytification/SheafCoherent.lean:150`
with `failed to synthesize instance of type class (analytificationSheaf g).PreservesZeroMorphisms`.

**What makes it load-bearing is not the reason this docstring used to give.** It said instance
search does not cross the two spellings, *for the reason above* — but the reason above is about
`Opens.map f.base`'s implicit arguments, and no `Opens.map` occurs here: with this instance
deleted, `infer_instance` still finds `HasSheafify (Opens.grothendieckTopology ↑Z.toPresheafedSpace)
AddCommGrpCat` at a direct goal in this very file. So the two spellings *do* cross at that goal,
and what the declared instance buys is something the deletion test locates and this docstring does
not: **the cause is unmeasured, the cost is not.** All three measurements are from 2026-08-25 at
`master` = `d12d334`. -/
instance hasSheafify_toPresheafedSpace :
    HasSheafify (Opens.grothendieckTopology ↑Y.toPresheafedSpace) AddCommGrpCat.{u} :=
  inferInstanceAs (HasSheafify (Opens.grothendieckTopology ↑Y.toTopCat) AddCommGrpCat.{u})

variable {Y} in
/-- **The morphism of sheaves of rings attached to a morphism of locally ringed spaces.**

Mathlib has this for schemes, as `AlgebraicGeometry.Scheme.Hom.toRingCatSheafHom`, and not for
locally ringed spaces; this is that definition verbatim. It is what
`SheafOfModules.pullback` consumes, and hence what makes the pullback of
`𝒪`-modules along a morphism of locally ringed spaces — the analytification of a sheaf, among
other things — available at all. -/
noncomputable def Hom.toRingSheafHom {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    Y.ringSheaf ⟶ ((Opens.map f.base).sheafPushforwardContinuous
      RingCat.{u} _ _).obj X.ringSheaf where
  hom := Functor.whiskerRight f.c _

variable {Y} in
/-- The existing module pushforward has a left adjoint, using the actual continuous
open-set functor and module sheafification. No premise on the morphism is added. -/
instance Hom.isRightAdjoint_pushforwardModules {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    (SheafOfModules.pushforward.{u} f.toRingSheafHom).IsRightAdjoint := by
  let φ := f.toRingSheafHom
  haveI : (PresheafOfModules.pushforward.{u} (F := Opens.map f.base)
      (R := X.ringSheaf.obj) (S := Y.ringSheaf.obj) φ.hom).IsRightAdjoint :=
    CategoryTheory.Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
      (PresheafOfModules.pullbackObjIsDefined_eq_top (F := Opens.map f.base)
        (R := X.ringSheaf.obj) (S := Y.ringSheaf.obj) φ.hom)
  exact (SheafOfModules.PullbackConstruction.adjunction.{u}
    (F := Opens.map f.base) (R := X.ringSheaf) φ).isRightAdjoint

variable {Y} in
/-- **Pullback of `𝒪`-modules along a morphism of locally ringed spaces.**

`SheafOfModules.pullback`, which Mathlib defines as the left adjoint of
`SheafOfModules.pushforward` for any morphism of sheaves of rings over a continuous functor of
sites, applied to `AlgebraicGeometry.LocallyRingedSpace.Hom.toRingSheafHom`. Mathlib uses exactly
this to make `AlgebraicGeometry.Scheme.Modules` functorial; nothing about it is special to
schemes, and the only thing that had to be supplied for locally ringed spaces is the morphism of
sheaves of rings above. -/
noncomputable def Hom.pullbackModules {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    SheafOfModules.{u} Y.ringSheaf ⥤ SheafOfModules.{u} X.ringSheaf :=
  SheafOfModules.pullback.{u} f.toRingSheafHom

variable {Y} in
/-- **Pullback is left adjoint to pushforward**, which is what determines it: it is defined as
that left adjoint, so this is the adjunction and not a theorem about it. -/
noncomputable def Hom.pullbackModulesAdj {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f.pullbackModules ⊣ SheafOfModules.pushforward.{u} f.toRingSheafHom :=
  SheafOfModules.pullbackPushforwardAdjunction.{u} f.toRingSheafHom

variable {Y} in
/-- **The pullback of the structure sheaf maps canonically to the structure sheaf.**

`SheafOfModules.pullbackObjUnitToUnit`, which needs no hypothesis on `f` beyond the adjunction
that defines the pullback. This is the map that makes `𝒪_X` an algebra over the pullback of
`𝒪_Y`, and it is what a comparison theorem between the two structure sheaves is a statement
about. -/
noncomputable def Hom.pullbackModulesUnitToUnit {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f.pullbackModules.obj (SheafOfModules.unit Y.ringSheaf) ⟶ SheafOfModules.unit X.ringSheaf :=
  SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingSheafHom

variable {Y} in
/-- **The pullback of `𝒪_Y` is `𝒪_X`**: the canonical map above is an isomorphism.

Mathlib proves this for a *final* functor between the sites
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`), and here that functor is
`TopologicalSpace.Opens.map f.base`, which is final because `Opens` is filtered —
`TopologicalSpace.Opens.final_map`.

**The `inferInstanceAs` is load-bearing**: `Hom.pullbackModulesUnitToUnit` is a plain `def`, so
instance search does not unfold it, and replacing this body by `by infer_instance` fails with
`failed to synthesize instance of type class IsIso (Hom.pullbackModulesUnitToUnit f)`.

**The universe annotation is not.** This docstring used to say that
`SheafOfModules.pullbackObjUnitToUnit` written without `.{u}` elaborates with a universe
metavariable at which the instance does not fire; dropping the `.{u}` here compiles. Both
measured 2026-08-25 at `master` = `d12d334`. The `.{u}` is kept because it is what the rest of
this file spells, not because anything breaks without it. -/
instance isIso_pullbackModulesUnitToUnit {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    IsIso (Hom.pullbackModulesUnitToUnit.{u} f) :=
  inferInstanceAs (IsIso (SheafOfModules.pullbackObjUnitToUnit.{u} f.toRingSheafHom))

variable {Y} in
/-- **The pullback of the structure sheaf is the structure sheaf**, as an isomorphism. -/
noncomputable def Hom.pullbackModulesUnitIso {X : LocallyRingedSpace.{u}} (f : X ⟶ Y) :
    f.pullbackModules.obj (SheafOfModules.unit Y.ringSheaf) ≅ SheafOfModules.unit X.ringSheaf :=
  asIso (Hom.pullbackModulesUnitToUnit.{u} f)

variable {Y} in
/-- **The pullback of a free sheaf of modules is free**, on the same index type — which need not
be finite. Mathlib's `SheafOfModules.pullbackObjFreeIso` at `Hom.toRingSheafHom`. -/
noncomputable def Hom.pullbackModulesFreeIso {X : LocallyRingedSpace.{u}} (f : X ⟶ Y)
    (I : Type u) :
    f.pullbackModules.obj (SheafOfModules.free I) ≅ SheafOfModules.free I :=
  SheafOfModules.pullbackObjFreeIso.{u} f.toRingSheafHom I

variable {Y} in
/-- **Pullback of `𝒪`-modules commutes with the free-sheaf functor**, naturally. -/
noncomputable def Hom.freeFunctorCompPullbackModulesIso {X : LocallyRingedSpace.{u}}
    (f : X ⟶ Y) :
    SheafOfModules.freeFunctor ⋙ f.pullbackModules ≅ SheafOfModules.freeFunctor :=
  SheafOfModules.freeFunctorCompPullbackIso.{u} f.toRingSheafHom

end AlgebraicGeometry.LocallyRingedSpace
