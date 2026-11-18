import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Forgetting commutativity preserves the sheaf condition, on any site

`CategoryTheory.GrothendieckTopology.HasSheafCompose (forget₂ CommRingCat RingCat)` is assumed
as a hypothesis throughout this development's topos-level ring theory —
`Stacks.forgetCommRingSheaf`, `Stacks.Sheaves.ToposPullback.pullbackCommRingSheaf`,
`AlgebraicGeometry.RingedToposHom` and `AlgebraicGeometry.ClosedRingedImmersion` all carry it.
The implementation notes of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPushforward.lean` say it is assumed because
deriving it would need a size hypothesis relating the site's hom universe to the universe of
sections.

That is not so, and the repository already contains the reason why:
`AlgebraicGeometry.preservesLimitsOfSize_forget₂_commRingCat_ringCat` proves that
`forget₂ CommRingCat RingCat` preserves limits of *every* size, because it creates them and a
limit of commutative rings exists exactly when the limit of the underlying types does. Feeding
that to `CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize` discharges the hypothesis for
an arbitrary site with no size condition at all.

The existing universe-general limit-preservation proof and canonical
`Stacks.SheafOfModules.Tensor.ringSheaf` constructor also live here. This keeps their
single implementations below ringed sites and derived tensor products in the import graph.

## Main results

* `Stacks.hasSheafCompose_forget₂_commRingCat`: on any site, and for any universe of sections,
  `forget₂ CommRingCat RingCat` preserves the sheaf condition.

## Implementation notes

This is deliberately a `theorem` and **not** an `instance`. Several structures in this
development — `AlgebraicGeometry.RingedToposHom`, `AlgebraicGeometry.ClosedRingedImmersion`,
`AlgebraicGeometry.RingedSite` — carry their own witness of this class, as a field or as a
theorem (`AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`, which this
generalizes). Registering a second, globally applicable instance would put two distinct terms
of one class in scope at every use site in that stack, which is the standard source of
`synthesized instance is not definitionally equal to expression inferred by typing rules`. Use
it with `letI`/`haveI` where a witness is wanted and none is to hand.

It is the general form of `AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat`: that
theorem is this one at `J := X.J` for a ringed site `X`.

## References

* [Stacks Project, Tag 03AD](https://stacks.math.columbia.edu/tag/03AD)
-/


open _root_.CategoryTheory
open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry
#cloudR2LocalInstances

universe t s u v w
#cloudR2Vendor preservesLimitsOfSize_forget₂_commRingCat_ringCat in

/-- The forgetful functor from commutative rings to rings preserves limits of every size: it
creates limits, and a limit of commutative rings exists exactly when the limit of the
underlying types does. -/
theorem preservesLimitsOfSize_forget₂_commRingCat_ringCat :
    PreservesLimitsOfSize.{t, s} (forget₂ CommRingCat.{w} RingCat.{w}) :=
  { preservesLimitsOfShape := fun {J} _ ↦
      { preservesLimit := fun {F} ↦
          { preserves := fun {c} hc ↦ by
              have : HasLimit (F ⋙ forget CommRingCat.{w}) :=
                ⟨_, isLimitOfPreserves (forget CommRingCat.{w}) hc⟩
              have : Small.{w} (F ⋙ forget CommRingCat.{w}).sections :=
                (Types.hasLimit_iff_small_sections _).mp inferInstance
              have : Small.{w} ((F ⋙ forget₂ CommRingCat.{w} RingCat.{w}) ⋙
                  forget RingCat.{w}).sections :=
                ‹Small.{w} (F ⋙ forget CommRingCat.{w}).sections›
              have : HasLimit (F ⋙ forget₂ CommRingCat.{w} RingCat.{w}) := inferInstance
              exact (preservesLimit_of_createsLimit_and_hasLimit F
                (forget₂ CommRingCat.{w} RingCat.{w})).preserves hc } } }

end AlgebraicGeometry

namespace Stacks
#cloudR2LocalInstances

universe w v u
#cloudR2Vendor hasSheafCompose_forget₂_commRingCat in

/-- On any site, and for any universe of sections, the sheaf condition for `CommRingCat`-valued
presheaves is preserved by `forget₂ CommRingCat RingCat`. No size hypothesis relating the site
to the universe of sections is needed: the forgetful functor creates limits and preserves them
in every size.

This is a `theorem` rather than an `instance` on purpose; see the module's implementation
notes. -/
theorem hasSheafCompose_forget₂_commRingCat {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w}) :=
  letI : PreservesLimitsOfSize.{v, max u v} (forget₂ CommRingCat.{w} RingCat.{w}) :=
    AlgebraicGeometry.preservesLimitsOfSize_forget₂_commRingCat_ringCat
  hasSheafCompose_of_preservesLimitsOfSize J

end Stacks

namespace Stacks.SheafOfModules.Tensor
#cloudR2LocalInstances

universe u v w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
#cloudR2Vendor ringSheaf in

/-- The underlying sheaf of (not necessarily commutative) rings of the ringed
site, obtained from the sheaf of commutative rings `O = R`.  `Mod(O)` is
`SheafOfModules (ringSheaf R)`.

The universe `w` of the sections is independent of the two site universes `u` and
`v`: supplying `HasSheafCompose` from `Stacks.hasSheafCompose_forget₂_commRingCat` in the local
context, rather than letting instance search find Mathlib's size-restricted
`hasSheafCompose_of_preservesMulticospan`, is what keeps `w` free. -/
def ringSheaf : Sheaf J RingCat.{w} :=
  letI := Stacks.hasSheafCompose_forget₂_commRingCat.{w, v, u} J
  ⟨R.obj ⋙ forget₂ CommRingCat RingCat,
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).property⟩
#cloudR2Vendor ringSheafSectionCommRing in

/-- The commutative structure of a canonical section ring extends its bundled ring structure. -/
local instance ringSheafSectionCommRing (siteObject : Cᵒᵖ) :
    CommRing ((ringSheaf R).obj.obj siteObject) :=
  { ((ringSheaf R).obj.obj siteObject).ring with
    mul_comm := (R.obj.obj siteObject).commRing.mul_comm }

universe moduleUniverse
#cloudR2Vendor ringSheafSectionModule in

/-- A module over a canonical section ring retains its action over the commutative sections. -/
local instance ringSheafSectionModule (siteObject : Cᵒᵖ)
    (sectionModule : ModuleCat.{moduleUniverse} ((ringSheaf R).obj.obj siteObject)) :
    Module (R.obj.obj siteObject) sectionModule :=
  sectionModule.isModule
#cloudR2Vendor ringSheafSectionModuleOfCommRing in

/-- A module over the commutative sections retains its action over the canonical section ring. -/
local instance ringSheafSectionModuleOfCommRing (siteObject : Cᵒᵖ)
    (sectionModule : ModuleCat.{moduleUniverse} (R.obj.obj siteObject)) :
    Module ((ringSheaf R).obj.obj siteObject) sectionModule :=
  sectionModule.isModule
#cloudR2Vendor ringSheafPresheafMonoidalCategory in

/-- The canonical ring index carries the existing objectwise monoidal structure. -/
noncomputable local instance ringSheafPresheafMonoidalCategory :
    MonoidalCategory (PresheafOfModules.{w} (ringSheaf R).obj) :=
  PresheafOfModulesOfCommRing.monoidalCategory (R := R.obj)
#cloudR2Vendor ringSheafPresheafSymmetricCategory in

/-- The canonical presheaf tensor is symmetric because its section rings are commutative. -/
noncomputable local instance ringSheafPresheafSymmetricCategory :
    SymmetricCategory (PresheafOfModules.{w} (ringSheaf R).obj) :=
  PresheafOfModulesOfCommRing.symmetricCategory (R := R.obj)
#cloudR2Vendor ringSheafPresheafTensorLeftPreservesColimits in

/-- Tensoring a canonical module presheaf on the left preserves colimits. -/
noncomputable local instance ringSheafPresheafTensorLeftPreservesColimits
    (modulePresheaf : PresheafOfModules.{w} (ringSheaf R).obj) :
    PreservesColimitsOfSize.{w, w} (MonoidalCategory.tensorLeft modulePresheaf) := by
  let sectionPresheaf : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
    modulePresheaf
  exact (inferInstance : PreservesColimitsOfSize.{w, w}
    (MonoidalCategory.tensorLeft sectionPresheaf))
#cloudR2Vendor ringSheafPresheafTensorRightPreservesColimits in

/-- Tensoring a canonical module presheaf on the right preserves colimits. -/
noncomputable local instance ringSheafPresheafTensorRightPreservesColimits
    (modulePresheaf : PresheafOfModules.{w} (ringSheaf R).obj) :
    PreservesColimitsOfSize.{w, w} (MonoidalCategory.tensorRight modulePresheaf) := by
  let sectionPresheaf : PresheafOfModules.{w} (R.obj ⋙ forget₂ CommRingCat RingCat) :=
    modulePresheaf
  exact (inferInstance : PreservesColimitsOfSize.{w, w}
    (MonoidalCategory.tensorRight sectionPresheaf))

end Stacks.SheafOfModules.Tensor


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
