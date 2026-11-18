import Mathlib
import ZInQKernel.Contrib.CloudR2Poincare.L3.VendorAlias
import ZInQKernel.Contrib.CloudR2Poincare.L3.InstanceScope

#cloudR2LocalInstances

/-!
# Isolated Stacks proof port

Upstream: AxiomMath/Stacks, commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`,
module `StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence`, Apache-2.0 (see the adjacent L3/LICENSE).
Prominent change notice, 2026-11-14: imports are restricted to the selected proof
closure; source metadata attributes and module-visibility sections are removed;
all new declarations are isolated beneath `ZInQ.Contrib.CloudR2Poincare.L3.StacksPort` to avoid main namespace clashes.
No proof hypothesis or mathematical conclusion is replaced by an assumed fact.
-/

namespace ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
#cloudR2LocalInstances

open _root_.TopologicalSpace _root_.AlgebraicGeometry _root_.CategoryTheory



/-!
# Existence of sheafification for presheaves of abelian groups

Presheaves of abelian groups with sections in `Type w` on a site admit a left exact
sheafification as soon as the site is essentially small at `w`; no inequality between `w` and the
universes of the objects and morphisms of the site is required.

## Main results

* `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall`:
  abelian presheaves with sections in `w` on a site essentially small at `w` can be sheafified.

## References

* [Stacks Project, Tag 00WI](https://stacks.math.columbia.edu/tag/00WI)
-/


open _root_.CategoryTheory
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.GrothendieckTopology
#cloudR2LocalInstances

/-- Presheaves of abelian groups with sections in `Type w` on a site which is essentially small
at `w` admit a sheafification, and it is left exact. Neither the universe of the objects of the
site nor that of its morphisms need be contained in `w`. -/
theorem hasSheafify_addCommGrpCat_of_essentiallySmall.{w, v, u} {C : Type u} [Category.{v} C]
    (J : GrothendieckTopology C) [EssentiallySmall.{w} C] :
    HasSheafify J AddCommGrpCat.{w} :=
  have : HasSheafify ((equivSmallModel.{w} C).inverse.inducedTopology J) AddCommGrpCat.{w} :=
    inferInstance
  hasSheafifyEssentiallySmallSite.{v, w, u, w + 1, w} J _

end CategoryTheory.GrothendieckTopology


end ZInQ.Contrib.CloudR2Poincare.L3.StacksPort
