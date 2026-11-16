/-
Adapted from AxiomMath/Stacks c496df0d9beea9deaeabcea8492605f9a0a2313b.
Source: StacksFrontier/CategoryTheory/Sites/SmallSiteSheafification.lean
Source SHA256: 0fa36674d266548b3b946e7aae14d9fc0f3c96916b7ede1a32127edec55ae302
Apache-2.0; see LICENSE and NOTICE.md.
Changes: isolated vendor namespaces and import paths; citation attributes removed.
-/
import Mathlib.Algebra.Category.Grp.AB
import Mathlib.CategoryTheory.Sites.LocallyBijective

namespace ZInQ.Contrib.CloudB3W16Cartier.Vendor
open _root_.CategoryTheory


/-!
# Sheafification of abelian presheaves on a small site

On a small site, abelian presheaves admit a sheafification and the maps it inverts are exactly
the locally bijective ones: `AddCommGrpCat` in the universe of the site satisfies AB5 and is a
concrete category with the exactness properties the two statements need, so both are instances.

## Main results

* `CategoryTheory.smallSiteHasSheafify`: abelian presheaves on a small site admit sheafification.
* `CategoryTheory.smallSiteWEqualsLocallyBijective`: sheafification of abelian presheaves on a
  small site inverts exactly the locally bijective maps.
-/

section

namespace CategoryTheory

universe w

/-- Sheafification of abelian presheaves exists on a small site. -/
theorem smallSiteHasSheafify {D : Type w} [SmallCategory D] (K : GrothendieckTopology D) :
    HasSheafify K AddCommGrpCat.{w} := inferInstance

/-- On a small site, the maps of abelian presheaves inverted by sheafification are exactly the
locally bijective ones. -/
theorem smallSiteWEqualsLocallyBijective {D : Type w} [SmallCategory D]
    (K : GrothendieckTopology D) : K.WEqualsLocallyBijective AddCommGrpCat.{w} := inferInstance

end CategoryTheory

end
end ZInQ.Contrib.CloudB3W16Cartier.Vendor
