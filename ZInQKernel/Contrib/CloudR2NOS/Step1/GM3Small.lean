/-
H5 lane3 Step 1: `IrreducibleSpaceOfClosedImmersionRange` (GM3Assembly.lean) PROVED from
Mathlib. 2026-11-17. New file. SOURCE-ONLY, UNCOMPILED. Universe u.

The proof:
* a closed immersion's underlying map is a closed embedding (`Scheme.Hom.isClosedEmbedding`), so
  the source is homeomorphic to the range (`IsEmbedding.toHomeomorph`);
* the irreducible range is an irreducible space (`Subtype.irreducibleSpace`);
* that is transported by the continuous surjection `φ.symm`
  (`Function.Surjective.irreducibleSpace`).
-/
import ZInQKernel.Contrib.CloudR2NOS.Step1.GM3Assembly

set_option autoImplicit false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Topology

namespace ZInQ.Contrib.CloudR2NOS.Step1

theorem irreducibleSpaceOfClosedImmersionRange : IrreducibleSpaceOfClosedImmersionRange.{u} := by
  intro X Y f _ hirr
  haveI : IrreducibleSpace (Set.range f) := Subtype.irreducibleSpace hirr
  let φ := f.isClosedEmbedding.toIsEmbedding.toHomeomorph
  exact Function.Surjective.irreducibleSpace φ.symm.continuous φ.symm.surjective

end ZInQ.Contrib.CloudR2NOS.Step1
