/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Property transport on the SAME actually descended scheme/group. This file
consumes a genuine cartesian comparison, not an effective MODEL existence
assumption in a final NOS theorem. Properness uses the real canonical
source fpqc proof, with unchanged H76 namespace and fixed pins; geometric
connectedness is proved in GeometricProperties without a desired Fact.
Source credit: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2,
ported canonically by H5 lane4, preserving LICENSE/NOTICE/modification credits.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GeometricProperties
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_AlgebraicGeometry_IsProper_descendsAlong_surjective_inf_flat_inf_quasiCompact
import ZInQKernel.HDecomp.Objects

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- Properness of the actual cartesian descended scheme. The fpqc descent
    supplier is a proved source theorem, not a caller's Proper Fact. -/
theorem proper_of_fpqc_isPullback
    {X X' S S' : Scheme.{u}} {q : X' ⟶ X} {f' : X' ⟶ S'} {f : X ⟶ S} {p : S' ⟶ S}
    (hp : IsPullback q f' f p) [Surjective p] [Flat p] [QuasiCompact p] [IsProper f'] :
    IsProper f := by
  letI : MorphismProperty.DescendsAlong (@IsProper : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
    ZInQ.Contrib.CloudW03NeronSurj.FLT.AlgebraicGeometry.IsProper.descendsAlong_surjective_inf_flat_inf_quasiCompact
  exact MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsProper) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp.flip
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance

/-- All native abelian-scheme properties on the SAME descended group object,
    rather than on a replacement model or supplied unknown quotient.
    The actual group law is constructed separately from the group datum. -/
theorem abelianScheme_on_cartesian_group
    {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (G' : Grp (Over (Spec (CommRingCat.of R'))))
    (p : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    [Surjective p] [Flat p] [QuasiCompact p]
    (q : G'.X.left ⟶ G.X.left) (hq : IsPullback q G'.X.hom G.X.hom p)
    [PkgI2.IsAbelianScheme G'] : PkgI2.IsAbelianScheme G := by
  haveI : IsProper G'.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : Smooth G'.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : GeometricallyConnected G'.X.hom := PkgI2.IsAbelianScheme.geomConnected
  exact ⟨proper_of_fpqc_isPullback hq, smooth_of_fpqc_isPullback hq,
    geometricallyConnected_of_surjective_isPullback hq⟩

#print axioms proper_of_fpqc_isPullback
#print axioms abelianScheme_on_cartesian_group

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
