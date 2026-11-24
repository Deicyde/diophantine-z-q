/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.

Stage geometric connectedness is DERIVED from the ACTUAL upstairs GROUP
iso along its actual surjective base map. The cartesian square uses the
same original scheme/group maps; no hStageGC, supplied scheme substitute,
or unproved ind-étale stage-to-upstairs algebra is introduced.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.Effective.GeometricProperties
import ZInQKernel.HDecomp.Objects

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective

/-- The ACTUAL upstairs GROUP iso supplies a cartesian square and hence
    geometric connectedness of the SAME stage group scheme. -/
theorem geometricallyConnected_of_surjective_groupIso
    {S U : Scheme.{u}} (p : U ⟶ S) [Surjective p]
    (G : Grp (Over S)) (N : Grp (Over U)) [GeometricallyConnected N.X.hom]
    (i : (Over.pullback p).mapGrp.obj G ≅ N) : GeometricallyConnected G.X.hom := by
  let E : pullback G.X.hom p ≅ N.X.left :=
    (Over.forget _).mapIso ((Grp.forget _).mapIso i)
  let q : N.X.left ⟶ G.X.left := E.inv ≫ pullback.fst G.X.hom p
  have hsnd : E.inv ≫ pullback.snd G.X.hom p = N.X.hom := by
    have h := Over.w i.inv.hom.hom
    change E.inv ≫ pullback.snd G.X.hom p = N.X.hom at h
    exact h
  have hc : IsPullback q N.X.hom G.X.hom p := by
    refine IsPullback.of_iso_pullback ?_ E.symm rfl hsnd
    constructor
    calc
      q ≫ G.X.hom = E.inv ≫ (pullback.fst G.X.hom p ≫ G.X.hom) := Category.assoc ..
      _ = E.inv ≫ (pullback.snd G.X.hom p ≫ p) := by rw [pullback.condition]
      _ = N.X.hom ≫ p := by rw [← Category.assoc, hsnd]
  exact geometricallyConnected_of_surjective_isPullback hc

/-- Proper/smooth stage properties plus an actual good upstairs model give
    the original native abelian-scheme class on the SAME stage GROUP. -/
theorem isAbelianScheme_of_surjective_groupIso
    {R P : Type u} [CommRing R] [CommRing P]
    (p : Spec (CommRingCat.of P) ⟶ Spec (CommRingCat.of R)) [Surjective p]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [Smooth G.X.hom] [IsProper G.X.hom]
    (N : Grp (Over (Spec (CommRingCat.of P)))) [PkgI2.IsAbelianScheme N]
    (i : (Over.pullback p).mapGrp.obj G ≅ N) : PkgI2.IsAbelianScheme G := by
  haveI : GeometricallyConnected N.X.hom := PkgI2.IsAbelianScheme.geomConnected
  exact ⟨inferInstance, inferInstance, geometricallyConnected_of_surjective_groupIso p G N i⟩

#print axioms geometricallyConnected_of_surjective_groupIso
#print axioms isAbelianScheme_of_surjective_groupIso

end ZInQ.Contrib.CloudR2NOS.GoodDescent.Effective
