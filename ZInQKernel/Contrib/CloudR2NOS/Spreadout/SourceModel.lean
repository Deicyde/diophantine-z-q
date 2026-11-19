/-
# H5 / NOS round 2, lane 3 (`Spreadout/`): a source abelian-scheme bundle is a `PkgI2` abelian scheme

New glue (no vendored source in this file).

The Anthropic FLT source (`anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2`,
Apache-2.0, Copyright 2026 Anthropic, PBC; lane 4's canonical port
`ZInQKernel.Contrib.CloudR2NOS.Source.*` and the published H76 vendor `CloudW03NeronSurj`) encodes an
abelian scheme over a ring `R` as `GoodReductionJacobian.AbelianSchemePropertyBundle R f`: smooth,
proper, TOPOLOGICALLY connected set-theoretic fibres, and a relative group law.  `PkgI2.IsAbelianScheme`
asks for GEOMETRICALLY connected fibres instead.  This file proves the latter from the former, with no
extra geometric-connectedness input, on the EXACT group object `Grp.mk (Over.mk f)` whose group
structure is the source's own `RelativeGroupLaw.grpObjOverMk L`:

1. every scheme-theoretic fibre `f.fiber s` is connected (`Scheme.Hom.fiberHomeo` with the bundle's
   `connectedFibres`);
2. every fibre is itself a source bundle over the residue field `κ(s)` (`fiberBundle`): smoothness and
   properness by base change, connectedness by 1, and the base-changed group object
   (`Over.grpObjMkPullbackSnd`, with H76's `relativeGroupLawOfGrpObj`), whose unit section is a
   `κ(s)`-rational point;
3. the source's field theorem `AbelianSchemePropertyBundle.geometricallyIntegral` (connected smooth
   group over a field with its rational unit, Stacks 04KV) makes each fibre geometrically integral,
   hence geometrically connected (lead's `ZInQ.Contrib.CloudR2NOS.geometricallyConnectedOfIntegral`);
4. Mathlib's `GeometricallyConnected.iff_geometricallyConnected_fiber` concludes over ANY base ring,
   in particular over both points (closed and generic) of a DVR.
-/
import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudR2NOS.AVInput
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_RelativeGroupLawGrpObj
import ZInQKernel.Contrib.CloudR2NOS.Source.Theorems.Thm_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace ZInQ.Contrib.CloudR2NOS.Spreadout

section Bundle

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)}

/-- Every scheme-theoretic fibre of a source abelian-scheme bundle is connected. -/
theorem connectedSpace_fiber_of_bundle
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f) (s : Spec (CommRingCat.of R)) :
    ConnectedSpace (f.fiber s) := by
  haveI : ConnectedSpace (f ⁻¹' {s}) := isConnected_iff_connectedSpace.mp (hA.connectedFibres s)
  exact (f.fiberHomeo s).symm.surjective.connectedSpace (f.fiberHomeo s).symm.continuous

/-- **The fibre of a source abelian-scheme bundle at any point is a source abelian-scheme bundle over
the residue field**, with the base-changed group law (whose unit is a rational point). -/
theorem fiberBundle (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (s : Spec (CommRingCat.of R)) :
    GoodReductionJacobian.AbelianSchemePropertyBundle ((Spec (CommRingCat.of R)).residueField s)
      (f.fiberToSpecResidueField s) := by
  haveI : Smooth f := hA.smooth
  haveI : IsProper f := hA.proper
  haveI : ConnectedSpace (f.fiber s) := connectedSpace_fiber_of_bundle hA s
  obtain ⟨L⟩ := hA.hasGroupLaw
  letI : GrpObj (Over.mk f) := L.grpObjOverMk
  let g := (Spec (CommRingCat.of R)).fromSpecResidueField s
  letI hg : GrpObj (Over.mk (pullback.snd f g)) := Over.grpObjMkPullbackSnd (f := f) (g := g)
  refine
    { smooth := ?_
      proper := ?_
      connectedFibres := fun t => ?_
      hasGroupLaw := ⟨@GoodReductionJacobian.relativeGroupLawOfGrpObj _ _ _
        (f.fiberToSpecResidueField s) hg⟩ }
  · change Smooth (pullback.snd f g)
    infer_instance
  · change IsProper (pullback.snd f g)
    infer_instance
  · convert (isConnected_univ (α := f.fiber s)) using 1
    exact Set.eq_univ_of_forall fun a =>
      Set.mem_preimage.mpr (Set.mem_singleton_iff.mpr (Subsingleton.elim _ _))

/-- **A source abelian-scheme bundle is geometrically connected** over any base ring. -/
theorem geometricallyConnected_of_bundle
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f) : GeometricallyConnected f := by
  rw [GeometricallyConnected.iff_geometricallyConnected_fiber]
  intro s
  haveI : GeometricallyIntegral (f.fiberToSpecResidueField s) :=
    (fiberBundle hA s).geometricallyIntegral
  exact ZInQ.Contrib.CloudR2NOS.geometricallyConnectedOfIntegral _

/-- **A source abelian-scheme bundle with a relative group law `L` is a `PkgI2` abelian scheme**,
on the exact group object `Grp.mk (Over.mk f)` with the source group structure `L.grpObjOverMk`. -/
theorem isAbelianScheme_of_bundle
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle R f)
    (L : GoodReductionJacobian.RelativeGroupLaw R f) :
    @PkgI2.IsAbelianScheme R _ (@Grp.mk _ _ _ (Over.mk f) L.grpObjOverMk) :=
  { proper := hA.proper
    smooth := hA.smooth
    geomConnected := geometricallyConnected_of_bundle hA }

end Bundle

section DVR

variable {K : Type u} [Field K] (O : ValuationSubring K) [IsDiscreteValuationRing O]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of O)}

/-- The same over the original DVR `O ⊆ K`, in the literal form of `PkgI2.HasGoodReduction`'s
model: closed and generic fibres are both geometrically connected. -/
theorem isAbelianScheme_of_bundle_dvr
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle O f)
    (L : GoodReductionJacobian.RelativeGroupLaw O f) :
    @PkgI2.IsAbelianScheme O _ (@Grp.mk _ _ _ (Over.mk f) L.grpObjOverMk) :=
  isAbelianScheme_of_bundle hA L

/-- **Packing for `PkgI2.HasGoodReduction`**: a source bundle with law `L` and a group-object
isomorphism of the generic fibre of `Grp.mk (Over.mk f)` with `A` give good reduction. -/
theorem hasGoodReduction_of_bundle (A : Grp (Over (Spec (.of K))))
    (hA : GoodReductionJacobian.AbelianSchemePropertyBundle O f)
    (L : GoodReductionJacobian.RelativeGroupLaw O f)
    (e : (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap O K)))).mapGrp.obj
        (@Grp.mk _ _ _ (Over.mk f) L.grpObjOverMk) ≅ A) :
    PkgI2.HasGoodReduction A O :=
  ⟨@Grp.mk _ _ _ (Over.mk f) L.grpObjOverMk, isAbelianScheme_of_bundle hA L, ⟨e⟩⟩

end DVR

end ZInQ.Contrib.CloudR2NOS.Spreadout
