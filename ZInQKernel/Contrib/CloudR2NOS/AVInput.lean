import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudW03NeronSurj.Basic
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_JacJ1Iface

/-!
# The actual PkgI2 objects as inputs to the general NOS source

This module uses the existing, unchanged H-76 source data and the group law on
exactly the given `Grp (Over (Spec R))`. It neither copies that library's
nominal definitions nor replaces the abelian variety by an unrelated model.

Source credit: the abelian-scheme bundle conversion factors the construction
in `CloudW03NeronSurj/Main.lean`, based on Anthropic's Apache-2.0 source at
`6e837e75355538c7f80bab5b956861e86c4eacc2`. Its existing LICENSE/NOTICE and
modification notices are unchanged. This new bridge generalizes that local
construction to any base ring and adds the original PkgI2 abelian-variety
input using Mathlib's geometric-integrality API. No Néron-model existence,
NOS criterion, henselianity, or perfectness is assumed or asserted here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace ZInQ.Contrib.CloudR2NOS

/-- The source relative group law is the law of the given group object. -/
def relativeLawOfGrp {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) :
    GoodReductionJacobian.RelativeGroupLaw R G.X.hom := by
  letI : GrpObj (Over.mk G.X.hom) := G.grp
  exact GoodReductionJacobian.relativeGroupLawOfGrpObj R G.X.hom

/-- Convert an actual PkgI2 abelian scheme to the already published source
bundle, without adding a model or changing its underlying scheme. -/
theorem sourceBundleOfAbelianScheme {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G] :
    GoodReductionJacobian.AbelianSchemePropertyBundle R G.X.hom := by
  haveI : GeometricallyConnected G.X.hom := PkgI2.IsAbelianScheme.geomConnected
  exact
    { smooth := PkgI2.IsAbelianScheme.smooth
      proper := PkgI2.IsAbelianScheme.proper
      connectedFibres := fun s => G.X.hom.isConnected_preimage_singleton s
      hasGroupLaw := ⟨relativeLawOfGrp G⟩ }

/-- Geometric integrality implies geometric connectedness over the same base.
The proof uses the actual geometric fibres, not a dimension-zero surrogate. -/
theorem geometricallyConnectedOfIntegral {X Y : Scheme.{u}} (f : X ⟶ Y)
    [GeometricallyIntegral f] : GeometricallyConnected f := by
  constructor
  intro K instK y Z fst snd hpb
  haveI : IrreducibleSpace Z :=
    (inferInstance : GeometricallyIrreducible f).geometrically_irreducibleSpace
      y fst snd hpb
  infer_instance

/-- Every original PkgI2 abelian variety provides the general source's
abelian bundle on the same scheme and its same group law, over every field. -/
theorem sourceBundleOfAbelianVariety {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A] :
    GoodReductionJacobian.AbelianSchemePropertyBundle K A.X.hom := by
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : PkgI2.IsAbelianScheme A :=
    { proper := PkgI2.IsAbelianVariety.proper
      smooth := PkgI2.IsAbelianVariety.smooth
      geomConnected := geometricallyConnectedOfIntegral A.X.hom }
  exact sourceBundleOfAbelianScheme A

/-- The source law is commutative whenever the SAME group object is commutative.
This is an equality on all test schemes, not only geometric points. -/
theorem relativeLawOfGrp_commutative {R : Type u} [CommRing R]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [IsCommMonObj G.X] :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
      (x y : NeronModelInfra.SchemeHomOver t G.X.hom),
      (relativeLawOfGrp G).mul t x y = (relativeLawOfGrp G).mul t y x := by
  intro T t x y
  letI : GrpObj (Over.mk G.X.hom) := G.grp
  letI : IsCommMonObj (Over.mk G.X.hom) := (inferInstance : IsCommMonObj G.X)
  change NeronModelInfra.overHomToSchemeHomOver
      (NeronModelInfra.schemeHomOverToOverHom x *
        NeronModelInfra.schemeHomOverToOverHom y) =
    NeronModelInfra.overHomToSchemeHomOver
      (NeronModelInfra.schemeHomOverToOverHom y *
        NeronModelInfra.schemeHomOverToOverHom x)
  rw [mul_comm]

/-- Commutativity for the source law of an original PkgI2 abelian variety follows
from Mathlib's actual proper geometrically integral group-scheme theorem. -/
theorem relativeLawOfAbelianVariety_commutative {K : Type u} [Field K]
    (A : Grp (Over (Spec (CommRingCat.of K)))) [PkgI2.IsAbelianVariety A] :
    ∀ {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of K))
      (x y : NeronModelInfra.SchemeHomOver t A.X.hom),
      (relativeLawOfGrp A).mul t x y = (relativeLawOfGrp A).mul t y x := by
  haveI : IsProper A.X.hom := PkgI2.IsAbelianVariety.proper
  haveI : GeometricallyIntegral A.X.hom := PkgI2.IsAbelianVariety.geomIntegral
  haveI : IsCommMonObj A.X := isCommMonObj_of_isProper_of_geometricallyIntegral A.X
  intro T t x y
  exact relativeLawOfGrp_commutative A t x y

end ZInQ.Contrib.CloudR2NOS

#print axioms ZInQ.Contrib.CloudR2NOS.sourceBundleOfAbelianScheme
#print axioms ZInQ.Contrib.CloudR2NOS.geometricallyConnectedOfIntegral
#print axioms ZInQ.Contrib.CloudR2NOS.sourceBundleOfAbelianVariety
#print axioms ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp_commutative
#print axioms ZInQ.Contrib.CloudR2NOS.relativeLawOfAbelianVariety_commutative
