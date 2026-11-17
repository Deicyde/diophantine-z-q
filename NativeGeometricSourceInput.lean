import ZInQKernel.Contrib.CloudR2NOS.AVInput
import ZInQKernel.Contrib.CloudR2NOS.Review.AmpleGoodGeometry
import Lean

/-
H5 lead SOURCE-only construction of the Source abelian input on the LITERAL
field pullback of the original native good model. This file changes no Source
provider and does not assume a special Source bundle, Source law or field
integrality. No source-paired compilation is claimed until Parent selects the
actual AVInput dependency closure and a fresh bounded consumer check.

The special-point condition is unnecessary for these geometric input facts:
they hold for every actual field map g. Positivity and cohomology are separate.
No finite stabilizer, family presentation, very-ampleness or NOS is proved here.
-/

set_option autoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace ZInQ.Contrib.CloudR2NOS.FieldAmpleness.NativeGeometricSourceInput

/-- The original group pullback has literally the usual second projection. -/
theorem field_group_structure_map
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    ((Over.pullback g).mapGrp.obj G).X.hom = pullback.snd G.X.hom g := rfl

/-- Derive the native AV class for the SAME actual field-pullback group. -/
theorem field_pullback_isAbelianVariety
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    PkgI2.IsAbelianVariety ((Over.pullback g).mapGrp.obj G) := by
  haveI : IsProper G.X.hom := PkgI2.IsAbelianScheme.proper
  haveI : Smooth G.X.hom := PkgI2.IsAbelianScheme.smooth
  haveI : GeometricallyIntegral G.X.hom :=
    ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.goodModel_geometricallyIntegral G
  refine ⟨?_, ?_, ?_⟩
  · change IsProper (pullback.snd G.X.hom g)
    infer_instance
  · change Smooth (pullback.snd G.X.hom g)
    infer_instance
  · change GeometricallyIntegral (pullback.snd G.X.hom g)
    infer_instance

/-- Construct the Source abelian bundle on LITERAL pb.snd, not a different fibre. -/
theorem source_bundle_on_field_pullback
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle
      Ω (pullback.snd G.X.hom g) := by
  letI : PkgI2.IsAbelianVariety ((Over.pullback g).mapGrp.obj G) :=
    field_pullback_isAbelianVariety G g
  exact ZInQ.Contrib.CloudR2NOS.sourceBundleOfAbelianVariety
    ((Over.pullback g).mapGrp.obj G)

/-- The Source relative law is constructed from the SAME field-pullback group. -/
def source_law_on_field_pullback
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.RelativeGroupLaw
      Ω (pullback.snd G.X.hom g) :=
  ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp ((Over.pullback g).mapGrp.obj G)

theorem source_law_on_field_pullback_eq
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    source_law_on_field_pullback G g =
      ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp ((Over.pullback g).mapGrp.obj G) := rfl

/-- Actual properness of the literal field structure morphism. -/
theorem field_pullback_isProper
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    IsProper (pullback.snd G.X.hom g) := by
  haveI : IsProper G.X.hom := PkgI2.IsAbelianScheme.proper
  infer_instance

/-- The SAME geometric field pullback is integral, not just dimension-one. -/
theorem field_pullback_isIntegral
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    IsIntegral (pullback G.X.hom g) := by
  haveI : GeometricallyIntegral G.X.hom :=
    ZInQ.Contrib.CloudR2NOS.Review.AmpleExtension.goodModel_geometricallyIntegral G
  haveI : GeometricallyIntegral (pullback.snd G.X.hom g) := inferInstance
  exact GeometricallyIntegral.isIntegral_of_subsingleton (pullback.snd G.X.hom g)

/-- The actual original group's rational identity, not a chosen unrelated point.
This is the native Hom-monoid unit over the literal identity base map. -/
def field_identity_section
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    Spec (CommRingCat.of Ω) ⟶ pullback G.X.hom g := by
  let A := (Over.pullback g).mapGrp.obj G
  letI : GrpObj A.X := A.grp
  exact (1 : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ A.X).left

/-- The literal structure-map triangle of that SAME native identity section. -/
theorem field_identity_section_fac
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    field_identity_section G g ≫ pullback.snd G.X.hom g = 𝟙 (Spec (CommRingCat.of Ω)) := by
  let A := (Over.pullback g).mapGrp.obj G
  letI : GrpObj A.X := A.grp
  change (1 : Over.mk (𝟙 (Spec (CommRingCat.of Ω))) ⟶ A.X).left ≫ A.X.hom =
    𝟙 (Spec (CommRingCat.of Ω))
  exact Over.w _

/-- Definition anchor tying the section to the native pullback group's Source law. -/
theorem field_identity_section_eq
    {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)) :
    field_identity_section G g =
      ((ZInQ.Contrib.CloudR2NOS.relativeLawOfGrp ((Over.pullback g).mapGrp.obj G)).one
        (𝟙 (Spec (CommRingCat.of Ω)))).1 := rfl

namespace Audit

/-- Hand-written literal native field-pullback input, at the theorem's own u. -/
def E_native : Prop :=
  ∀ {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
    PkgI2.IsAbelianVariety ((Over.pullback g).mapGrp.obj G)

/-- Hand-written Source bundle contract retaining the literal pb.snd. -/
def E_source : Prop :=
  ∀ {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle
      Ω (pullback.snd G.X.hom g)

/-- Exact properness of the literal field structure map. -/
def E_proper : Prop :=
  ∀ {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
    IsProper (pullback.snd G.X.hom g)

/-- Exact integrality of the literal field-pullback scheme. -/
def E_integral : Prop :=
  ∀ {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
    IsIntegral (pullback G.X.hom g)

/-- Exact rational identity-section triangle, not merely a point-existence claim. -/
def E_identity : Prop :=
  ∀ {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R))))
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R)),
    field_identity_section G g ≫ pullback.snd G.X.hom g = 𝟙 (Spec (CommRingCat.of Ω))

/-- Wrong universe restriction. -/
def N_typeZero : Prop := E_source.{0}

/-- Wrong scope: supplying a field-pullback AV class is not deriving it. -/
def N_suppliedFieldAV : Prop :=
  ∀ {R Ω : Type u} [CommRing R] [Field Ω]
    (G : Grp (Over (Spec (CommRingCat.of R)))) [PkgI2.IsAbelianScheme G]
    (g : Spec (CommRingCat.of Ω) ⟶ Spec (CommRingCat.of R))
    [PkgI2.IsAbelianVariety ((Over.pullback g).mapGrp.obj G)],
    ZInQ.Contrib.CloudW03NeronSurj.FLT.GoodReductionJacobian.AbelianSchemePropertyBundle
      Ω (pullback.snd G.X.hom g)

open Lean Meta Elab Command

private def sameWholeType (actual expected : Name) : TermElabM Bool := do
  let ci ← getConstInfo actual
  let .thmInfo _ := ci | throwError "not a theorem: {actual}"
  let ei ← getConstInfo expected
  let some ev := ei.value? | throwError "missing expected statement: {expected}"
  if ci.levelParams.length != ei.levelParams.length then return false
  let rhs := ev.instantiateLevelParams ei.levelParams (ci.levelParams.map Level.param)
  if ci.type.hasMVar || rhs.hasMVar || ci.type.hasLevelMVar || rhs.hasLevelMVar then
    throwError "unresolved declaration/expected type"
  isDefEq ci.type rhs

run_cmd liftTermElabM do
  for (actual, expected) in [
      (``field_pullback_isAbelianVariety, ``E_native),
      (``source_bundle_on_field_pullback, ``E_source),
      (``field_pullback_isProper, ``E_proper),
      (``field_pullback_isIntegral, ``E_integral),
      (``field_identity_section_fac, ``E_identity)] do
    unless ← sameWholeType actual expected do throwError "whole field-input contract differs"
    let ax ← collectAxioms actual
    for a in ax do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains a do
        throwError "non-AX3 axiom: {a}"
    logInfo m!"FIELD_SOURCE_INPUT_WHOLE_KIND_RIGID_U_AX3_OK {actual} {ax}"
  for n in [``N_typeZero, ``N_suppliedFieldAV] do
    if ← sameWholeType ``source_bundle_on_field_pullback n then
      throwError "wrong field-input contract accepted"
    logInfo m!"FIELD_SOURCE_INPUT_NEGATIVE_REJECTED {n}"
  let ci ← getConstInfo ``source_bundle_on_field_pullback
  let .thmInfo ti := ci | throwError "source-bundle proof body absent"
  for n in [
      ``field_pullback_isAbelianVariety,
      ``ZInQ.Contrib.CloudR2NOS.sourceBundleOfAbelianVariety] do
    unless ti.value.getUsedConstants.contains n do throwError "missing actual input supplier: {n}"
  logInfo m!"FIELD_SOURCE_INPUT_ACTUAL_SUPPLIERS_OK"

end Audit
end ZInQ.Contrib.CloudR2NOS.FieldAmpleness.NativeGeometricSourceInput
