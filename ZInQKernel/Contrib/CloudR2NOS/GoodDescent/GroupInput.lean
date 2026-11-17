/-
Copyright (c) 2026 H5/NOS Round-2 Lane5 contributors.
Released under Apache 2.0 license as described in the project LICENSE.
New same-object group-generic-fibre adapter for the actual scheme datum.
The given generic identification remains an isomorphism of GROUP OBJECTS;
no arbitrary scheme isomorphism is substituted for it. Does not claim
that the datum has already been made effective or that NOS is proved.
-/
import ZInQKernel.Contrib.CloudR2NOS.GoodDescent.SchemeDatum
import ZInQKernel.HDecomp.Objects

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace ZInQ.Contrib.CloudR2NOS.GoodDescent

variable {U S : Scheme.{u}} (p : U ⟶ S) (V : S.Opens)
    (G : Grp (Over U)) (A : Grp (Over V.toScheme))
    (e : (Over.pullback (p ⁻¹ᵁ V).ι).mapGrp.obj G ≅ (Over.pullback (p ∣_ V)).mapGrp.obj A)

/-- The underlying generic scheme isomorphism of the specified group iso,
    with only the canonical open/pullback comparison inserted. -/
def groupGenericSchemeIso :
    (G.X.hom ⁻¹ᵁ (p ⁻¹ᵁ V)).toScheme ≅ pullback A.X.hom (p ∣_ V) :=
  (pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).symm ≪≫
    (Over.forget _).mapIso ((Grp.forget _).mapIso e)

@[reassoc]
theorem groupGenericSchemeIso_snd :
    (groupGenericSchemeIso p V G A e).hom ≫ pullback.snd A.X.hom (p ∣_ V) =
      G.X.hom ∣_ (p ⁻¹ᵁ V) := by
  let t : pullback G.X.hom (p ⁻¹ᵁ V).ι ⟶ pullback A.X.hom (p ∣_ V) := e.hom.hom.hom.left
  have he := Over.w e.hom.hom.hom
  change t ≫ pullback.snd A.X.hom (p ∣_ V) =
    pullback.snd G.X.hom (p ⁻¹ᵁ V).ι at he
  change ((pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv ≫ t) ≫
      pullback.snd A.X.hom (p ∣_ V) = G.X.hom ∣_ (p ⁻¹ᵁ V)
  rw [Category.assoc, he]
  rfl

/-- Supply the exact generic cartesian square from the original
    multiplication-compatible group-object isomorphism. -/
def genericModelOfGroupIso : GenericModel G.X.hom p V where
  A := A.X.left
  a := A.X.hom
  q := (groupGenericSchemeIso p V G A e).hom ≫ pullback.fst A.X.hom (p ∣_ V)
  cartesian := by
    refine IsPullback.of_iso_pullback ?_ (groupGenericSchemeIso p V G A e) rfl
      (groupGenericSchemeIso_snd p V G A e)
    constructor
    calc
      ((groupGenericSchemeIso p V G A e).hom ≫ pullback.fst A.X.hom (p ∣_ V)) ≫ A.X.hom =
          (groupGenericSchemeIso p V G A e).hom ≫ (pullback.fst A.X.hom (p ∣_ V) ≫ A.X.hom) := Category.assoc ..
      _ = (groupGenericSchemeIso p V G A e).hom ≫ (pullback.snd A.X.hom (p ∣_ V) ≫ (p ∣_ V)) := by rw [pullback.condition]
      _ = ((groupGenericSchemeIso p V G A e).hom ≫ pullback.snd A.X.hom (p ∣_ V)) ≫ (p ∣_ V) := (Category.assoc ..).symm
      _ = (G.X.hom ∣_ (p ⁻¹ᵁ V)) ≫ (p ∣_ V) := by rw [groupGenericSchemeIso_snd]

/-- Retain the group-object iso while constructing the actual underlying
    scheme descent datum. No datum/effectivity input is taken. -/
def schemeDatumOfGroupIso [Etale p] (s : S) [Mono (p.fiberToSpecResidueField s)]
    (hV : ∀ z : S, z ∉ V → z = s) : Over.DescentDatum p G.X :=
  (genericModelOfGroupIso p V G A e).schemeDatum s hV

/-- The generic scheme-coordinate map is literally the given group iso,
    followed by the canonical generic-fibre projection. -/
@[simp]
theorem genericModelOfGroupIso_q :
    (genericModelOfGroupIso p V G A e).q =
      (pullbackRestrictIsoRestrict G.X.hom (p ⁻¹ᵁ V)).inv ≫
        e.hom.hom.hom.left ≫ pullback.fst A.X.hom (p ∣_ V) := by
  rfl

#print axioms groupGenericSchemeIso_snd
#print axioms genericModelOfGroupIso
#print axioms schemeDatumOfGroupIso

end ZInQ.Contrib.CloudR2NOS.GoodDescent
