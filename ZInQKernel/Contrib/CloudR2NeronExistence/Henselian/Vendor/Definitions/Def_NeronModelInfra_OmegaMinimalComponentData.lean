import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: Definitions/Def_NeronModelInfra_OmegaMinimalComponentData.lean
Original Git blob: f1d9238c85df7f03d52851516271928c6fafccc7
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Removed 3 namespace-sensitive axiom-print diagnostics; full final AX3 audit is separate.
-/
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_WeakNeronModel
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_SmoothnessDefect

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace NeronModelInfra
h77_bridge_namespace

section StalkAlgebra

variable {R : Type u} [CommRing R] {Y : Scheme.{u}} (f : Y ⟶ Spec (CommRingCat.of R)) (y : Y)

theorem ofHom_stalkAlgebraMap_eq :
    CommRingCat.ofHom (stalkAlgebraMap f y) =
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫
        (Spec (CommRingCat.of R)).presheaf.germ ⊤ (f.base y) trivial) ≫ f.stalkMap y := by
  ext r
  change stalkAlgebraMap f y r = _
  rw [stalkAlgebraMap_apply]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  rw [Scheme.Hom.germ_stalkMap_apply]
  rfl

theorem fromSpecStalk_comp_eq_specMap_algebraMap_stalkAlgebra :
    letI := stalkAlgebra f y
    Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y))) := by
  letI := stalkAlgebra f y
  change Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (stalkAlgebraMap f y))
  rw [ofHom_stalkAlgebraMap_eq, Spec.map_comp, ← Scheme.SpecMap_stalkMap_fromSpecStalk f,
    Spec.fromSpecStalk_eq]

end StalkAlgebra

section Reading

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))

structure ComponentReading where

  Y : Scheme.{u}

  f : Y ⟶ Spec (CommRingCat.of R)

  smooth : Smooth f

  locallyOfFiniteType : LocallyOfFiniteType f

  e : SchemeHomOver (pullback.snd f (specGenericFibreInclusion R K)) gK

  isOpenImmersion : IsOpenImmersion e.1

  y : Y

  hy : f.base y = IsLocalRing.closedPoint R

  hmax : ∀ y' : Y, y' ⤳ y → f.base y' = IsLocalRing.closedPoint R → y' = y

  isDomain : IsDomain (Y.presheaf.stalk y)

  isDiscreteValuationRing : IsDiscreteValuationRing (Y.presheaf.stalk y)

  algebra : Algebra R (Y.presheaf.stalk y)

  halg : Y.fromSpecStalk y ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))

  algebraK : Algebra K (FractionRing (Y.presheaf.stalk y))

  isScalarTower : IsScalarTower R K (FractionRing (Y.presheaf.stalk y))

  b : Module.Basis (Fin d) (Y.presheaf.stalk y) (Ω[Y.presheaf.stalk y⁄R])

  U : XK.Opens

  hU : IsAffineOpen U

  algebraU : Algebra Γ(XK, U) (FractionRing (Y.presheaf.stalk y))

  isScalarTowerU : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U
    IsScalarTower K Γ(XK, U) (FractionRing (Y.presheaf.stalk y))

  hx : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U) (FractionRing (Y.presheaf.stalk y)))) ≫ hU.fromSpec =
    (schemeHomOverComp
      (pointGenericFibre (K := K) (K' := FractionRing (Y.presheaf.stalk y))
        (⟨Y.fromSpecStalk y, halg⟩ :
          SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (Y.presheaf.stalk y)))) f))
      e).1

  ωU : ⋀[Γ(XK, U)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U))

  hωU : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U ωU = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω

  a : FractionRing (Y.presheaf.stalk y)

  ha : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U
    TopFormOrder.topFormMap K K Γ(XK, U) (FractionRing (Y.presheaf.stalk y)) d ωU =
      a • TopFormOrder.topFormMap R K (Y.presheaf.stalk y) (FractionRing (Y.presheaf.stalk y)) d
        (exteriorPower.ιMulti (Y.presheaf.stalk y) d b)

  ha0 : a ≠ 0

attribute [instance] ComponentReading.smooth ComponentReading.locallyOfFiniteType
  ComponentReading.isOpenImmersion ComponentReading.isDomain ComponentReading.isDiscreteValuationRing

variable {R K gK d ω}

def ComponentReading.n (T : ComponentReading R K gK d ω) : ℤ :=
  TopFormOrder.addOrd (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) T.a

end Reading

section Minimal

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} (gK : XK ⟶ Spec (CommRingCat.of K)) (d : ℕ) (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤))

structure MinimalComponentData where

  ι : Type u

  finite : Finite ι

  nonempty : Nonempty ι

  C : ι → ComponentReading R K gK d ω

  isSeparated : ∀ c, IsSeparated (C c).f

  quasiCompact : ∀ c, QuasiCompact (C c).f

  isIso : ∀ c, IsIso (C c).e.1

  hgen : ∀ c (y' : ↥(C c).Y), (C c).f.base y' = IsLocalRing.closedPoint R → (C c).y ⤳ y'

  inequiv : ∀ c c', c ≠ c' → ∀ (U : ((C c).Y).Opens), (C c).y ∈ U →
    ∀ u : SchemeHomOver (U.ι ≫ (C c).f) (C c').f,
      (genericFibreRestrict R K (C c').f (U.ι ≫ (C c).f) u).1 ≫ (C c').e.1 ≠
        (genericFibreRestrict R K (C c).f (U.ι ≫ (C c).f) ⟨U.ι, rfl⟩).1 ≫ (C c).e.1

attribute [instance] MinimalComponentData.finite MinimalComponentData.nonempty

variable {R K gK d ω}

def MinimalComponentData.IsOmegaMinimal (D : MinimalComponentData R K gK d ω) : Prop :=
  (∀ (c : D.ι) (T : ComponentReading R K gK d ω), (D.C c).n ≤ T.n) ∧
  (∀ T : ComponentReading R K gK d ω, (∃ c : D.ι, T.n = (D.C c).n) →
    ∃ (c : D.ι) (W : T.Y.Opens) (hyW : T.y ∈ W) (ε : SchemeHomOver (W.ι ≫ T.f) (D.C c).f),
      IsOpenImmersion ε.1 ∧ ε.1.base ⟨T.y, hyW⟩ = (D.C c).y ∧
      (genericFibreRestrict R K (D.C c).f (W.ι ≫ T.f) ε).1 ≫ (D.C c).e.1 =
        (genericFibreRestrict R K T.f (W.ι ≫ T.f) ⟨W.ι, rfl⟩).1 ≫ T.e.1)

end Minimal

section Gates

variable {R K : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K] [Algebra R K]
  {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)} {d : ℕ} {ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)}

theorem ComponentReading.n_eq_one_of_a_eq_uniformizer (T : ComponentReading R K gK d ω)
    (ϖ : T.Y.presheaf.stalk T.y) (hϖ : IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y) = Ideal.span {ϖ})
    (h : T.a = algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) ϖ) :
    T.n = 1 := by
  unfold ComponentReading.n
  rw [h]
  exact TopFormOrder.addOrd_uniformizer _ _ ϖ hϖ

theorem ComponentReading.n_eq_two_of_a_eq_uniformizer_sq (T : ComponentReading R K gK d ω)
    (ϖ : T.Y.presheaf.stalk T.y) (hϖ : IsLocalRing.maximalIdeal (T.Y.presheaf.stalk T.y) = Ideal.span {ϖ})
    (h : T.a = algebraMap (T.Y.presheaf.stalk T.y) (FractionRing (T.Y.presheaf.stalk T.y)) ϖ ^ 2) :
    T.n = 2 := by
  unfold ComponentReading.n
  rw [h]
  exact TopFormOrder.addOrd_uniformizer_sq _ _ ϖ hϖ

theorem MinimalComponentData.IsOmegaMinimal.n_eq (D : MinimalComponentData R K gK d ω)
    (hD : D.IsOmegaMinimal) (c c' : D.ι) : (D.C c).n = (D.C c').n :=
  le_antisymm (hD.1 c (D.C c')) (hD.1 c' (D.C c))

end Gates

end NeronModelInfra

end





end ZInQ.Contrib.CloudR2NeronExistence.Henselian
