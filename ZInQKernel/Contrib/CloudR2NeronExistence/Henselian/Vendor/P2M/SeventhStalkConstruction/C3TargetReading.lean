import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.P2M.SeventhStalkConstruction.Prelude
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul.lean
Original Git blob: d23292a5ef1bfb7b6a02aec23fb6a94d3f3c825e
NOTICE OF MODIFICATION (2026-11-18): the affine chart through the generic-fibre point of the
auxiliary closed stalk and its basis reading, one step of the original proof, are stated and
proved here as a separate lemma. No hypothesis or conclusion of the original statement is weakened.
-/

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TensorProduct"
h77_open "TensorProduct"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped _root_.TensorProduct

universe u

theorem chart_generic_field_witness_construction
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]
    {XK : Scheme.{u}} {gK : XK ⟶ Spec (CommRingCat.of K)}
    (d : ℕ) [SmoothOfRelativeDimension d gK]
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d, ⊤)) (hωframe : Scheme.Modules.IsFrameOn ω ⊤)
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of R))
    (Z : Scheme.{u}) (z : Z ⟶ Spec (CommRingCat.of R))
    (η : ↑(pullback z f))
    (T : ComponentReading R K gK d ω)
    (U₀ : (pullback z f).Opens) (hηU : η ∈ U₀)
    (v : (U₀ : Scheme.{u}) ⟶ pullback z T.f)
    (ϖ : R) (hϖ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ})
    (hy₁sp : T.f.base ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)) = IsLocalRing.closedPoint R)
    (hgen₁ : T.y ⤳ ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) :
    letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩);
    letI rAux : CommRing (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) := _root_.CommRingCat.commRing (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)));
    ∀ [aR1 : Algebra R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))]
      (halg₁ : T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)) ≫ T.f = Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))))))
      [domainO : IsDomain ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)],
    letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) rOpen domainO;
    ∀ [aAF : Algebra (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))]
      [aRF : Algebra R (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))]
      [aKF : Algebra K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))]
      [towerRAF : IsScalarTower R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))]
      [towerRKF : IsScalarTower R K (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩))],
    ∃ (U'' : XK.Opens) (hU'' : IsAffineOpen U'')
      (algU'' : Algebra Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
      (hKU'' : letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''; IsScalarTower K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
      (hx'' : Spec.map (CommRingCat.ofHom (algebraMap Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))) ≫ hU''.fromSpec =
        (NeronModelInfra.schemeHomOverComp
          (pointGenericFibre (K := K) (K' := (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)))
            (⟨T.Y.fromSpecStalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)), halg₁⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))))) T.f))
          T.e).1)
      (ωU'' : ⋀[Γ(XK, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf gK).obj (op U'')))
      (hωU'' : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections gK) d U'' ωU'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials gK) d).presheaf.map (homOfLE le_top).op ω)
      (b₁ : Module.Basis (Fin d) (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (Ω[(T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))⁄R]))
      (w₁ : (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))ˣ),
      letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra gK) U''
      TopFormOrder.topFormMap K K Γ(XK, U'') (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) d ωU'' =
        (algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) (w₁ : (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))) *
            algebraMap (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) (algebraMap R (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) ϖ) ^ T.n) •
          TopFormOrder.topFormMap R K (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) d
            (exteriorPower.ιMulti (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) d b₁) := by
  letI rOpen : CommRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) := _root_.CommRingCat.commRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)
  letI rAux : CommRing (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩))) := _root_.CommRingCat.commRing (T.Y.presheaf.stalk ((pullback.snd z T.f).base (v.base ⟨η, hηU⟩)))
  intro aR1 halg₁ domainO
  letI fieldOpen : Field (FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩)) := @FractionRing.field ((U₀ : Scheme.{u}).presheaf.stalk ⟨η, hηU⟩) rOpen domainO
  intro aAF aRF aKF towerRAF towerRKF
  let ηU : ↥U₀ := ⟨η, hηU⟩
  let y₁ : ↥T.Y := (pullback.snd z T.f).base (v.base ηU)
  let F := FractionRing ((U₀ : Scheme.{u}).presheaf.stalk ηU)
  let pt := NeronModelInfra.schemeHomOverComp
    (pointGenericFibre (K := K) (K' := F)
      (⟨T.Y.fromSpecStalk y₁, halg₁⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap R (T.Y.presheaf.stalk y₁)))) T.f))
    T.e
  have hChart :=
    @T3Glue.exists_affine_chart_of_point K inferInstance XK gK d ω F fieldOpen aKF pt.1 pt.2
  obtain ⟨U'', hU'', algU'', hKU'', hx'', ωU'', hωU''⟩ := hChart
  have hReading :=
    @NeronModelInfra.ComponentReading.exists_basis_units_topFormMap_eq_mul_zpow_smul_of_specializes
      R inferInstance inferInstance inferInstance ϖ hϖ K inferInstance inferInstance inferInstance
      XK gK d inferInstance ω hωframe T y₁ hy₁sp hgen₁ aR1 halg₁
      F fieldOpen aAF aRF aKF towerRAF towerRKF
      U'' hU'' algU'' hKU'' hx'' ωU'' hωU''
  obtain ⟨b₁, w₁, hread⟩ := hReading
  exact ⟨U'', hU'', algU'', hKU'', hx'', ωU'', hωU'', b₁, w₁, hread⟩

end P2MW.S_NeronModelInfra_exists_n_eq_and_formallySmooth_stalk_of_isOmegaMinimal_of_genericFibreRestrict_comp_eq_mul
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
