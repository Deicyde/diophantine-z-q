import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_GoodReductionJacobian_RelativeGroupLaw_topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq.lean
Original Git blob: 4b90c31a0ce906b48d351051e811fe8219ae258f
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW03NeronSurj.Vendor.Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesSectionsTensor
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_NeronModelInfra_TopFormOrder
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_NeronModelInfra_TopFormOrder_topFormMap_topFormMap
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_GoodReductionJacobian_RelativeGroupLaw_topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry NeronModelInfra GoodReductionJacobian

universe u

namespace PointsLeftGC7
h77_bridge_namespace

theorem exists_ringHom_of_mem {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {F : Type u} [Field F] (φ : Spec (CommRingCat.of F) ⟶ X) (hφ : φ.base (IsLocalRing.closedPoint F) ∈ U) :
    ∃ ψ : Γ(X, U) →+* F, Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec = φ := by
  have hr : Set.range φ.base ⊆ Set.range hU.fromSpec.base := by
    rw [IsAffineOpen.range_fromSpec]
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint F)]
    exact hφ
  let θ := IsOpenImmersion.lift hU.fromSpec φ hr
  refine ⟨(Spec.preimage θ).hom, ?_⟩
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  exact IsOpenImmersion.lift_fac _ _ _

theorem ringHom_eq_of_SpecMap_comp_fromSpec {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    {F : Type u} [CommRing F] (ψ₁ ψ₂ : Γ(X, U) →+* F)
    (h : Spec.map (CommRingCat.ofHom ψ₁) ≫ hU.fromSpec = Spec.map (CommRingCat.ofHom ψ₂) ≫ hU.fromSpec) :
    ψ₁ = ψ₂ := by
  have h1 : Spec.map (CommRingCat.ofHom ψ₁) = Spec.map (CommRingCat.ofHom ψ₂) := (cancel_mono _).mp h
  have h2 := Spec.map_injective h1
  exact congrArg (fun f => f.hom) h2

theorem exists_affineOpen_le {X : Scheme.{u}} (O : X.Opens) (x : X) (hx : x ∈ O) :
    ∃ W : X.Opens, IsAffineOpen W ∧ x ∈ W ∧ W ≤ O := by
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, hWO⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx O.2
  exact ⟨W, hW, hxW, hWO⟩

theorem fromSpec_comp_eq {K : Type u} [CommRing K] {X : Scheme.{u}} (g : X ⟶ Spec (CommRingCat.of K))
    {V : X.Opens} (hV : IsAffineOpen V) :
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) V
    hV.fromSpec ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K Γ(X, V))) := by
  have h := IsAffineOpen.SpecMap_appLE_fromSpec g (isAffineOpen_top _) hV (le_top : V ≤ g ⁻¹ᵁ ⊤)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  change _ = Spec.map (CommRingCat.ofHom
    ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ V le_top).hom)
  rw [CommRingCat.ofHom_hom, Spec.map_comp, h]

theorem appLE_congr {X Y : Scheme.{u}} {f f' : X ⟶ Y} (h : f = f') (U : Y.Opens) (V : X.Opens) (e : V ≤ f ⁻¹ᵁ U) :
    f.appLE U V e = f'.appLE U V (h ▸ e) := by
  subst h; rfl

end PointsLeftGC7

set_option backward.isDefEq.respectTransparency false in
open PointsLeftGC7 in
theorem solution
    {K : Type u} [Field K] {G : Scheme.{u}} (g : G ⟶ Spec (CommRingCat.of K))
    [Smooth g] (LG : RelativeGroupLaw K g) (d : ℕ) [SmoothOfRelativeDimension d g]
    (ω : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d, ⊤))
    (hω : ∀ (V U' U'' : G.Opens) (hV : IsAffineOpen V) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        (W : (pullback g g).Opens) (hW : IsAffineOpen W)
        (hWV : W ≤ pullback.fst g g ⁻¹ᵁ V) (hWU' : W ≤ pullback.snd g g ⁻¹ᵁ U')
        (hWU'' : W ≤ (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
            ⟨pullback.snd g g, pullback.condition.symm⟩).1 ⁻¹ᵁ U''),
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) V; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U'; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U''
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra (pullback.fst g g ≫ g)) W
        letI : Algebra Γ(G, V) Γ(pullback g g, W) := ((pullback.fst g g).appLE V W hWV).hom.toAlgebra
        letI : Algebra Γ(G, U') Γ(pullback g g, W) := ((pullback.snd g g).appLE U' W hWU').hom.toAlgebra
        letI : Algebra Γ(G, U'') Γ(pullback g g, W) :=
          ((LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
            ⟨pullback.snd g g, pullback.condition.symm⟩).1.appLE U'' W hWU'').hom.toAlgebra
        ∀ [IsScalarTower K Γ(G, V) Γ(pullback g g, W)] [IsScalarTower K Γ(G, U') Γ(pullback g g, W)]
          [IsScalarTower K Γ(G, U'') Γ(pullback g g, W)],
        ∀ (ω' : ⋀[Γ(G, U')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf g).obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf g).obj (op U''))),
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections g) d U' ω' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d).presheaf.map (homOfLE le_top).op ω →
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections g) d U'' ω'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K Γ(G, V) Γ(G, U'') Γ(pullback g g, W) d ω'' =
            TopFormOrder.topFormMap K Γ(G, V) Γ(G, U') Γ(pullback g g, W) d ω') :
    ∀ (L F : Type u) [Field L] [Field F] [Algebra K L] [Algebra L F] [Algebra K F] [IsScalarTower K L F]
        (a : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K L))) g)
        (x : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) g)
        (U' U'' : G.Opens) (hU' : IsAffineOpen U') (hU'' : IsAffineOpen U'')
        [Algebra Γ(G, U') F] [Algebra Γ(G, U'') F],
        letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U'; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U''
        ∀ [IsScalarTower K Γ(G, U') F] [IsScalarTower K Γ(G, U'') F],
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U') F)) ≫ hU'.fromSpec = x.1 →
        Spec.map (CommRingCat.ofHom (algebraMap Γ(G, U'') F)) ≫ hU''.fromSpec =
          (LG.mul (Spec.map (CommRingCat.ofHom (algebraMap K F)))
            ⟨Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1, by
              rw [Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
                ← IsScalarTower.algebraMap_eq]⟩ x).1 →
        ∀ (ω' : ⋀[Γ(G, U')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf g).obj (op U')))
          (ω'' : ⋀[Γ(G, U'')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf g).obj (op U''))),
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections g) d U' ω' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d).presheaf.map (homOfLE le_top).op ω →
          (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections g) d U'' ω'' = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials g) d).presheaf.map (homOfLE le_top).op ω →
          TopFormOrder.topFormMap K L Γ(G, U'') F d ω'' = TopFormOrder.topFormMap K L Γ(G, U') F d ω' := by
  intro L F _ _ _ _ _ _ a x U' U'' hU' hU'' algU'F algU''F
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U'; letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U''
  intro _ _ hx hax ω' ω'' hω' hω''
  classical

  let m : pullback g g ⟶ G := (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
    ⟨pullback.snd g g, pullback.condition.symm⟩).1
  have hm : m = (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩
    ⟨pullback.snd g g, pullback.condition.symm⟩).1 := rfl
  have hmg : m ≫ g = pullback.fst g g ≫ g :=
    (LG.mul (pullback.fst g g ≫ g) ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩).2

  obtain ⟨V, hV, haV, -⟩ := exists_affineOpen_le (⊤ : G.Opens) (a.1.base (IsLocalRing.closedPoint L)) trivial
  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) V
  obtain ⟨ρ, hρ⟩ := exists_ringHom_of_mem hV a.1 haV
  letI algVL : Algebra Γ(G, V) L := ρ.toAlgebra
  letI algVF : Algebra Γ(G, V) F := ((algebraMap L F).comp ρ).toAlgebra
  haveI : IsScalarTower Γ(G, V) L F := IsScalarTower.of_algebraMap_eq fun _ => rfl

  haveI : IsScalarTower K Γ(G, V) L := by
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    have h1 : Spec.map (CommRingCat.ofHom ((algebraMap Γ(G, V) L).comp (algebraMap K Γ(G, V)))) =
        Spec.map (CommRingCat.ofHom (algebraMap K L)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp, ← fromSpec_comp_eq g hV, ← Category.assoc]
      change (Spec.map (CommRingCat.ofHom ρ) ≫ hV.fromSpec) ≫ g = _
      rw [hρ, a.2]
    have h2 := congrArg (fun f => f.hom k) (Spec.map_injective h1)
    simpa using h2.symm

  let aF : Spec (CommRingCat.of F) ⟶ G := Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1
  have haF : aF = Spec.map (CommRingCat.ofHom (algebraMap L F)) ≫ a.1 := rfl
  have haFg : aF ≫ g = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    rw [haF, Category.assoc, a.2, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]
  let z : Spec (CommRingCat.of F) ⟶ pullback g g := pullback.lift aF x.1 (by rw [haFg, x.2])
  have hz : z = pullback.lift aF x.1 (by rw [haFg, x.2]) := rfl
  have hzg : z ≫ (pullback.fst g g ≫ g) = Spec.map (CommRingCat.ofHom (algebraMap K F)) := by
    rw [← Category.assoc, hz, pullback.lift_fst, haFg]

  have hzm : z ≫ m = (LG.mul (Spec.map (CommRingCat.ofHom (algebraMap K F))) ⟨aF, haFg⟩ x).1 := by
    have key := congrArg Subtype.val (LG.mul_natural (pullback.fst g g ≫ g) _ z hzg
      ⟨pullback.fst g g, rfl⟩ ⟨pullback.snd g g, pullback.condition.symm⟩)
    rw [schemeHomOverComp_coe] at key
    have h1 : schemeHomOverComp z hzg ⟨pullback.fst g g, rfl⟩ =
        (⟨aF, haFg⟩ : SchemeHomOver (Spec.map (CommRingCat.ofHom (algebraMap K F))) g) :=
      Subtype.ext (by rw [schemeHomOverComp_coe, hz, pullback.lift_fst])
    have h2 : schemeHomOverComp z hzg ⟨pullback.snd g g, pullback.condition.symm⟩ = x :=
      Subtype.ext (by rw [schemeHomOverComp_coe, hz, pullback.lift_snd])
    rw [h1, h2] at key
    rw [← hm] at key
    exact key

  have hcp : (Spec.map (CommRingCat.ofHom (algebraMap L F))).base (IsLocalRing.closedPoint F) =
      IsLocalRing.closedPoint L := Subsingleton.elim _ _
  let O : (pullback g g).Opens := (pullback.fst g g ⁻¹ᵁ V ⊓ pullback.snd g g ⁻¹ᵁ U') ⊓ m ⁻¹ᵁ U''
  have hzO : z.base (IsLocalRing.closedPoint F) ∈ O := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · show (z ≫ pullback.fst g g).base (IsLocalRing.closedPoint F) ∈ V
      rw [hz, pullback.lift_fst, haF, Scheme.Hom.comp_base, TopCat.comp_app, hcp]
      exact haV
    · show (z ≫ pullback.snd g g).base (IsLocalRing.closedPoint F) ∈ U'
      rw [hz, pullback.lift_snd, ← hx, Scheme.Hom.comp_base, TopCat.comp_app, ← SetLike.mem_coe,
        ← IsAffineOpen.range_fromSpec hU']
      exact ⟨_, rfl⟩
    · show (z ≫ m).base (IsLocalRing.closedPoint F) ∈ U''
      rw [hzm, ← hax, Scheme.Hom.comp_base, TopCat.comp_app, ← SetLike.mem_coe, ← IsAffineOpen.range_fromSpec hU'']
      exact ⟨_, rfl⟩
  obtain ⟨W, hW, hzW, hWO⟩ := exists_affineOpen_le O _ hzO
  have hWV : W ≤ pullback.fst g g ⁻¹ᵁ V := hWO.trans (inf_le_left.trans inf_le_left)
  have hWU' : W ≤ pullback.snd g g ⁻¹ᵁ U' := hWO.trans (inf_le_left.trans inf_le_right)
  have hWU'' : W ≤ m ⁻¹ᵁ U'' := hWO.trans inf_le_right
  obtain ⟨ζ, hζ⟩ := exists_ringHom_of_mem hW z hzW

  letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra (pullback.fst g g ≫ g)) W
  letI algVW : Algebra Γ(G, V) Γ(pullback g g, W) := ((pullback.fst g g).appLE V W hWV).hom.toAlgebra
  letI algU'W : Algebra Γ(G, U') Γ(pullback g g, W) := ((pullback.snd g g).appLE U' W hWU').hom.toAlgebra
  letI algU''W : Algebra Γ(G, U'') Γ(pullback g g, W) := (m.appLE U'' W hWU'').hom.toAlgebra
  letI algWF : Algebra Γ(pullback g g, W) F := ζ.toAlgebra

  have tower : ∀ (f : pullback g g ⟶ G) (hf : f ≫ g = pullback.fst g g ≫ g) (U : G.Opens) (hWU : W ≤ f ⁻¹ᵁ U),
      letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U
      letI : Algebra Γ(G, U) Γ(pullback g g, W) := (f.appLE U W hWU).hom.toAlgebra
      IsScalarTower K Γ(G, U) Γ(pullback g g, W) := by
    intro f hf U hWU
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra g) U
    letI : Algebra Γ(G, U) Γ(pullback g g, W) := (f.appLE U W hWU).hom.toAlgebra
    refine IsScalarTower.of_algebraMap_eq fun k => ?_
    change ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ (pullback.fst g g ≫ g).appLE ⊤ W le_top).hom k =
      (f.appLE U W hWU).hom (((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ g.appLE ⊤ U le_top).hom k)
    rw [← CommRingCat.comp_apply, Category.assoc, Scheme.Hom.appLE_comp_appLE, appLE_congr hf]
  haveI : IsScalarTower K Γ(G, V) Γ(pullback g g, W) := tower (pullback.fst g g) rfl V hWV
  haveI : IsScalarTower K Γ(G, U') Γ(pullback g g, W) := tower (pullback.snd g g) pullback.condition.symm U' hWU'
  haveI : IsScalarTower K Γ(G, U'') Γ(pullback g g, W) := tower m hmg U'' hWU''

  haveI : IsScalarTower Γ(G, V) Γ(pullback g g, W) F := by
    refine IsScalarTower.of_algebraMap_eq fun v => ?_
    have : ζ.comp ((pullback.fst g g).appLE V W hWV).hom = (algebraMap L F).comp ρ := by
      apply ringHom_eq_of_SpecMap_comp_fromSpec hV
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
        IsAffineOpen.SpecMap_appLE_fromSpec _ hV hW hWV, ← Category.assoc, hζ, hz, pullback.lift_fst,
        CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hρ]
    exact (congrArg (fun φ => φ v) this).symm
  haveI : IsScalarTower Γ(G, U') Γ(pullback g g, W) F := by
    refine IsScalarTower.of_algebraMap_eq fun v => ?_
    have : ζ.comp ((pullback.snd g g).appLE U' W hWU').hom = algebraMap Γ(G, U') F := by
      apply ringHom_eq_of_SpecMap_comp_fromSpec hU'
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
        IsAffineOpen.SpecMap_appLE_fromSpec _ hU' hW hWU', ← Category.assoc, hζ, hz, pullback.lift_snd, hx]
    exact (congrArg (fun φ => φ v) this).symm
  haveI : IsScalarTower Γ(G, U'') Γ(pullback g g, W) F := by
    refine IsScalarTower.of_algebraMap_eq fun v => ?_
    have : ζ.comp (m.appLE U'' W hWU'').hom = algebraMap Γ(G, U'') F := by
      apply ringHom_eq_of_SpecMap_comp_fromSpec hU''
      rw [CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, CommRingCat.ofHom_hom,
        IsAffineOpen.SpecMap_appLE_fromSpec _ hU'' hW hWU'', ← Category.assoc, hζ, hzm, hax]
    exact (congrArg (fun φ => φ v) this).symm

  have E := hω V U' U'' hV hU' hU'' W hW hWV hWU' hWU'' ω' ω'' hω' hω''
  have E' := congrArg (TopFormOrder.topFormMap Γ(G, V) L Γ(pullback g g, W) F d) E
  have A1 : TopFormOrder.topFormMap Γ(G, V) L Γ(pullback g g, W) F d
      (TopFormOrder.topFormMap K Γ(G, V) Γ(G, U'') Γ(pullback g g, W) d ω'') =
      TopFormOrder.topFormMap K L Γ(G, U'') F d ω'' :=
    NeronModelInfra.TopFormOrder.topFormMap_topFormMap K Γ(G, V) L Γ(G, U'') Γ(pullback g g, W) F d ω''
  have A2 : TopFormOrder.topFormMap Γ(G, V) L Γ(pullback g g, W) F d
      (TopFormOrder.topFormMap K Γ(G, V) Γ(G, U') Γ(pullback g g, W) d ω') =
      TopFormOrder.topFormMap K L Γ(G, U') F d ω' :=
    NeronModelInfra.TopFormOrder.topFormMap_topFormMap K Γ(G, V) L Γ(G, U') Γ(pullback g g, W) F d ω'
  exact A1.symm.trans (E'.trans A2)


end P2MW.S_GoodReductionJacobian_RelativeGroupLaw_topFormMap_mul_eq_of_forall_topFormMap_appLE_mul_eq
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
