import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen.lean
Original Git blob: 34e9eb3b8ca9f15f9f5a46771c7175c6dcf61bb1
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_IsLocalizedModule_existsUnique_forall_eq_of_span_range_eq_top
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_IsLocalizedModule_of_forall_apply_iotaMulti_eq
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace T0bKS
h77_bridge_namespace

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)

noncomputable abbrev pre : X.PresheafOfModules :=
  (Scheme.Modules.presheafExteriorPower X d).obj (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val

noncomputable def unitD (W : X.Opens) : (⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W)) → Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, W) :=
  fun w => ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f d)).app
    (op W) (show (pre f d).obj (op W) from w)

lemma topToSections_eq (W : X.Opens) (s : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W))) :
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d W s = unitD f d W (exteriorPower.map d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) W) s) := rfl

lemma unitD_add (W : X.Opens) (w w' : ⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W)) :
    unitD f d W (w + w') = unitD f d W w + unitD f d W w' :=
  map_add (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f d)).app
    (op W)).hom _ _

lemma unitD_smul (W : X.Opens) (r : Γ(X, W)) (w : ⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W)) :
    unitD f d W (r • w) = r • unitD f d W w :=
  (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app (pre f d)).app
    (op W)).hom.map_smul r _

noncomputable abbrev resD {W' W : X.Opens} (h : W' ≤ W) (s : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, W)) :
    Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, W') :=
  ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d).presheaf.map (homOfLE h).op s

lemma resD_resD {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (s : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, W₁)) :
    resD f d h₃₂ (resD f d h₂₁ s) = resD f d (h₃₂.trans h₂₁) s := by
  change (((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d).presheaf.map (homOfLE h₂₁).op ≫
    ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d).presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma resD_smul {W' W : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (s : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, W)) :
    resD f d h (r • s) = X.presheaf.map (homOfLE h).op r • resD f d h s :=
  Scheme.Modules.map_smul _ (homOfLE h) r s

noncomputable abbrev preMap {W W' : X.Opens} (h : W' ≤ W) (w : ⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W)) :
    ⋀[Γ(X, W')]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W') :=
  show ⋀[Γ(X, W')]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W') from (pre f d).map (homOfLE h).op (show (pre f d).obj (op W) from w)

lemma preMap_ιMulti {W W' : X.Opens} (h : W' ≤ W) (m : Fin d → Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W)) :
    preMap f d h (exteriorPower.ιMulti _ d m) =
      exteriorPower.ιMulti _ d (fun k => ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).presheaf.map (homOfLE h).op : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) ⟶ _) (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti d (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val (homOfLE h).op m

lemma preMap_preMap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (w : ⋀[Γ(X, W₁)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W₁)) :
    preMap f d h₃₂ (preMap f d h₂₁ w) = preMap f d (h₃₂.trans h₂₁) w := by
  change _ = (pre f d).map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op) (show (pre f d).obj (op W₁) from w)
  rw [PresheafOfModules.map_comp_apply]

lemma resD_unitD {W' W : X.Opens} (h : W' ≤ W) (w : ⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W)) :
    resD f d h (unitD f d W w) = unitD f d W' (preMap f d h w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (pre f d))).naturality (homOfLE h).op
  exact (congrArg (fun φ => φ.hom (show (pre f d).obj (op W) from w)) hnat).symm

lemma unitD_locally_injective {W : X.Opens} (w w' : ⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W))
    (h : unitD f d W w = unitD f d W w') (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ preMap f d i w = preMap f d i w' := by
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre f d).presheaf) (X := op W)
    (show (pre f d).presheaf.obj (op W) from w) (show (pre f d).presheaf.obj (op W) from w') h
  obtain ⟨V, g, hg, hxV⟩ := hmem x hx
  refine ⟨V, g.le, hxV, ?_⟩
  show (pre f d).map (homOfLE g.le).op (show (pre f d).obj (op W) from w) =
    (pre f d).map (homOfLE g.le).op (show (pre f d).obj (op W) from w')
  rw [show homOfLE g.le = g from Subsingleton.elim _ _]
  exact hg

lemma unitD_locally_surjective {W : X.Opens} (c : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, W)) (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ ∃ w : ⋀[Γ(X, V)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), V), unitD f d V w = resD f d i c := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre f d).presheaf) :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (pre f d).presheaf))
  obtain ⟨V, i, ⟨w, hw⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hls W c x hx
  exact ⟨V, i, hxV, show ⋀[Γ(X, V)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), V) from w, hw⟩

lemma sections_eq_of_locally_eq {W : X.Opens} (c c' : Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d, W))
    (h : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ resD f d i c = resD f d i c') : c = c' := by
  choose V i hxV hV using h
  let D : TopCat.Sheaf Ab X.toTopCat := ⟨((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d).presheaf, ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topDifferentials f) d).isSheaf⟩
  exact D.eq_of_locally_eq' (fun p : {x // x ∈ W} => V p.1 p.2) W (fun p => homOfLE (i p.1 p.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) c c' (fun p => hV p.1 p.2)

noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W') : Type u) :=
  ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map (homOfLE i).op).hom w

lemma pmap_pmap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W₁) : Type u)) :
    pmap f h₃₂ (pmap f h₂₁ w) = pmap f (h₃₂.trans h₂₁) w := by
  change _ = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op)).hom w
  rw [PresheafOfModules.map_comp_apply]

lemma res_kaehlerToSections {W' W : X.Opens} (i : W' ≤ W) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val.presheaf.map (homOfLE i).op ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W w) = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f))).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

noncomputable abbrev preK : X.PresheafOfModules := PresheafOfModules.exteriorPower d (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f)

noncomputable abbrev emap {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W))) :
    ⋀[Γ(X, W')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W')) :=
  show ⋀[Γ(X, W')]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W')) from
    (preK f d).map (homOfLE h).op (show (preK f d).obj (op W) from s)

lemma emap_ιMulti {W W' : X.Opens} (h : W' ≤ W) (m : Fin d → ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    emap f d h (exteriorPower.ιMulti _ d m) = exteriorPower.ιMulti _ d (fun k => pmap f h (m k)) :=
  PresheafOfModules.exteriorPower_map_ιMulti d (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f) (homOfLE h).op m

lemma emap_emap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (s : ⋀[Γ(X, W₁)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W₁))) :
    emap f d h₃₂ (emap f d h₂₁ s) = emap f d (h₃₂.trans h₂₁) s := by
  change _ = (preK f d).map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op) (show (preK f d).obj (op W₁) from s)
  rw [PresheafOfModules.map_comp_apply]

lemma emap_add {W W' : X.Opens} (h : W' ≤ W) (s s' : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W))) :
    emap f d h (s + s') = emap f d h s + emap f d h s' :=
  map_add ((preK f d).map (homOfLE h).op).hom _ _

lemma emap_smul {W W' : X.Opens} (h : W' ≤ W) (r : Γ(X, W)) (s : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W))) :
    emap f d h (r • s) = X.presheaf.map (homOfLE h).op r • emap f d h s :=
  (preK f d).map_smul (homOfLE h).op r (show (preK f d).obj (op W) from s)

noncomputable abbrev Λ (W : X.Opens) :
    ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W)) →ₗ[Γ(X, W)] ⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) :=
  exteriorPower.map d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) W)



lemma preMap_Λ {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W))) :
    preMap f d h (Λ f d W s) = Λ f d W' (emap f d h s) := by
  have key : ∀ s ∈ Submodule.span Γ(X, W) (Set.range (exteriorPower.ιMulti Γ(X, W) d
      (M := ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)))),
      preMap f d h (Λ f d W s) = Λ f d W' (emap f d h s) := by
    intro s hs
    induction hs using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨m, rfl⟩ := hy
      rw [emap_ιMulti]
      show preMap f d h (exteriorPower.map d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) W) (exteriorPower.ιMulti _ d m)) =
        exteriorPower.map d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) W') (exteriorPower.ιMulti _ d (fun k => pmap f h (m k)))
      rw [exteriorPower.map_apply_ιMulti, exteriorPower.map_apply_ιMulti, preMap_ιMulti]
      congr 1
      funext k
      exact res_kaehlerToSections f h (m k)
    | zero =>
      have e0 : emap f d h 0 = 0 := map_zero ((preK f d).map (homOfLE h).op).hom
      have p0 : preMap f d h 0 = 0 := map_zero ((pre f d).map (homOfLE h).op).hom
      rw [(Λ f d W).map_zero, e0, (Λ f d W').map_zero, p0]
    | add y z _ _ hy hz =>
      rw [(Λ f d W).map_add y z, emap_add, (Λ f d W').map_add, ← hy, ← hz]
      exact map_add ((pre f d).map (homOfLE h).op).hom _ _
    | smul r y _ hy =>
      rw [(Λ f d W).map_smul r y, emap_smul, (Λ f d W').map_smul, ← hy]
      exact (pre f d).map_smul (homOfLE h).op r (show (pre f d).obj (op W) from Λ f d W y)
  exact key s (by rw [exteriorPower.ιMulti_span]; trivial)

lemma resD_top {W W' : X.Opens} (h : W' ≤ W) (s : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W))) :
    resD f d h ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d W s) = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d W' (emap f d h s) := by
  rw [topToSections_eq, topToSections_eq, resD_unitD, preMap_Λ]

lemma Λ_bijective {W : X.Opens} (hW : IsAffineOpen W) : Function.Bijective (Λ f d W) := by
  have hb : Function.Bijective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) W) :=
    AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hW
  let e := LinearEquiv.ofBijective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) W) hb
  let E : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W)) ≃ₗ[Γ(X, W)] ⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) :=
    LinearEquiv.ofLinear (exteriorPower.map d e.toLinearMap) (exteriorPower.map d e.symm.toLinearMap)
      (by rw [← exteriorPower.map_comp, show e.toLinearMap ∘ₗ e.symm.toLinearMap = LinearMap.id from
            LinearMap.ext fun x => e.apply_symm_apply x, exteriorPower.map_id])
      (by rw [← exteriorPower.map_comp, show e.symm.toLinearMap ∘ₗ e.toLinearMap = LinearMap.id from
            LinearMap.ext fun x => e.symm_apply_apply x, exteriorPower.map_id])
  have : (E : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W)) →ₗ[Γ(X, W)] ⋀[Γ(X, W)]^d Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W)) = Λ f d W := rfl
  rw [← this]
  exact E.bijective

end T0bKS

namespace T0bKS
h77_bridge_namespace

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A)) (d : ℕ)

lemma le_left {W : X.Opens} (a b : Γ(X, W)) : X.basicOpen (a * b) ≤ X.basicOpen a :=
  (X.basicOpen_mul a b).le.trans inf_le_left

lemma le_right {W : X.Opens} (a b : Γ(X, W)) : X.basicOpen (a * b) ≤ X.basicOpen b :=
  (X.basicOpen_mul a b).le.trans inf_le_right



theorem glue {W : X.Opens} (hW : IsAffineOpen W) {ι : Type u} [Finite ι] (t : ι → Γ(X, W))
    (ht : Ideal.span (Set.range t) = ⊤)
    (m : ∀ i, ⋀[Γ(X, X.basicOpen (t i))]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen (t i)))))
    (hm : ∀ i j, emap f d (le_left (t i) (t j)) (m i) = emap f d (le_right (t i) (t j)) (m j)) :
    ∃! s : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W)), ∀ i, emap f d (X.basicOpen_le (t i)) s = m i := by
  classical
  letI algW : Algebra A Γ(X, W) := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) W
  letI algD : ∀ g : Γ(X, W), Algebra A Γ(X, X.basicOpen g) := fun g => (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) (X.basicOpen g)
  have tower : ∀ g : Γ(X, W), IsScalarTower A Γ(X, W) Γ(X, X.basicOpen g) := by
    intro g
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf f).naturality (homOfLE (X.basicOpen_le g)).op
    have h := congrArg (fun φ => φ.hom a) this
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp,
      Function.comp_apply] at h
    exact h
  haveI := tower
  haveI hloc : ∀ g : Γ(X, W), IsLocalization.Away g Γ(X, X.basicOpen g) := fun g => hW.isLocalization_basicOpen g

  let κ : ∀ g : Γ(X, W), Ω[Γ(X, W)⁄A] →ₗ[Γ(X, W)] Ω[Γ(X, X.basicOpen g)⁄A] :=
    fun g => KaehlerDifferential.map A A Γ(X, W) Γ(X, X.basicOpen g)
  have hκ : ∀ (g : Γ(X, W)) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)),
      pmap f (X.basicOpen_le g) w = κ g (show Ω[Γ(X, W)⁄A] from w) := fun g w => rfl
  haveI hκloc : ∀ g : Γ(X, W), IsLocalizedModule (Submonoid.powers g) (κ g) := fun g =>
    KaehlerDifferential.isLocalizedModule_map A Γ(X, W) Γ(X, X.basicOpen g) (Submonoid.powers g)

  have towerΩ : ∀ g : Γ(X, W), IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) (Ω[Γ(X, X.basicOpen g)⁄A]) :=
    fun g => KaehlerDifferential.isScalarTower_of_tower A Γ(X, X.basicOpen g)
  haveI := towerΩ
  letI modN : ∀ g : Γ(X, W), Module Γ(X, W) ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen g))) :=
    fun g => (inferInstance : Module Γ(X, W) (Ω[Γ(X, X.basicOpen g)⁄A]))
  haveI towerN : ∀ g : Γ(X, W),
      IsScalarTower Γ(X, W) Γ(X, X.basicOpen g) ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen g))) :=
    fun g => towerΩ g

  have emap_smulW : ∀ {a b : Γ(X, W)} (hab : X.basicOpen b ≤ X.basicOpen a) (r : Γ(X, W))
      (s : ⋀[Γ(X, X.basicOpen a)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen a)))),
      emap f d hab (r • s) = r • emap f d hab s := by
    intro a b hab r s
    rw [← algebraMap_smul Γ(X, X.basicOpen a) r s, emap_smul,
      ← algebraMap_smul Γ(X, X.basicOpen b) r (emap f d hab s)]
    congr 1
    change (X.presheaf.map (homOfLE (X.basicOpen_le a)).op ≫ X.presheaf.map (homOfLE hab).op).hom r = _
    rw [← Functor.map_comp]
    rfl
  let E : ∀ g : Γ(X, W), ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W)) →ₗ[Γ(X, W)]
      ⋀[Γ(X, X.basicOpen g)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen g))) := fun g =>
    { toFun := fun s => emap f d (X.basicOpen_le g) s
      map_add' := fun s s' => emap_add f d _ s s'
      map_smul' := fun r s => by
        rw [RingHom.id_apply, ← algebraMap_smul Γ(X, X.basicOpen g) r (emap f d _ s)]
        exact emap_smul f d _ r s }
  haveI hEloc : ∀ g : Γ(X, W), IsLocalizedModule (Submonoid.powers g) (E g) := fun g => by
    haveI := towerΩ g
    haveI := hκloc g
    haveI := hloc g
    exact @IsLocalizedModule.of_forall_apply_iotaMulti_eq _ _ (Submonoid.powers g) Γ(X, X.basicOpen g)
      _ _ _ _ _ _ _ _ _ _ (towerΩ g) (κ g) (hκloc g) d (E g)
      (fun mm => by
        show emap f d (X.basicOpen_le g) (exteriorPower.ιMulti _ d mm) = _
        rw [emap_ιMulti]
        rfl)
  let ρ : ∀ i j, ⋀[Γ(X, X.basicOpen (t i))]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen (t i)))) →ₗ[Γ(X, W)]
      ⋀[Γ(X, X.basicOpen (t i * t j))]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen (t i * t j)))) := fun i j =>
    { toFun := fun s => emap f d (le_left (t i) (t j)) s
      map_add' := fun s s' => emap_add f d _ s s'
      map_smul' := fun r s => emap_smulW (le_left (t i) (t j)) r s }
  let ρ' : ∀ i j, ⋀[Γ(X, X.basicOpen (t j))]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen (t j)))) →ₗ[Γ(X, W)]
      ⋀[Γ(X, X.basicOpen (t i * t j))]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen (t i * t j)))) := fun i j =>
    { toFun := fun s => emap f d (le_right (t i) (t j)) s
      map_add' := fun s s' => emap_add f d _ s s'
      map_smul' := fun r s => emap_smulW (le_right (t i) (t j)) r s }
  have hρ : ∀ i j, (ρ i j).comp (E (t i)) = E (t i * t j) := by
    intro i j
    refine LinearMap.ext fun s => ?_
    show emap f d (le_left (t i) (t j)) (emap f d (X.basicOpen_le (t i)) s) = emap f d (X.basicOpen_le (t i * t j)) s
    rw [emap_emap]
  have hρ' : ∀ i j, (ρ' i j).comp (E (t j)) = E (t i * t j) := by
    intro i j
    refine LinearMap.ext fun s => ?_
    show emap f d (le_right (t i) (t j)) (emap f d (X.basicOpen_le (t j)) s) = emap f d (X.basicOpen_le (t i * t j)) s
    rw [emap_emap]
  exact IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top t ht
    (fun i => E (t i)) (fun i j => E (t i * t j)) ρ ρ' hρ hρ' m (fun i j => hm i j)

lemma exists_finite_family {W : X.Opens} (hW : IsAffineOpen W) (Q : Γ(X, W) → Prop)
    (h : ∀ x ∈ W, ∃ g : Γ(X, W), x ∈ X.basicOpen g ∧ Q g) :
    ∃ (T : Finset Γ(X, W)), Ideal.span (Set.range fun s : ↥T => (s : Γ(X, W))) = ⊤ ∧ ∀ s : ↥T, Q s := by
  classical
  choose g hxg hQ using h
  have hspan : Ideal.span (Set.range fun p : {x // x ∈ W} => g p.1 p.2) = ⊤ := by
    rw [← hW.iSup_basicOpen_eq_self_iff]
    refine le_antisymm (iSup_le fun s => X.basicOpen_le _) fun x hx => ?_
    exact Opens.mem_iSup.mpr ⟨⟨g x hx, ⟨x, hx⟩, rfl⟩, hxg x hx⟩
  obtain ⟨T, hTsub, hT1⟩ := Submodule.mem_span_finite_of_mem_span
    ((Ideal.eq_top_iff_one _).mp hspan)
  refine ⟨T, ?_, fun s => ?_⟩
  · rw [Ideal.eq_top_iff_one]
    have : Set.range (fun s : ↥T => (s : Γ(X, W))) = (T : Set Γ(X, W)) := by
      ext y; simp
    rw [this]; exact hT1
  · obtain ⟨⟨x, hx⟩, hgx⟩ := hTsub s.2
    rw [← hgx]; exact hQ x hx



theorem top_injective {W : X.Opens} (hW : IsAffineOpen W) : Function.Injective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d W) := by
  classical
  intro s s' h
  have key : ∀ x ∈ W, ∃ g : Γ(X, W), x ∈ X.basicOpen g ∧
      emap f d (X.basicOpen_le g) s = emap f d (X.basicOpen_le g) s' := by
    intro x hx
    rw [topToSections_eq, topToSections_eq] at h
    obtain ⟨V, i, hxV, hV⟩ := unitD_locally_injective f d _ _ h x hx
    obtain ⟨g, hgV, hxg⟩ := hW.exists_basicOpen_le ⟨x, hxV⟩ hx
    refine ⟨g, hxg, (Λ_bijective f d (hW.basicOpen g)).1 ?_⟩
    have e1 : ∀ s₁ : ⋀[Γ(X, W)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W)),
        Λ f d (X.basicOpen g) (emap f d (X.basicOpen_le g) s₁) = preMap f d hgV (preMap f d i (Λ f d W s₁)) := by
      intro s₁; rw [preMap_preMap, preMap_Λ]
    rw [e1, e1, hV]
  obtain ⟨T, hT, hTQ⟩ := exists_finite_family hW _ key
  obtain ⟨s₀, -, huniq⟩ := glue f d hW (fun u : ↥T => (u : Γ(X, W))) hT
    (fun u => emap f d (X.basicOpen_le _) s) (fun i j => by rw [emap_emap, emap_emap])
  have e1 : s = s₀ := huniq s (fun i => rfl)
  have e2 : s' = s₀ := huniq s' (fun i => (hTQ i).symm)
  rw [e1, e2]



theorem top_surjective {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U) := by
  classical
  intro c
  have key : ∀ x ∈ U, ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧
      ∃ s : ⋀[Γ(X, X.basicOpen g)]^d ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen g))),
        (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d (X.basicOpen g) s = resD f d (X.basicOpen_le g) c := by
    intro x hx
    obtain ⟨V, i, hxV, w, hw⟩ := unitD_locally_surjective f d c x hx
    obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    obtain ⟨s, hs⟩ := (Λ_bijective f d (hU.basicOpen g)).2 (preMap f d hgV w)
    refine ⟨g, hxg, s, ?_⟩
    rw [topToSections_eq, hs, ← resD_unitD, hw, resD_resD]
  obtain ⟨T, hT, hTQ⟩ := exists_finite_family hU _ key
  choose m hm using hTQ
  have hcompat : ∀ i j : ↥T, emap f d (le_left (i : Γ(X, U)) j) (m i) = emap f d (le_right (i : Γ(X, U)) j) (m j) := by
    intro i j
    apply top_injective f d (hU.basicOpen ((i : Γ(X, U)) * j))
    rw [← resD_top, ← resD_top, hm i, hm j, resD_resD, resD_resD]
  obtain ⟨s₀, hs₀, -⟩ := glue f d hU (fun u : ↥T => (u : Γ(X, U))) hT m hcompat
  refine ⟨s₀, ?_⟩
  have hcov : ∀ x ∈ U, ∃ u : ↥T, x ∈ X.basicOpen (u : Γ(X, U)) := by
    intro x hx
    have hsup : ⨆ u : ↥(Set.range fun u : ↥T => (u : Γ(X, U))), X.basicOpen (u : Γ(X, U)) = U :=
      hU.iSup_basicOpen_eq_self_iff.mpr hT
    have hx' : x ∈ (⨆ u : ↥(Set.range fun u : ↥T => (u : Γ(X, U))), X.basicOpen (u : Γ(X, U))) := by
      rw [hsup]; exact hx
    obtain ⟨⟨_, ⟨u, rfl⟩⟩, hu⟩ := Opens.mem_iSup.mp hx'
    exact ⟨u, hu⟩
  apply sections_eq_of_locally_eq f d
  intro x hx
  obtain ⟨u, hu⟩ := hcov x hx
  refine ⟨X.basicOpen (u : Γ(X, U)), X.basicOpen_le _, hu, ?_⟩
  rw [resD_top, hs₀ u, hm u]

end T0bKS

theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.topToSections f) d U) := by
  exact ⟨T0bKS.top_injective f d hU, T0bKS.top_surjective f d hU⟩


end P2MW.S_AlgebraicGeometry_Scheme_Hom_topToSections_bijective_of_isAffineOpen
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
