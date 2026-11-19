import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen.lean
Original Git blob: 3e0fe545311159740c5c8a6321483980e81bbe54
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
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace

universe u

namespace T0aKS
h77_bridge_namespace

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W') : Type u) :=
  ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map (homOfLE i).op).hom w

noncomputable abbrev res {W' W : X.Opens} (i : W' ≤ W) (s : (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) : Type u)) :
    (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W') : Type u) :=
  (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val.presheaf.map (homOfLE i).op s

lemma pmap_pmap {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂)
    (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W₁) : Type u)) :
    pmap f h₃₂ (pmap f h₂₁ w) = pmap f (h₃₂.trans h₂₁) w := by
  change _ = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map ((homOfLE h₂₁).op ≫ (homOfLE h₃₂).op)).hom w
  rw [PresheafOfModules.map_comp_apply]

lemma res_res {W₁ W₂ W₃ : X.Opens} (h₂₁ : W₂ ≤ W₁) (h₃₂ : W₃ ≤ W₂) (s : (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W₁) : Type u)) :
    res f h₃₂ (res f h₂₁ s) = res f (h₃₂.trans h₂₁) s := by
  change ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val.presheaf.map (homOfLE h₂₁).op ≫ (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val.presheaf.map (homOfLE h₃₂).op) s = _
  rw [← Functor.map_comp]
  rfl

lemma res_toSh {W' W : X.Opens} (i : W' ≤ W) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    res f i ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W w) = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f))).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

lemma toSh_locally_injective {W : X.Opens} (w w' : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u))
    (h : (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W w = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W w') (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ pmap f i w = pmap f i w' := by
  have hli : Presheaf.IsLocallyInjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).presheaf) := inferInstance
  have hmem := Presheaf.equalizerSieve_mem (Opens.grothendieckTopology X)
    (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).presheaf) (X := op W)
    (show (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).presheaf.obj (op W) from w) (show (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).presheaf.obj (op W) from w') h
  obtain ⟨V, g, hg, hxV⟩ := hmem x hx
  refine ⟨V, g.le, hxV, ?_⟩
  show ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map (homOfLE g.le).op).hom w = ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map (homOfLE g.le).op).hom w'
  rw [show homOfLE g.le = g from Subsingleton.elim _ _]
  exact hg

lemma toSh_locally_surjective {W : X.Opens} (c : (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) : Type u)) (x : X) (hx : x ∈ W) :
    ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ ∃ w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op V) : Type u),
      (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) V w = res f i c := by
  have hls : TopCat.Presheaf.IsLocallySurjective
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).presheaf) :=
    (inferInstance : CategoryTheory.Presheaf.IsLocallySurjective (Opens.grothendieckTopology X)
      (CategoryTheory.toSheafify (Opens.grothendieckTopology X) (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).presheaf))
  obtain ⟨V, i, ⟨w, hw⟩, hxV⟩ := (TopCat.Presheaf.isLocallySurjective_iff _).mp hls W c x hx
  exact ⟨V, i, hxV, show ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op V) : Type u) from w, hw⟩

lemma sections_eq_of_locally_eq {W : X.Opens} (c c' : (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) : Type u))
    (h : ∀ x ∈ W, ∃ (V : X.Opens) (i : V ≤ W), x ∈ V ∧ res f i c = res f i c') : c = c' := by
  choose V i hxV hV using h
  let D : TopCat.Sheaf Ab X.toTopCat := ⟨(ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val.presheaf, (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).isSheaf⟩
  exact D.eq_of_locally_eq' (fun p : {x // x ∈ W} => V p.1 p.2) W (fun p => homOfLE (i p.1 p.2))
    (fun x hx => Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hxV x hx⟩) c c' (fun p => hV p.1 p.2)

end T0aKS

namespace T0aKS
h77_bridge_namespace

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

lemma le_left {W : X.Opens} (a b : Γ(X, W)) : X.basicOpen (a * b) ≤ X.basicOpen a :=
  (X.basicOpen_mul a b).le.trans inf_le_left

lemma le_right {W : X.Opens} (a b : Γ(X, W)) : X.basicOpen (a * b) ≤ X.basicOpen b :=
  (X.basicOpen_mul a b).le.trans inf_le_right



theorem glue {W : X.Opens} (hW : IsAffineOpen W) {ι : Type u} [Finite ι] (t : ι → Γ(X, W))
    (ht : Ideal.span (Set.range t) = ⊤)
    (m : ∀ i, ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen (t i))) : Type u))
    (hm : ∀ i j, pmap f (le_left (t i) (t j)) (m i) = pmap f (le_right (t i) (t j)) (m j)) :
    ∃! w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u), ∀ i, pmap f (X.basicOpen_le (t i)) w = m i := by
  classical
  letI algW : Algebra A Γ(X, W) := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) W
  letI algD : ∀ g : Γ(X, W), Algebra A Γ(X, X.basicOpen g) := fun g => (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) (X.basicOpen g)
  have tower : ∀ g : Γ(X, W), IsScalarTower A Γ(X, W) Γ(X, X.basicOpen g) := by
    intro g
    refine IsScalarTower.of_algebraMap_eq fun a => ?_
    have := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf f).naturality (homOfLE (X.basicOpen_le g)).op
    have h := congrArg (fun φ => φ.hom a) this
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp,
      RingHom.coe_comp, Function.comp_apply] at h
    exact h
  haveI := tower
  haveI hloc : ∀ g : Γ(X, W), IsLocalization.Away g Γ(X, X.basicOpen g) := fun g => hW.isLocalization_basicOpen g

  let κ : ∀ g : Γ(X, W), Ω[Γ(X, W)⁄A] →ₗ[Γ(X, W)] Ω[Γ(X, X.basicOpen g)⁄A] :=
    fun g => KaehlerDifferential.map A A Γ(X, W) Γ(X, X.basicOpen g)
  have hκ : ∀ (g : Γ(X, W)) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)),
      pmap f (X.basicOpen_le g) w = κ g (show Ω[Γ(X, W)⁄A] from w) := fun g w => rfl
  haveI hκloc : ∀ g : Γ(X, W), IsLocalizedModule (Submonoid.powers g) (κ g) := fun g =>
    KaehlerDifferential.isLocalizedModule_map A Γ(X, W) Γ(X, X.basicOpen g) (Submonoid.powers g)

  have smul_def : ∀ (g : Γ(X, W)) (r : Γ(X, W)) (n : Ω[Γ(X, X.basicOpen g)⁄A]),
      r • n = (X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom r • n := fun g r n => rfl
  have pmap_smul : ∀ {a b : Γ(X, W)} (hab : X.basicOpen b ≤ X.basicOpen a) (r : Γ(X, W))
      (n : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen a)) : Type u)),
      pmap f hab ((show Ω[Γ(X, X.basicOpen a)⁄A] → ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen a)) : Type u) from id)
        (r • (show Ω[Γ(X, X.basicOpen a)⁄A] from n))) =
      (show Ω[Γ(X, X.basicOpen b)⁄A] → ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen b)) : Type u) from id)
        (r • (show Ω[Γ(X, X.basicOpen b)⁄A] from pmap f hab n)) := by
    intro a b hab r n
    have hms := PresheafOfModules.map_smul (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f) (homOfLE hab).op
      ((X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom r) n
    refine hms.trans ?_
    show (X.presheaf.map (homOfLE (X.basicOpen_le a)).op ≫ X.presheaf.map (homOfLE hab).op).hom r •
        pmap f hab n = (X.presheaf.map (homOfLE (X.basicOpen_le b)).op).hom r • pmap f hab n
    rw [← Functor.map_comp]
    rfl
  let ρ : ∀ i j, Ω[Γ(X, X.basicOpen (t i))⁄A] →ₗ[Γ(X, W)] Ω[Γ(X, X.basicOpen (t i * t j))⁄A] := fun i j =>
    { toFun := fun n => show Ω[Γ(X, X.basicOpen (t i * t j))⁄A] from pmap f (le_left (t i) (t j)) n
      map_add' := fun n n' => map_add ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map (homOfLE (le_left (t i) (t j))).op).hom n n'
      map_smul' := fun r n => pmap_smul (le_left (t i) (t j)) r n }
  let ρ' : ∀ i j, Ω[Γ(X, X.basicOpen (t j))⁄A] →ₗ[Γ(X, W)] Ω[Γ(X, X.basicOpen (t i * t j))⁄A] := fun i j =>
    { toFun := fun n => show Ω[Γ(X, X.basicOpen (t i * t j))⁄A] from pmap f (le_right (t i) (t j)) n
      map_add' := fun n n' => map_add ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map (homOfLE (le_right (t i) (t j))).op).hom n n'
      map_smul' := fun r n => pmap_smul (le_right (t i) (t j)) r n }
  have hρ : ∀ i j, (ρ i j).comp (κ (t i)) = κ (t i * t j) := by
    intro i j
    refine LinearMap.ext fun w => ?_
    show pmap f (le_left (t i) (t j)) (pmap f (X.basicOpen_le (t i)) w) = pmap f (X.basicOpen_le (t i * t j)) w
    rw [pmap_pmap]
  have hρ' : ∀ i j, (ρ' i j).comp (κ (t j)) = κ (t i * t j) := by
    intro i j
    refine LinearMap.ext fun w => ?_
    show pmap f (le_right (t i) (t j)) (pmap f (X.basicOpen_le (t j)) w) = pmap f (X.basicOpen_le (t i * t j)) w
    rw [pmap_pmap]
  have key := IsLocalizedModule.existsUnique_forall_eq_of_span_range_eq_top t ht
    (fun i => κ (t i)) (fun i j => κ (t i * t j)) ρ ρ' hρ hρ'
    (fun i => show Ω[Γ(X, X.basicOpen (t i))⁄A] from m i) (fun i j => hm i j)
  exact key

end T0aKS

namespace T0aKS
h77_bridge_namespace

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

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



theorem toSh_injective {W : X.Opens} (hW : IsAffineOpen W) : Function.Injective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W) := by
  classical
  intro w w' h
  have key : ∀ x ∈ W, ∃ g : Γ(X, W), x ∈ X.basicOpen g ∧
      pmap f (X.basicOpen_le g) w = pmap f (X.basicOpen_le g) w' := by
    intro x hx
    obtain ⟨V, i, hxV, hV⟩ := toSh_locally_injective f w w' h x hx
    obtain ⟨g, hgV, hxg⟩ := hW.exists_basicOpen_le ⟨x, hxV⟩ hx
    refine ⟨g, hxg, ?_⟩
    rw [← pmap_pmap f i hgV w, ← pmap_pmap f i hgV w', hV]
  obtain ⟨T, hT, hTQ⟩ := exists_finite_family hW _ key
  obtain ⟨w₀, -, huniq⟩ := glue f hW (fun s : ↥T => (s : Γ(X, W))) hT
    (fun s => pmap f (X.basicOpen_le _) w) (fun i j => by rw [pmap_pmap, pmap_pmap])
  have e1 : w = w₀ := huniq w (fun i => rfl)
  have e2 : w' = w₀ := huniq w' (fun i => (hTQ i).symm)
  rw [e1, e2]



theorem toSh_surjective {U : X.Opens} (hU : IsAffineOpen U) : Function.Surjective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) U) := by
  classical
  intro c
  have key : ∀ x ∈ U, ∃ g : Γ(X, U), x ∈ X.basicOpen g ∧
      ∃ w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen g)) : Type u),
        (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) (X.basicOpen g) w = res f (X.basicOpen_le g) c := by
    intro x hx
    obtain ⟨V, i, hxV, w, hw⟩ := toSh_locally_surjective f c x hx
    obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
    refine ⟨g, hxg, pmap f hgV w, ?_⟩
    rw [← res_toSh, hw, res_res]
  obtain ⟨T, hT, hTQ⟩ := exists_finite_family hU _ key
  choose m hm using hTQ

  have hcompat : ∀ i j : ↥T, pmap f (le_left (i : Γ(X, U)) j) (m i) = pmap f (le_right (i : Γ(X, U)) j) (m j) := by
    intro i j
    apply toSh_injective f (hU.basicOpen ((i : Γ(X, U)) * j))
    rw [← res_toSh, ← res_toSh, hm i, hm j, res_res, res_res]
  obtain ⟨w₀, hw₀, -⟩ := glue f hU (fun s : ↥T => (s : Γ(X, U))) hT m hcompat
  refine ⟨w₀, ?_⟩

  have hcov : ∀ x ∈ U, ∃ s : ↥T, x ∈ X.basicOpen (s : Γ(X, U)) := by
    intro x hx
    have hsup : ⨆ s : ↥(Set.range fun s : ↥T => (s : Γ(X, U))), X.basicOpen (s : Γ(X, U)) = U :=
      hU.iSup_basicOpen_eq_self_iff.mpr hT
    have hx' : x ∈ (⨆ s : ↥(Set.range fun s : ↥T => (s : Γ(X, U))), X.basicOpen (s : Γ(X, U))) := by
      rw [hsup]; exact hx
    obtain ⟨⟨_, ⟨s, rfl⟩⟩, hs⟩ := Opens.mem_iSup.mp hx'
    exact ⟨s, hs⟩
  apply sections_eq_of_locally_eq f
  intro x hx
  obtain ⟨s, hs⟩ := hcov x hx
  refine ⟨X.basicOpen (s : Γ(X, U)), X.basicOpen_le _, hs, ?_⟩
  rw [res_toSh, hw₀ s, hm s]

end T0aKS


theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) U) := by
  exact ⟨T0aKS.toSh_injective f hU, T0aKS.toSh_surjective f hU⟩


end P2MW.S_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
