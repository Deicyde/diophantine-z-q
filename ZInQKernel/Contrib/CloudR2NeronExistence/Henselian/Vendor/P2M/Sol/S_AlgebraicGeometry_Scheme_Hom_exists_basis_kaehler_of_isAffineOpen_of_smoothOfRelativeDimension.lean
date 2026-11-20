import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension.lean
Original Git blob: 4d0a183486bf18cbf60ca5546704dde4f4a81257
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_PresheafOfModules_ExteriorPower
import ZInQKernel.Contrib.CloudR2NOS.Source.Definitions.Def_AlgebraicGeometry_ModulesDet
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Definitions.Def_AlgebraicGeometry_KaehlerModule
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.Vendor.Theorems.Thm_AlgebraicGeometry_Scheme_Hom_kaehlerToSections_bijective_of_isAffineOpen
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "AlgebraicGeometry CategoryTheory TensorProduct TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace TensorProduct

universe u

namespace KAFrameGC6
h77_bridge_namespace

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))

noncomputable abbrev pmap {W W' : X.Opens} (i : W' ≤ W) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W') : Type u) :=
  ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).map (homOfLE i).op).hom w

noncomputable abbrev res {W' W : X.Opens} (i : W' ≤ W) (s : (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) : Type u)) :
    (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W') : Type u) :=
  (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).val.presheaf.map (homOfLE i).op s

lemma res_toSh {W' W : X.Opens} (i : W' ≤ W) (w : ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op W) : Type u)) :
    res f i ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W w) = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W' (pmap f i w) := by
  have hnat := (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
    (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f))).naturality (homOfLE i).op
  exact (congrArg (fun φ => φ.hom w) hnat).symm

lemma algebraMap_sections_eq {U W : X.Opens} (h : W ≤ U) (a : A) :
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) U
    letI := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) W
    algebraMap A Γ(X, W) a = (X.presheaf.map (homOfLE h).op).hom (algebraMap A Γ(X, U) a) := by
  have := congrArg (fun φ => φ.hom a) ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf f).naturality (homOfLE h).op)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp, CommRingCat.hom_comp] at this
  exact this

theorem main (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ e : Fin d → Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), U),
      ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W),
          ∀ i, b i = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).presheaf.map (homOfLE hW).op (e i) := by
  classical

  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hloc : RingHom.Locally (RingHom.IsStandardSmoothOfRelativeDimension d)
      (f.appLE ⊤ V le_top).hom :=
    HasRingHomProperty.appLE (P := @SmoothOfRelativeDimension d) f inferInstance
      ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
  obtain ⟨s, hs, hP⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).mp hloc

  have hcov : V ≤ ⨆ t : (↑s : Set Γ(X, V)), X.basicOpen (t : Γ(X, V)) :=
    hV.self_le_iSup_basicOpen_iff.mpr hs
  obtain ⟨⟨t, hts⟩, hxt⟩ : ∃ t : (↑s : Set Γ(X, V)), x ∈ X.basicOpen (t : Γ(X, V)) :=
    Opens.mem_iSup.mp (hcov hxV)
  have hU : IsAffineOpen (X.basicOpen t) := hV.basicOpen t
  haveI : IsLocalization.Away t Γ(X, X.basicOpen t) := hV.isLocalization_basicOpen t
  have hstd : RingHom.IsStandardSmoothOfRelativeDimension d
      ((algebraMap Γ(X, V) Γ(X, X.basicOpen t)).comp (f.appLE ⊤ V le_top).hom) :=
    hP t (Finset.mem_coe.mp hts) Γ(X, X.basicOpen t)

  letI algU : Algebra A Γ(X, X.basicOpen t) := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) (X.basicOpen t)
  have hstdU : Algebra.IsStandardSmoothOfRelativeDimension d A Γ(X, X.basicOpen t) := by
    have h1 : (algebraMap Γ(X, V) Γ(X, X.basicOpen t)).comp (f.appLE ⊤ V le_top).hom =
        (f.appLE ⊤ (X.basicOpen t) le_top).hom := by
      change (f.appLE ⊤ V le_top ≫ X.presheaf.map (homOfLE (X.basicOpen_le t)).op).hom = _
      rw [Scheme.Hom.appLE_map]
    rw [h1] at hstd
    have h2 := RingHom.isStandardSmoothOfRelativeDimension_respectsIso.2
      (f.appLE ⊤ (X.basicOpen t) le_top).hom
      (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm hstd
    have h3 : (f.appLE ⊤ (X.basicOpen t) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv.symm.toRingHom =
          ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.constToPresheaf f).app (op (X.basicOpen t))).hom := by
      ext a; rfl
    rw [h3] at h2
    exact h2

  obtain ⟨b₀⟩ : Nonempty (Module.Basis (Fin d) Γ(X, X.basicOpen t) (Ω[Γ(X, X.basicOpen t)⁄A])) := by
    obtain ⟨ι, σ, _, _, P, hP⟩ := hstdU.out
    letI := Fintype.ofFinite ι
    letI := Fintype.ofFinite σ
    have hcard : Fintype.card ((Set.range P.map)ᶜ : Set ι) = d := by
      rw [Fintype.card_compl_set, Set.card_range_of_injective P.map_inj, ← hP,
        Algebra.Presentation.dimension, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact ⟨P.basisKaehler.reindex (Fintype.equivFinOfCardEq hcard)⟩

  refine ⟨X.basicOpen t, hxt, fun i => (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) (X.basicOpen t)
    (show ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen t)) : Type u) from b₀ i), ?_⟩
  intro W hW hWaff
  letI algW : Algebra A Γ(X, W) := (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.sectionsAlgebra f) W
  letI algUW : Algebra Γ(X, X.basicOpen t) Γ(X, W) := (X.presheaf.map (homOfLE hW).op).hom.toAlgebra
  haveI : IsScalarTower A Γ(X, X.basicOpen t) Γ(X, W) :=
    IsScalarTower.of_algebraMap_eq fun a => algebraMap_sections_eq f hW a

  haveI : Algebra.FormallyEtale Γ(X, X.basicOpen t) Γ(X, W) := by
    have hE : RingHom.Etale ((𝟙 X : X ⟶ X).appLE (X.basicOpen t) W hW).hom :=
      HasRingHomProperty.appLE (P := @Etale) (𝟙 X) inferInstance ⟨X.basicOpen t, hU⟩ ⟨W, hWaff⟩ hW
    have hE' : RingHom.Etale (X.presheaf.map (homOfLE hW).op).hom := hE
    exact hE'.formallyEtale
  let κ := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale A Γ(X, X.basicOpen t) Γ(X, W)
  let bW : Module.Basis (Fin d) Γ(X, W) (Ω[Γ(X, W)⁄A]) :=
    (Algebra.TensorProduct.basis Γ(X, W) b₀).map κ
  have hbW : ∀ i, bW i = pmap f hW (show ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerPresheaf f).obj (op (X.basicOpen t)) : Type u) from b₀ i) := by
    intro i
    change κ (Algebra.TensorProduct.basis Γ(X, W) b₀ i) = _
    rw [Algebra.TensorProduct.basis_apply]
    change KaehlerDifferential.mapBaseChange A Γ(X, X.basicOpen t) Γ(X, W) (1 ⊗ₜ b₀ i) = _
    rw [KaehlerDifferential.mapBaseChange_tmul, one_smul]
    rfl

  have hbij := AlgebraicGeometry.Scheme.Hom.kaehlerToSections_bijective_of_isAffineOpen f hWaff
  let τ : (Ω[Γ(X, W)⁄A]) ≃ₗ[Γ(X, W)] (Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W) : Type u) :=
    LinearEquiv.ofBijective ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSectionsₗ f) W) hbij
  refine ⟨bW.map τ, fun i => ?_⟩
  rw [Module.Basis.map_apply, hbW]
  change (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehlerToSections f) W (pmap f hW _) = _
  rw [← res_toSh]
  rfl

end KAFrameGC6

theorem solution
    {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of A))
    (d : ℕ) [SmoothOfRelativeDimension d f] (x : X) :
    ∃ U : X.Opens, x ∈ U ∧ ∃ e : Fin d → Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), U),
      ∀ (W : X.Opens) (hW : W ≤ U), IsAffineOpen W →
        ∃ b : Module.Basis (Fin d) Γ(X, W) Γ((ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f), W),
          ∀ i, b i = (ZInQ.Contrib.CloudR2NeronExistence.Henselian.AlgebraicGeometry.Scheme.Hom.kaehler f).presheaf.map (homOfLE hW).op (e i) :=
  KAFrameGC6.main f d x


end P2MW.S_AlgebraicGeometry_Scheme_Hom_exists_basis_kaehler_of_isAffineOpen_of_smoothOfRelativeDimension
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
