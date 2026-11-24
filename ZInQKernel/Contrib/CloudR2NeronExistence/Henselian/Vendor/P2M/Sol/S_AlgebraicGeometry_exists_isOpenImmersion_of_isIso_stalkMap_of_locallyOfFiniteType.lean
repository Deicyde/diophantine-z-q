import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.Lemmas01
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.MvPolynomialCoeff
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.TensorProductInduction
import ZInQKernel.Contrib.CloudR2NOS.Source.Compat.PresheafOfModulesMonoidal
import ZInQKernel.Contrib.CloudR2NOS.Source.PortUtilExt
/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License, Version 2.0; see LICENSE, NOTICE, ATTRIBUTION.md.
Source: anthropics/fermats-last-theorem@6e837e75355538c7f80bab5b956861e86c4eacc2
Original file: P2M/Sol/S_AlgebraicGeometry_exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType.lean
Original Git blob: f95c6fa7b2076c469f5152ed4e4af7234d8b812c
NOTICE OF MODIFICATION (2026-11-14): isolated namespace/import port to Lean 4.35.0,
Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679; shared H76 declarations are imported,
not redeclared. No constructor hypothesis or conclusion has been weakened.
* Explicitly closed 1 scopes originally left open at EOF.
-/
import Mathlib
import ZInQKernel.Contrib.CloudR2NeronExistence.Henselian.PortUtil

namespace ZInQ.Contrib.CloudR2NeronExistence.Henselian
h77_bridge_namespace

h77_import_shared
h77_open "CategoryTheory.Limits"
h77_open "AlgebraicGeometry CategoryTheory TopologicalSpace"
h77_open "AlgebraicGeometry NeronModelInfra GoodReductionJacobian"
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace P2MW.S_AlgebraicGeometry_exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType
h77_bridge_namespace

set_option autoImplicit false


set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

namespace LocalIsoGC4
h77_bridge_namespace

end LocalIsoGC4

theorem solution
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [IsLocallyNoetherian Y]
    (x : X) [IsIso (f.stalkMap x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsOpenImmersion (U.ι ≫ f) := by
  haveI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f

  obtain ⟨V, hV, g, hg1, hg2⟩ := spread_out_of_isGermInjective (sX := 𝟙 Y) (sY := f) (x := f x) (y := x)
    rfl (inv (f.stalkMap x)) (by simp [TopCat.Presheaf.stalkSpecializes_refl])
  rw [Category.comp_id] at hg2

  let W₀ : X.Opens := f ⁻¹ᵁ V
  have hxW₀ : x ∈ W₀ := hV
  have hrange : Set.range (W₀.ι ≫ f) ⊆ Set.range V.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact w.2
  let fV : (W₀ : Scheme.{u}) ⟶ V := IsOpenImmersion.lift V.ι (W₀.ι ≫ f) hrange
  have hfV : fV ≫ V.ι = W₀.ι ≫ f := IsOpenImmersion.lift_fac _ _ _
  let k : (W₀ : Scheme.{u}) ⟶ X := fV ≫ g

  have hk₀ : W₀.fromSpecStalkOfMem x hxW₀ ≫ k = W₀.fromSpecStalkOfMem x hxW₀ ≫ W₀.ι := by
    have h1 : W₀.fromSpecStalkOfMem x hxW₀ ≫ fV = Spec.map (f.stalkMap x) ≫ V.fromSpecStalkOfMem (f x) hV := by
      rw [← cancel_mono V.ι, Category.assoc, hfV, Scheme.Opens.fromSpecStalkOfMem_ι_assoc, Category.assoc,
        Scheme.Opens.fromSpecStalkOfMem_ι, Scheme.SpecMap_stalkMap_fromSpecStalk]
    change W₀.fromSpecStalkOfMem x hxW₀ ≫ fV ≫ g = _
    rw [← Category.assoc, h1, Category.assoc, ← hg1, ← Category.assoc, ← Spec.map_comp, IsIso.inv_hom_id,
      Spec.map_id, Category.id_comp, Scheme.Opens.fromSpecStalkOfMem_ι]
  have hk : (W₀ : Scheme.{u}).fromSpecStalk ⟨x, hxW₀⟩ ≫ k = (W₀ : Scheme.{u}).fromSpecStalk ⟨x, hxW₀⟩ ≫ W₀.ι := by
    have := hk₀
    simp only [Scheme.Opens.fromSpecStalkOfMem, Category.assoc] at this
    exact (cancel_epi _).mp this

  obtain ⟨W, hxW, hW⟩ := spread_out_unique_of_isGermInjective' k W₀.ι hk

  let jW : (W : Scheme.{u}) ⟶ X := W.ι ≫ W₀.ι
  let U : X.Opens := jW.opensRange
  have hxU : x ∈ U := ⟨⟨⟨x, hxW₀⟩, hxW⟩, rfl⟩
  let V' : (V : Scheme.{u}).Opens := g ⁻¹ᵁ U

  have hkW : W.ι ≫ k = jW := hW
  have hα_range : Set.range (W.ι ≫ fV) ⊆ Set.range V'.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    change g ((W.ι ≫ fV) w) ∈ U
    rw [← Scheme.Hom.comp_apply, Category.assoc]
    change (W.ι ≫ k) w ∈ U
    rw [hkW]
    exact ⟨w, rfl⟩
  let α : (W : Scheme.{u}) ⟶ V' := IsOpenImmersion.lift V'.ι (W.ι ≫ fV) hα_range
  have hα : α ≫ V'.ι = W.ι ≫ fV := IsOpenImmersion.lift_fac _ _ _
  have hβ_range : Set.range (V'.ι ≫ g) ⊆ Set.range jW := by
    rintro _ ⟨v, rfl⟩
    exact v.2
  let β : (V' : Scheme.{u}) ⟶ W := IsOpenImmersion.lift jW (V'.ι ≫ g) hβ_range
  have hβ : β ≫ jW = V'.ι ≫ g := IsOpenImmersion.lift_fac _ _ _

  have hαβ : α ≫ β = 𝟙 _ := by
    rw [← cancel_mono jW, Category.assoc, hβ, ← Category.assoc, hα, Category.assoc, Category.id_comp]
    exact hkW
  have hβα : β ≫ α = 𝟙 _ := by
    rw [← cancel_mono (V'.ι ≫ V.ι), Category.assoc, ← Category.assoc α, hα, Category.assoc, hfV,
      Category.id_comp]
    rw [← Category.assoc W.ι, ← Category.assoc β, hβ, Category.assoc, hg2]
  haveI : IsIso α := ⟨⟨β, hαβ, hβα⟩⟩

  have hUι : U.ι = (IsOpenImmersion.isoOfRangeEq U.ι jW (by rw [Scheme.Opens.range_ι]; rfl)).hom ≫ jW :=
    (IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _).symm
  refine ⟨U, hxU, ?_⟩
  have hjWf : jW ≫ f = α ≫ V'.ι ≫ V.ι := by
    rw [← Category.assoc α, hα]
    simp only [jW, Category.assoc, hfV]
  rw [hUι, Category.assoc, hjWf]
  infer_instance


end P2MW.S_AlgebraicGeometry_exists_isOpenImmersion_of_isIso_stalkMap_of_locallyOfFiniteType
end ZInQ.Contrib.CloudR2NeronExistence.Henselian
