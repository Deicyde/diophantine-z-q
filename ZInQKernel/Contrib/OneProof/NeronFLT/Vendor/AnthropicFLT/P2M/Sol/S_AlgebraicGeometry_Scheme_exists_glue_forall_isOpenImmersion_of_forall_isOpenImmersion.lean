/-
Vendored from anthropics/fermats-last-theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0.
Upstream module: P2M.Sol.S_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion
Modified for the Z-in-Q kernel (2026-11-16, task neron-flt): local import paths are relocated
(`P2M.Util` is the copy published by Cloud Worker 2) and the upstream lakefile options are set
as `set_option` lines after the imports; any other change is marked `-- [port]`.
Original copyright/attribution notices: Vendor/AnthropicFLT/NOTICE.upstream and
Vendor/AnthropicFLT/ATTRIBUTION.upstream.md; license: Vendor/AnthropicFLT/LICENSE.
-/
import Mathlib
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false
set_option autoImplicit false

namespace P2MW.S_AlgebraicGeometry_Scheme_exists_glue_forall_isOpenImmersion_of_forall_isOpenImmersion

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace E86WPS

theorem some_hom_eq {J : Type u} {k i : J} (a : WidePushoutShape.Hom (some k) (some i)) : k = i := by
  match a with
  | .id _ => rfl

end E86WPS

theorem solution
    (W : Scheme.{u}) {ι : Type u} [Nonempty ι] (U : ι → Scheme.{u}) (f : ∀ i, W ⟶ U i)
    [∀ i, IsOpenImmersion (f i)] :
    ∃ (Y : Scheme.{u}) (g : ∀ i, U i ⟶ Y),
      (∀ i, IsOpenImmersion (g i)) ∧
      (∀ i j, f i ≫ g i = f j ≫ g j) ∧
      (⋃ i, Set.range (g i).base = Set.univ) ∧
      (∀ i j, i ≠ j → Set.range (g i).base ∩ Set.range (g j).base = Set.range (f i ≫ g i).base) ∧
      (∀ (Z : Scheme.{u}) (h : ∀ i, U i ⟶ Z), (∀ i j, f i ≫ h i = f j ≫ h j) →
        ∃! k : Y ⟶ Z, ∀ i, g i ≫ k = h i) := by
  classical

  let F : WidePushoutShape ι ⥤ Scheme.{u} := WidePushoutShape.wideSpan W U f
  haveI hF : ∀ {i j : WidePushoutShape ι} (a : i ⟶ j), IsOpenImmersion (F.map a) := by
    rintro i j ⟨⟩
    · exact inferInstanceAs (IsOpenImmersion (𝟙 _))
    · exact inferInstanceAs (IsOpenImmersion (f _))
  let Y : Scheme.{u} := colimit F
  let g : ∀ i, U i ⟶ Y := fun i => colimit.ι F (some i)
  have hgW : ∀ i, f i ≫ g i = colimit.ι F none := fun i => colimit.w F (WidePushoutShape.Hom.init i)
  refine ⟨Y, g, fun i => inferInstanceAs (IsOpenImmersion (colimit.ι F (some i))), ?_, ?_, ?_, ?_⟩
  ·
    intro i j; rw [hgW, hgW]
  ·
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨(_ | i), x, hx⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F y
    · obtain ⟨i⟩ := ‹Nonempty ι›
      refine Set.mem_iUnion.mpr ⟨i, (f i).base x, ?_⟩
      rw [← Scheme.Hom.comp_apply, hgW]; exact hx
    · exact Set.mem_iUnion.mpr ⟨i, x, hx⟩
  ·
    intro i j hij
    ext y; constructor
    · rintro ⟨⟨xi, rfl⟩, ⟨xj, hxj⟩⟩
      obtain ⟨k, fi, fj, x, hfi, hfj⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff F).mp hxj.symm

      rcases k with (_ | k)
      · obtain rfl : fi = WidePushoutShape.Hom.init i := Subsingleton.elim _ _
        refine ⟨x, ?_⟩
        rw [Scheme.Hom.comp_apply]
        exact congrArg (g i).base hfi
      ·
        exact absurd ((E86WPS.some_hom_eq fi).symm.trans (E86WPS.some_hom_eq fj)) hij
    · rintro ⟨w, rfl⟩
      refine ⟨⟨(f i).base w, by rw [← Scheme.Hom.comp_apply]⟩, ⟨(f j).base w, ?_⟩⟩
      rw [← Scheme.Hom.comp_apply, hgW, hgW]
  ·
    intro Z h hh
    obtain ⟨i₀⟩ := ‹Nonempty ι›
    let c : Cocone F := WidePushoutShape.mkCocone (f i₀ ≫ h i₀) h (fun i => hh i i₀)
    refine ⟨colimit.desc F c, fun i => colimit.ι_desc c (some i), ?_⟩
    intro k hk
    apply colimit.hom_ext
    intro j
    erw [colimit.ι_desc]
    rcases j with (_ | i)
    · show colimit.ι F none ≫ k = f i₀ ≫ h i₀
      rw [← hgW i₀]
      exact (Category.assoc _ _ _).trans (congrArg (fun t => f i₀ ≫ t) (hk i₀))
    · exact hk i
