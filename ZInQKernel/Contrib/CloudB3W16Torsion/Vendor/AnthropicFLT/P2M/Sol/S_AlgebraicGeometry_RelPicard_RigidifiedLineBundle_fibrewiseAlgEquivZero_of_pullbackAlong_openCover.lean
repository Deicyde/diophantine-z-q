/-
Vendored from anthropics/fermats-last-theorem @ 6e837e75355538c7f80bab5b956861e86c4eacc2.
Original module: P2M.Sol.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover. Apache-2.0.
Modification notice (CloudB3 Worker16, 2026-11-16): relocated imports; removed
nonessential negative-attribute and reactivation scaffolding; expanded namespace/open/export
helpers to ordinary commands and resolved metadata aliases directly. Mathematical proof
bodies retained, subject to documented Lean 4.35 API adaptations.
Full original notices/credits: NOTICE.upstream, ATTRIBUTION.upstream.md, LICENSE in this vendor root.
-/
import Mathlib
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_NeronModelPropertyBundleCarrier
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelativePicardFunctor
import ZInQKernel.Contrib.CloudB3W16Torsion.Vendor.AnthropicFLT.Definitions.Def_AlgebraicGeometry_RelPicardAlgEquivZeroCut
import ZInQKernel.Contrib.CloudW02Connectedness.Vendor.AnthropicFLT.P2M.Util

set_option backward.isDefEq.respectTransparency false

namespace P2MW.S_AlgebraicGeometry_RelPicard_RigidifiedLineBundle_fibrewiseAlgEquivZero_of_pullbackAlong_openCover

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.RelPicard NeronModelInfra

theorem solution
    (R : Type u) [CommRing R] {C : Scheme.{u}} (c : C ⟶ Spec (CommRingCat.of R))
    (ε : SchemeHomOver (𝟙 (Spec (CommRingCat.of R))) c)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R))
    {ι : Type u} {U : ι → Scheme.{u}} (u : ∀ i, U i ⟶ Spec (CommRingCat.of R))
    (f : ∀ i, SchemeHomOver (u i) t) [∀ i, IsOpenImmersion (f i).1]
    (hf : ∀ x : T, ∃ i, x ∈ Set.range (f i).1.base)
    (M : RigidifiedLineBundle c ε t) (h : ∀ i, FibrewiseAlgEquivZero (M.pullbackAlong (f i))) :
    FibrewiseAlgEquivZero M := by
  intro k _ _ σ

  obtain ⟨i, hi⟩ := hf (σ.base (IsLocalRing.closedPoint k))
  have hrange : Set.range σ.base ⊆ Set.range (f i).1.base := by
    rintro _ ⟨p, rfl⟩
    rw [Subsingleton.elim p (IsLocalRing.closedPoint k)]
    exact hi
  let σ' : Spec (CommRingCat.of k) ⟶ U i := IsOpenImmersion.lift (f i).1 σ hrange
  have hσ' : σ' ≫ (f i).1 = σ := IsOpenImmersion.lift_fac _ _ _

  set ψ : SchemeHomOver (u i) t := f i with hψ
  have w : (pullback.fst (pullback.snd c t) σ ≫ pullback.fst c t) ≫ c =
      (pullback.snd (pullback.snd c t) σ ≫ σ') ≫ u i := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc,
      ← ψ.2, reassoc_of% hσ']
  let a : pullback (pullback.snd c t) σ ⟶ pullback c (u i) := pullback.lift _ _ w
  let e' : pullback (pullback.snd c t) σ ⟶ pullback (pullback.snd c (u i)) σ' :=
    pullback.lift a (pullback.snd _ _) (pullback.lift_snd _ _ _)
  have he' : e' ≫ fibreAt c (u i) σ' = fibreAt c t σ := by
    simp only [e', fibreAt, pullback.lift_snd]
  have ha : a ≫ baseChangeSnd c ψ = pullback.fst (pullback.snd c t) σ := by
    apply pullback.hom_ext
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_fst, Category.comp_id]
    · simp only [a, baseChangeSnd, Category.assoc, pullback.lift_snd, pullback.lift_snd_assoc]
      rw [hσ']
      exact pullback.condition.symm
  have hcomp : (e' ≫ pullback.fst (pullback.snd c (u i)) σ') ≫ baseChangeSnd c ψ =
      pullback.fst (pullback.snd c t) σ := by
    rw [show e' ≫ pullback.fst _ _ = a from pullback.lift_fst _ _ _, ha]
  refine IsAlgEquivZero.of_iso ?_ ((h i k σ').pullback e' he')
  exact (Scheme.Modules.pullbackComp _ _).app _ ≪≫ (Scheme.Modules.pullbackComp _ _).app M.L ≪≫
    (Scheme.Modules.pullbackCongr hcomp).app M.L
