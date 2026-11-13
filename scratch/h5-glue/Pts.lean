import ZInQKernel.HDecomp.Faltings.Leaves

namespace ZInQ.H5Glue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L : Type} [Field L] [NumberField L] [Algebra K L]

noncomputable abbrev jL (L : Type) [Field L] [NumberField L] :
    Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) L))

/-- `ptC τ = Over.map (jL L) (Spec ℂ over L via τ)`. -/
noncomputable def ptCIso (τ : L →+* ℂ) :
    GroupModel.ptC (L := L) τ ≅ (Over.map (jL L)).obj (Over.mk (Spec.map (CommRingCat.ofHom τ))) :=
  Over.isoMk (Iso.refl _) (by
    simp only [GroupModel.ptC, Over.mk_hom, Over.map_obj_hom, Iso.refl_hom, Category.id_comp]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp])

/-- Complex points of a group model are complex points of its generic fibre. -/
noncomputable def ptsEquiv (𝒢 : GroupModel A L) (τ : L →+* ℂ) :
    𝒢.Pts τ ≃ (Over.mk (Spec.map (CommRingCat.ofHom τ)) ⟶ (Over.pullback (jL L)).obj 𝒢.G) :=
  ((ptCIso τ).homCongr (Iso.refl 𝒢.G)).trans ((Over.mapPullbackAdj (jL L)).homEquiv _ _)

theorem ptsEquiv_comp (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G) (τ : L →+* ℂ) (p : 𝒢.Pts τ) :
    ptsEquiv 𝒩 τ (p ≫ f) = ptsEquiv 𝒢 τ p ≫ (Over.pullback (jL L)).map f := by
  simp only [ptsEquiv, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id]
  rw [← Adjunction.homEquiv_naturality_right, Category.assoc]

/-- **A morphism of group models that is an isomorphism on generic fibres is bijective on
complex points** (at every `τ : L → ℂ`). -/
theorem pts_comp_bijective (𝒢 𝒩 : GroupModel A L) (f : 𝒢.G ⟶ 𝒩.G)
    [IsIso ((Over.pullback (jL L)).map f)] (τ : L →+* ℂ) :
    Function.Bijective (fun p : 𝒢.Pts τ => p ≫ f) := by
  have key : (fun p : 𝒢.Pts τ => p ≫ f) = (ptsEquiv 𝒩 τ).symm ∘
      (fun q => q ≫ (Over.pullback (jL L)).map f) ∘ ptsEquiv 𝒢 τ := by
    funext p
    simp only [Function.comp, ← ptsEquiv_comp, Equiv.symm_apply_apply]
  rw [key]
  refine (Equiv.bijective _).comp (Function.Bijective.comp ?_ (Equiv.bijective _))
  exact ⟨fun a b h => (cancel_mono _).mp h, fun c => ⟨c ≫ inv ((Over.pullback (jL L)).map f),
    by simp⟩⟩

end ZInQ.H5Glue

#print axioms ZInQ.H5Glue.pts_comp_bijective
