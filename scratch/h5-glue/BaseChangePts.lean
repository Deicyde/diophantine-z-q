import ZInQKernel.HDecomp.Faltings.Leaves

/-! # h5-glue: an ingredient of glue H4a (`ModelHeightBaseChange`): complex points of a base change

`ptsBaseChangeEquiv`: for `𝒢'` isomorphic to `𝒢 ×_{𝓞_L} 𝓞_{L'}` and `τ' : L' → ℂ`, the complex
points `𝒢'(ℂ)_{τ'}` are in bijection with `𝒢(ℂ)_{τ}` for `τ = τ'|_L` (through `e` and the
adjunction `Over.map ⊣ Over.pullback`). Compatibility with the group laws, values of regular
functions and Hodge lattices (the rest of H4a) is NOT proved here. -/

namespace ZInQ.H5Glue

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open NumberField DefFaltings
open PkgI3 (AbVar)

variable {K : Type} [Field K] {A : AbVar K} {L L' : Type} [Field L] [NumberField L] [Algebra K L]
    [Field L'] [NumberField L'] [Algebra K L'] [Algebra L L']

/-- `Spec 𝓞_{L'} → Spec 𝓞_L`. -/
noncomputable abbrev bO (L L' : Type) [Field L] [Field L'] [Algebra L L'] :
    Spec (CommRingCat.of (𝓞 L')) ⟶ Spec (CommRingCat.of (𝓞 L)) :=
  Spec.map (CommRingCat.ofHom (algebraMap (𝓞 L) (𝓞 L')))

omit [NumberField L] [NumberField L'] in
theorem ptC_hom_comp_bO (τ' : L' →+* ℂ) :
    (GroupModel.ptC (L := L') τ').hom ≫ bO L L' =
      (GroupModel.ptC (L := L) (τ'.comp (algebraMap L L'))).hom := by
  simp only [GroupModel.ptC, Over.mk_hom]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

/-- `Over.map b (Spec ℂ via τ') ≅ Spec ℂ via τ'|_L`. -/
noncomputable def ptCMapIso (τ' : L' →+* ℂ) :
    (Over.map (bO L L')).obj (GroupModel.ptC (L := L') τ') ≅
      GroupModel.ptC (L := L) (τ'.comp (algebraMap L L')) :=
  Over.isoMk (Iso.refl _) (by
    simp only [Over.map_obj_hom, Iso.refl_hom]
    erw [Category.id_comp]
    exact (ptC_hom_comp_bO (L := L) τ').symm)

/-- **Complex points of a base change** (proved). -/
noncomputable def ptsBaseChangeEquiv (𝒢 : GroupModel A L) (𝒢' : GroupModel A L')
    (e : 𝒢'.G ≅ (Over.pullback (bO L L')).obj 𝒢.G) (τ' : L' →+* ℂ) :
    𝒢'.Pts τ' ≃ 𝒢.Pts (τ'.comp (algebraMap L L')) :=
  ((Iso.refl (GroupModel.ptC (L := L') τ')).homCongr e).trans
    ((((Over.mapPullbackAdj (bO L L')).homEquiv _ _).symm).trans
      ((ptCMapIso τ').homCongr (Iso.refl 𝒢.G)))

end ZInQ.H5Glue

#print axioms ZInQ.H5Glue.ptsBaseChangeEquiv
