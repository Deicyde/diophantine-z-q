import ZInQKernel.Contrib.CloudW03NeronSurj.Main
import ZInQKernel.Contrib.OneProof.BLRLocalizes

/-! # neron-ext: smooth proper group schemes over a DVR are Néron models (no fibre connectedness)

The proof is CloudW03NeronSurj's port of the Fermat's Last Theorem project's argument
(anthropics/fermats-last-theorem 6e837e75, Apache-2.0; see
`ZInQKernel/Contrib/CloudW03NeronSurj/NOTICE`): properness at codimension one and Weil's extension
argument (BLR §1.2 Prop. 8, §4.4 Thm. 1). The two short top-level steps
`S_GoodReductionJacobian_AbelianSchemePropertyBundle_exists_extension_of_subset_opens.solution` and
`..._genericFibreRestrict_surjective_of_quasiCompact.solution` are restated here with the hypotheses they
actually use (smooth, proper, a relative group law); the bundle's `connectedFibres` field is never used by
the vendored proofs. -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ZInQ.Contrib.CloudW03NeronSurj.FLT

namespace NeronExt

open NeronModelInfra GoodReductionJacobian

section DVR

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]

theorem surj_of_groupLaw {A T : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} [IsProper f]
    [Smooth f] (G : RelativeGroupLaw R f)
    (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t] :
    Function.Surjective (genericFibreRestrict R K f t) := by
  intro uK
  obtain ⟨V, v, hVη, hVs, hcompat⟩ :=
    NeronModelInfra.exists_opens_extension_of_isProper_of_smooth R K f t uK
  obtain ⟨φ, hφ⟩ : ∃ φ : SchemeHomOver t f, V.ι ≫ φ.1 = v.1 := by
    obtain ⟨W, d, hd⟩ :=
      GoodReductionJacobian.RelativeGroupLaw.exists_opens_diagonal_difference_extension R G t V hVη hVs v
    exact GoodReductionJacobian.RelativeGroupLaw.exists_extension_of_diagonal_difference_extension
      R G t V hVη hVs v W d hd
  refine ⟨φ, ?_⟩
  have hrange : Set.range (pullback.fst t (specGenericFibreInclusion R K)).base ⊆ Set.range V.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    apply hVη
    have hc : (pullback.fst t (specGenericFibreInclusion R K) ≫ t).base p =
        (pullback.snd t (specGenericFibreInclusion R K) ≫ specGenericFibreInclusion R K).base p := by
      rw [pullback.condition]
    simp only [Scheme.Hom.comp_base, TopCat.coe_comp, Function.comp_apply] at hc
    rw [hc]
    exact P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_genericFibreRestrict_surjective_of_quasiCompact.NGlue.specGenericFibreInclusion_base_ne_closedPoint R K _
  let l : pullback t (specGenericFibreInclusion R K) ⟶ (V : Scheme.{0}) :=
    IsOpenImmersion.lift V.ι (pullback.fst t (specGenericFibreInclusion R K)) hrange
  have hl : l ≫ V.ι = pullback.fst t (specGenericFibreInclusion R K) := IsOpenImmersion.lift_fac _ _ _
  let n : pullback t (specGenericFibreInclusion R K) ⟶ pullback (V.ι ≫ t) (specGenericFibreInclusion R K) :=
    pullback.lift l (pullback.snd t (specGenericFibreInclusion R K)) (by rw [← Category.assoc, hl, pullback.condition])
  let m : pullback (V.ι ≫ t) (specGenericFibreInclusion R K) ⟶ pullback t (specGenericFibreInclusion R K) :=
    pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _)
      (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm)
  have hnm : n ≫ m = 𝟙 _ := by
    apply pullback.hom_ext
    · simp only [m, n, Category.assoc, pullback.lift_fst, Category.id_comp, pullback.lift_fst_assoc, hl]
    · simp only [m, n, Category.assoc, pullback.lift_snd, Category.comp_id, Category.id_comp]
  have hmφ : m ≫ (genericFibreRestrict R K f t φ).1 = (genericFibreRestrict R K f (V.ι ≫ t) v).1 := by
    apply pullback.hom_ext
    · rw [Category.assoc, genericFibreRestrict_coe_comp_fst, genericFibreRestrict_coe_comp_fst, ← hφ]
      simp only [m, pullback.lift_fst_assoc, Category.assoc]
    · rw [Category.assoc, genericFibreRestrict_coe_comp_snd, genericFibreRestrict_coe_comp_snd]
      simp only [m, pullback.lift_snd, Category.comp_id]
  apply Subtype.ext
  calc (genericFibreRestrict R K f t φ).1
      = (n ≫ m) ≫ (genericFibreRestrict R K f t φ).1 := by rw [hnm, Category.id_comp]
    _ = n ≫ (genericFibreRestrict R K f (V.ι ≫ t) v).1 := by rw [Category.assoc, hmφ]
    _ = (n ≫ m) ≫ uK.1 := by rw [hcompat, Category.assoc]
    _ = uK.1 := by rw [hnm, Category.id_comp]

theorem bundle_of_groupLaw {A : Scheme.{0}} {f : A ⟶ Spec (CommRingCat.of R)} [IsProper f]
    [Smooth f] (G : RelativeGroupLaw R f) : NeronModelPropertyBundle R K f := by
  have hsep : IsSeparated f := inferInstance
  refine ⟨inferInstance, hsep, inferInstance, inferInstance, ?_⟩
  refine neronUniqueExtension_of_forall_quasiCompact R K f fun T t ht hqc => ?_
  haveI := ht
  haveI := hqc
  haveI : Flat t := inferInstance
  exact ⟨genericFibreRestrict_injective_of_flat_of_isSeparated R K f t,
    surj_of_groupLaw R K G t⟩

/-- The vendored Néron bundle gives the printed Néron property (`CToPrinted.IsNeronModelOver`). -/
theorem isNeronModelOver_of_bundle (X : Over (Spec (CommRingCat.of R)))
    (h : NeronModelPropertyBundle R K X.hom) : CToPrinted.IsNeronModelOver R K X := by
  refine ⟨h.smooth, h.separated, h.locallyOfFiniteType, h.quasiCompact, fun Y _ => ?_⟩
  have hb := h.neronMapping Y.left Y.hom inferInstance
  let ιK := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let e1 : (Y ⟶ X) ≃ SchemeHomOver Y.hom X.hom :=
    { toFun := fun f => ⟨f.left, Over.w f⟩
      invFun := fun φ => Over.homMk φ.1 φ.2
      left_inv := fun f => by ext; rfl
      right_inv := fun φ => rfl }
  let e2 : ((Over.pullback ιK).obj Y ⟶ (Over.pullback ιK).obj X) ≃
      SchemeHomOver (pullback.snd Y.hom ιK) (pullback.snd X.hom ιK) :=
    { toFun := fun f => ⟨f.left, Over.w f⟩
      invFun := fun φ => Over.homMk φ.1 φ.2
      left_inv := fun f => by ext; rfl
      right_inv := fun φ => rfl }
  have : (fun f : Y ⟶ X => (Over.pullback ιK).map f) = e2.symm ∘ genericFibreRestrict R K X.hom Y.hom ∘ e1 := by
    funext f
    apply Over.OverMorphism.ext
    show ((Over.pullback ιK).map f).left = (genericFibreRestrict R K X.hom Y.hom ⟨f.left, Over.w f⟩).1
    apply pullback.hom_ext
    · simp only [Over.pullback_map_left, pullback.lift_fst]
      exact (genericFibreRestrict_coe_comp_fst (R := R) (K := K) X.hom Y.hom ⟨f.left, Over.w f⟩).symm
    · simp only [Over.pullback_map_left, pullback.lift_snd]
      exact (genericFibreRestrict_coe_comp_snd (R := R) (K := K) X.hom Y.hom ⟨f.left, Over.w f⟩).symm
  rw [this]
  exact e2.symm.bijective.comp (hb.comp e1.bijective)

/-- **A smooth proper group scheme over a DVR is a Néron model of its generic fibre** (BLR §1.2
Prop. 8 without fibre connectedness; proof from the vendored FLT argument). -/
theorem isNeronModelOver_of_grpObj (X : Over (Spec (CommRingCat.of R))) [GrpObj X] [IsProper X.hom]
    [Smooth X.hom] : CToPrinted.IsNeronModelOver R K X := by
  haveI : GrpObj (Over.mk X.hom) := ‹GrpObj X›
  exact isNeronModelOver_of_bundle R K X (bundle_of_groupLaw R K
    (GoodReductionJacobian.relativeGroupLawOfGrpObj R X.hom))

end DVR

end NeronExt

