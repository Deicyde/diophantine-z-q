/-
neron-flt (2026-11-16): Néron models of abelian varieties over henselian discrete valuation rings, in the
chain's language (`CToPrinted.IsNeronModelOver`, `PkgI3.AbVar`), from the vendored Fermat's Last Theorem
development (anthropics/fermats-last-theorem @ 6e837e75, Apache-2.0; `Vendor/AnthropicFLT/`, see its NOTICE).

`relativeGroupLawOfGrpObj` is CloudW03NeronSurj's `Basic.lean` definition (same source, same licence) restated
over the unwrapped vendored names; `isNeronModelOver_of_bundle'` is neron-ext's `NeronExt.isNeronModelOver_of_bundle`
restated likewise.
-/
import ZInQKernel.Contrib.OneProof.NeronFLT.Vendor.AnthropicFLT.Theorems.Thm_GoodReductionJacobian_RelativeGroupLaw_exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
import ZInQKernel.Contrib.OneProof.NeronSchemeExtensionExists

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace NeronFLT

open _root_.NeronModelInfra _root_.GoodReductionJacobian

universe u

/-- The source's relative group law, from a group object (CloudW03NeronSurj `Basic.lean`). -/
def relativeGroupLawOfGrpObj (R : Type u) [CommRing R] {A : Scheme.{u}}
    (f : A ⟶ Spec (CommRingCat.of R)) [GrpObj (Over.mk f)] : RelativeGroupLaw R f where
  mul {T} t x y :=
    overHomToSchemeHomOver (schemeHomOverToOverHom x * schemeHomOverToOverHom y)
  one {T} t := overHomToSchemeHomOver (1 : Over.mk t ⟶ Over.mk f)
  inv {T} t x := overHomToSchemeHomOver (schemeHomOverToOverHom x)⁻¹
  mul_assoc {T} t x y z := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [mul_assoc]
  one_mul {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [one_mul, overHomToSchemeHomOver_schemeHomOverToOverHom]
  mul_one {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [mul_one, overHomToSchemeHomOver_schemeHomOverToOverHom]
  inv_mul_cancel {T} t x := by
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [inv_mul_cancel]
  mul_natural {T T'} t t' ψ hψ x y := by
    have key : ∀ z : SchemeHomOver t f,
        schemeHomOverComp ψ hψ z = overHomToSchemeHomOver
          ((Over.homMk ψ (by simpa using hψ) : Over.mk t' ⟶ Over.mk t) ≫
            schemeHomOverToOverHom z) := by
      intro z
      apply Subtype.ext
      simp
    rw [key, key, key]
    simp only [schemeHomOverToOverHom_overHomToSchemeHomOver]
    rw [MonObj.comp_mul]

section DVR

variable (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]

/-- The vendored Néron bundle gives the printed Néron property (`CToPrinted.IsNeronModelOver`);
neron-ext's `NeronExt.isNeronModelOver_of_bundle` over the unwrapped vendored names. -/
theorem isNeronModelOver_of_bundle' (X : Over (Spec (CommRingCat.of R)))
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
  have : (fun f : Y ⟶ X => (Over.pullback ιK).map f) =
      e2.symm ∘ genericFibreRestrict R K X.hom Y.hom ∘ e1 := by
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

/-- **Néron models of abelian varieties over henselian discrete valuation rings** (BLR §1.4 Thm. 3 over a
henselian DVR; proved in the vendored FLT development, `exists_neronModelPropertyBundle_genericFibre_iso_of_
abelianSchemePropertyBundle_of_henselianLocalRing`). No hypothesis on the residue field. -/
theorem exists_neron_of_henselian [HenselianLocalRing R] (A : PkgI3.AbVar K) :
    ∃ N : Over (Spec (CommRingCat.of R)), CToPrinted.IsNeronModelOver R K N ∧
      Nonempty ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap R K)))).obj N ≅ A.X) := by
  haveI : GrpObj (Over.mk A.X.hom) := by
    change GrpObj A.X
    infer_instance
  let LAK := relativeGroupLawOfGrpObj K A.X.hom
  have hAK : AbelianSchemePropertyBundle K A.X.hom :=
    { smooth := inferInstance
      proper := inferInstance
      connectedFibres := fun s => A.X.hom.isConnected_preimage_singleton s
      hasGroupLaw := ⟨LAK⟩ }
  obtain ⟨B, g, LB, e, hN, -, he, -⟩ :=
    GoodReductionJacobian.RelativeGroupLaw.exists_neronModelPropertyBundle_genericFibre_iso_of_abelianSchemePropertyBundle_of_henselianLocalRing
      (R := R) K LAK hAK
  haveI := he
  refine ⟨Over.mk g, isNeronModelOver_of_bundle' R K (Over.mk g) hN, ⟨?_⟩⟩
  exact Over.isoMk (@asIso _ _ _ _ e.1 he) e.2

end DVR

end NeronFLT
