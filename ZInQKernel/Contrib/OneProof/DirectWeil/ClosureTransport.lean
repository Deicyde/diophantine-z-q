import ZInQKernel.Contrib.OneProof.H.TailZ7

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open PkgI3 PkgI3.AbVar
open scoped CategoryTheory.MonObj

namespace PicDict.DirectPairing

variable {K E F G : Type} [Field K] [Field E] [Field F] [Field G]
  [Algebra K E] [Algebra K F] [Algebra K G]

private def pointSpec (f : E →ₐ[K] F) : ptObj (K := K) F ⟶ ptObj E :=
  Over.homMk (Spec.map (CommRingCat.ofHom (f : E →+* F))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

private theorem pointSpec_comp (f : E →ₐ[K] F) (g : F →ₐ[K] G) :
    pointSpec (g.comp f) = pointSpec g ≫ pointSpec f := by
  apply Over.OverMorphism.ext
  simp only [pointSpec, Over.comp_left]
  exact Spec.map_comp (CommRingCat.ofHom (f : E →+* F)) (CommRingCat.ofHom (g : F →+* G))

private theorem inv_pointSpec_comp (e : E ≃ₐ[K] F) :
    pointSpec e.symm.toAlgHom ≫ pointSpec e.toAlgHom = 𝟙 _ := by
  rw [← pointSpec_comp]
  apply Over.OverMorphism.ext
  have h : (e.symm.toAlgHom.comp e.toAlgHom : E →ₐ[K] E) = AlgHom.id K E := by
    ext x
    exact e.symm_apply_apply x
  rw [h]
  exact Spec.map_id _

/-- Transport geometric points by an isomorphism of their coefficient fields. -/
def pointEquiv (A : AbVar K) (e : E ≃ₐ[K] F) : A.Pt E ≃* A.Pt F where
  toFun x := pointSpec e.toAlgHom ≫ x
  invFun x := pointSpec e.symm.toAlgHom ≫ x
  left_inv x := by
    change pointSpec e.symm.toAlgHom ≫ pointSpec e.toAlgHom ≫ x = x
    rw [← Category.assoc, inv_pointSpec_comp, Category.id_comp]
  right_inv x := by
    change pointSpec e.toAlgHom ≫ pointSpec e.symm.toAlgHom ≫ x = x
    have h := inv_pointSpec_comp e.symm
    rw [AlgEquiv.symm_symm] at h
    rw [← Category.assoc, h, Category.id_comp]
  map_mul' x y := MonObj.comp_mul _ _ _

theorem pointEquiv_gal (A : AbVar K) (e : E ≃ₐ[K] F) (σ : F ≃ₐ[K] F) (x : A.Pt E) :
    pointEquiv A e (A.galAct (e.trans (σ.trans e.symm)) x) = A.galAct σ (pointEquiv A e x) := by
  change pointSpec e.toAlgHom ≫ pointSpec (e.trans (σ.trans e.symm)).toAlgHom ≫ x =
    pointSpec σ.toAlgHom ≫ pointSpec e.toAlgHom ≫ x
  rw [← Category.assoc, ← Category.assoc, ← pointSpec_comp, ← pointSpec_comp]
  congr 2
  ext t
  exact e.apply_symm_apply (σ (e t))

variable {ℓ : ℕ} [Fact ℓ.Prime]

/-- Transport the Tate module by an isomorphism of coefficient fields. -/
def tateEquiv (A : AbVar K) (e : E ≃ₐ[K] F) : ReductSplit.TΩ A E ℓ ≃ₗ[ℤ_[ℓ]] ReductSplit.TΩ A F ℓ :=
  LinearEquiv.ofLinearMap (Tate.map (pointEquiv A e).toMonoidHom.toAdditive)
    (Tate.map (pointEquiv A e).symm.toMonoidHom.toAdditive)
    (by ext t : 1; apply Subtype.ext; funext n; exact (pointEquiv A e).apply_symm_apply _)
    (by ext t : 1; apply Subtype.ext; funext n; exact (pointEquiv A e).symm_apply_apply _)

theorem tateEquiv_gal (A : AbVar K) (e : E ≃ₐ[K] F) (σ : F ≃ₐ[K] F) (x : ReductSplit.TΩ A E ℓ) :
    tateEquiv A e (ReductSplit.galTΩ A ℓ (e.trans (σ.trans e.symm)) x) =
      ReductSplit.galTΩ A ℓ σ (tateEquiv A e x) := by
  apply Subtype.ext
  funext n
  exact pointEquiv_gal A e σ (Additive.toMul (x.1 n))

end PicDict.DirectPairing
