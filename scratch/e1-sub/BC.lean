import ZInQKernel.HDecomp.ModCurves.Glue
import ZInQKernel.HDecomp.I3Linalg.C2
import ZInQKernel.HDecomp.I3Linalg.TateBC

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 PkgI3.AbVar
open scoped TensorProduct CategoryTheory.Obj

namespace E1Sub

section BaseChange

variable {K : Type} [Field K] {L : Type} [Field L] [Algebra K L]

/-- `Spec M₂ → Spec M₁` over `K`, for a `K`-algebra map `M₁ → M₂`. -/
def specHom {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁] [Algebra K M₂]
    (i : M₁ →ₐ[K] M₂) : ptObj (K := K) M₂ ⟶ ptObj (K := K) M₁ :=
  Over.homMk (Spec.map (CommRingCat.ofHom (i : M₁ →+* M₂))) (by
    simp only [ptObj, Over.mk_hom, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext x
    simp)

/-- `Spec M → Spec M ×_{Spec K} Spec L` over `L` (graph of the structure maps). -/
def ptUnit (M : Type) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    ptObj (K := L) M ⟶
      (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).obj (ptObj (K := K) M) :=
  Over.homMk (pullback.lift (𝟙 _) (Spec.map (CommRingCat.ofHom (algebraMap L M))) (by
    simp only [ptObj, Over.mk_hom, Category.id_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp,
      ← IsScalarTower.algebraMap_eq])) (pullback.lift_snd _ _ _)

variable (L) in
/-- Points of `A` with values in an `L`-algebra `M` become points of `A_L`. -/
def bcPt (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M] [IsScalarTower K L M] :
    J.Pt M →* (J.baseChange L).Pt M where
  toFun Q := ptUnit M ≫ (Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map Q
  map_one' := by
    change ptUnit M ≫ (Over.pullback _).map (1 : ptObj (K := K) M ⟶ J.X) = 1
    rw [Functor.map_one, MonObj.comp_one]
    rfl
  map_mul' Q Q' := by
    change ptUnit M ≫ (Over.pullback _).map (Q * Q') =
      (ptUnit M ≫ (Over.pullback _).map Q) * (ptUnit M ≫ (Over.pullback _).map Q')
    rw [Functor.map_mul, MonObj.comp_mul]
    rfl

lemma bcPt_fst (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] (Q : J.Pt M) :
    (bcPt L J M Q).left ≫ pullback.fst _ _ = Q.left := by
  change ((ptUnit (K := K) (L := L) M).left ≫
    ((Over.pullback (Spec.map (CommRingCat.ofHom (algebraMap K L)))).map Q).left) ≫
      pullback.fst _ _ = Q.left
  simp only [ptUnit, Over.pullback_map_left, Category.assoc, pullback.lift_fst]
  exact (pullback.lift_fst_assoc _ _ _ _).trans (Category.id_comp _)

lemma bcPt_injective (J : AbVar K) (M : Type) [Field M] [Algebra L M] [Algebra K M]
    [IsScalarTower K L M] : Function.Injective (bcPt L J M) := by
  intro Q Q' h
  apply Over.OverMorphism.ext
  rw [← bcPt_fst (L := L) J M Q, ← bcPt_fst (L := L) J M Q', h]

/-- Precomposition with `Spec ι`, `A(M₁) → A(M₂)`. -/
def precompPt (J : AbVar K) {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁] [Algebra K M₂]
    (i : M₁ →ₐ[K] M₂) : J.Pt M₁ →* J.Pt M₂ where
  toFun P := specHom i ≫ P
  map_one' := MonObj.comp_one _
  map_mul' _ _ := MonObj.comp_mul _ _ _

lemma precompPt_injective (J : AbVar K) {M₁ M₂ : Type} [Field M₁] [Field M₂] [Algebra K M₁]
    [Algebra K M₂] (i : M₁ →ₐ[K] M₂) : Function.Injective (precompPt J i) := by
  intro P P' h
  have hd : IsDominant (specHom (K := K) i).left := by
    constructor
    have : Subsingleton (ptObj (K := K) M₁).left :=
      inferInstanceAs (Subsingleton (PrimeSpectrum M₁))
    have hne : Nonempty (ptObj (K := K) M₂).left :=
      inferInstanceAs (Nonempty (PrimeSpectrum M₂))
    obtain ⟨x⟩ := hne
    intro y
    rw [Subsingleton.elim y ((specHom (K := K) i).left x)]
    exact subset_closure (Set.mem_range_self x)
  have : IsReduced (ptObj (K := K) M₁).left :=
    inferInstanceAs (IsReduced (Spec (CommRingCat.of M₁)))
  apply Over.OverMorphism.ext
  exact ext_of_isDominant_of_isSeparated J.X.hom (by simp) (specHom (K := K) i).left
    (by rw [← Over.comp_left, ← Over.comp_left]; exact congrArg CommaMorphism.left h)

end BaseChange

end E1Sub
