import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RankOneModelVanishing
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricFrameExistence
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricProductIntegral
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.TestModelSlice
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ModelAxisFrames

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.Modules
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

open PicDict.Transport

variable {k : Type} [Field k] [IsAlgClosed k] {S W : Scheme.{0}}
  (G : Over S) [GrpObj G]
  (U : Over W) [GrpObj U] [IsCommMonObj U]
  (H : Over (Spec (.of k))) [GrpObj H] [Smooth H.hom] [GeometricallyIntegral H.hom]
  (j : W ⟶ S) (c : U.left ⟶ G.left) (hc : c ≫ G.hom = U.hom ≫ j)
  (s : Spec (.of k) ⟶ W) (p : H.left ⟶ G.left)
  (d : puncturedLine k ⟶ H) [IsMonHom d]

private theorem modelOrigin_translate (x : 𝟙_ (Over W) ⟶ U) :
    η[U] ≫ translateBy U x = x := by
  have h : η[U] ≫ toUnit U = 𝟙 _ := toUnit_unique _ _
  rw [translateBy, MonObj.comp_mul, Category.comp_id, ← Category.assoc, h,
    Category.id_comp, MonObj.one_eq_one, _root_.one_mul]

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2000000 in
/-- For an actual torsion slice on a test model, the Mumford trivialization
can be evaluated at the special identity. Its coefficient is one when the
translation point reduces to the rank-one torus. -/
theorem exists_testModel_trivialization_special_eq_one
    (hp : p ≫ G.hom = H.hom ≫ s ≫ j)
    (hη : η[H].left ≫ p = (s ≫ j) ≫ η[G].left)
    (hηU : η[U].left ≫ c = j ≫ η[G].left) (n : ℕ)
    (hpm : (multiplyBy H n).left ≫ p = p ≫ (multiplyBy G n).left)
    (hcm : (multiplyBy U n).left ≫ c = c ≫ (multiplyBy G n).left)
    (hconst : Function.Surjective G.hom.appTop)
    (x y : 𝟙_ (Over W) ⟶ U) (hx : x ^ n = 1) (hy : y ^ n = 1)
    (x₀ : 𝟙_ (Over (Spec (.of k))) ⟶ puncturedLine k) (y₀ : 𝟙_ (Over (Spec (.of k))) ⟶ H)
    (hx₀ : x₀ ^ n = 1) (hy₀ : y₀ ^ n = 1)
    (hxp : x₀.left ≫ d.left ≫ p = s ≫ x.left ≫ c)
    (hyp : y₀.left ≫ p = s ≫ y.left ≫ c)
    (L : G.left.Pic) (M : (G ⊗ G).left.Modules) [M.IsInvertible]
    (hM : Scheme.Pic.mk M = productDeltaClass G L)
    (J : (pullback (powerFirst G n).left).obj M ≅ (pullback (powerSecond G n).left).obj M) :
    let a := testPointSlice G U j c hc y
    ∃ ψ : unit U.left ≅ (pullback (multiplyBy U n).left).obj ((pullback a).obj M),
      (s ≫ η[U].left).appTop
        (wf (translateBy U x).left (multiplyBy U n).left
          (congrArg Over.Hom.left (translateBy_comp_multiplyBy U x n hx))
          ((pullback a).obj M) ψ) = 1 := by
  let a := testPointSlice G U j c hc y
  let m := (multiplyBy U n).left
  let t := (translateBy U x).left
  let g := s ≫ η[U].left
  let l := (powerFirst G n).left
  let r := (powerSecond G n).left
  let b := c ≫ (firstAxis G).left
  let hm := testPointSlice_powerFirst G U j c hc y n hcm
  let hb := testPointSlice_powerSecond G U j c hc y n hy hcm hηU
  let ht := congrArg Over.Hom.left (translateBy_comp_multiplyBy U x n hx)
  have hP : p ≫ G.hom = H.hom ≫ (s ≫ j) := hp
  have : IsIntegral H.left := GeometricallyIntegral.isIntegral_of_subsingleton H.hom
  have : IsIntegral (H ⊗ puncturedLine k).left := isIntegral_product_puncturedLine H
  obtain ⟨e₁, e₂, hE⟩ := exists_axis_frames_agree_at_origin G L M hM
  obtain ⟨α, hα₁, hα₂⟩ := exists_normalized_toric_frame G H (s ≫ j) p hP d hη M e₁ e₂ hE
  let e := pullFramedAlong c (firstAxis G).left e₁
  refine ⟨sliceComparisonTriv m a b l r hm hb M J e, ?_⟩
  have hη' : η[U].left ≫ t = x.left := congrArg Over.Hom.left (modelOrigin_translate U x)
  have hg' : g ≫ t = s ≫ x.left := by rw [show g = s ≫ η[U].left from rfl, Category.assoc, hη']
  have hU : η[U].left ≫ U.hom = 𝟙 W := Over.w η[U]
  have hUx : x.left ≫ U.hom = 𝟙 W := Over.w x
  refine rankOne_special_coefficient_eq_one G H (s ≫ j) p hP d hη n hpm hconst
    x₀ y₀ hx₀ hy₀ g t m ht c a hm hb ?_ ?_ ?_ ?_ ?_ M J e₁ e₂ hE α hα₁ hα₂
  · exact testPointSlice_fst G U j c hc y
  · simp only [g, Category.assoc, hηU]
  · rw [hg', Category.assoc, hxp]
  · simp only [g, testPointSlice_snd, a, Category.assoc, reassoc_of% hU, hyp]
    exact congrArg (s ≫ ·) (Category.id_comp (y.left ≫ c))
  · simp only [hg', testPointSlice_snd, a, Category.assoc, reassoc_of% hUx, hyp]
    exact congrArg (s ≫ ·) (Category.id_comp (y.left ≫ c))

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.exists_testModel_trivialization_special_eq_one
