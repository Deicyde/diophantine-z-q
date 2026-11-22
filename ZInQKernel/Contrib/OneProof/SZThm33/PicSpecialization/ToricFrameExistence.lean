import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricProductMaps
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ModelAxisComparison
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ExternalAxisFrames
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RankOneTorus
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.AffineLinePicard
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Regular

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.Modules
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

open PicDict.Transport

variable {k : Type} [Field k] [IsAlgClosed k] {S : Scheme.{0}}
  (G : Over S) [GrpObj G] (H : Over (Spec (.of k))) [GrpObj H] [IsIntegral H.left]
  (j : Spec (.of k) ⟶ S) (p : H.left ⟶ G.left)
  (hp : p ≫ G.hom = H.hom ≫ j) (d : puncturedLine k ⟶ H) [IsMonHom d]
  (hη : η[H].left ≫ p = j ≫ η[G].left)

set_option backward.isDefEq.respectTransparency false in
set_option maxHeartbeats 2800000 in
/-- The actual polarization line on the rank-one toric product admits a frame
compatible with the pulled-back model frames on both axes. -/
theorem exists_normalized_toric_frame [Smooth H.hom] [IsIntegral (H ⊗ puncturedLine k).left]
    (M : (G ⊗ G).left.Modules) [M.IsInvertible]
    (e₁ : unit G.left ≅ (pullback (firstAxis G).left).obj M)
    (e₂ : unit G.left ≅ (pullback (secondAxis G).left).obj M)
    (hE : pullFramedAlong η[G].left (firstAxis G).left e₁ ≪≫
      (pullbackCongr (congrArg Over.Hom.left (axisOrigin_eq G))).app M =
        pullFramedAlong η[G].left (secondAxis G).left e₂) :
    let i := toricProductMap G H (puncturedLine k) j p hp d
    ∃ α : unit (H ⊗ puncturedLine k).left ≅ (pullback i).obj M,
      (pullFramedAlong (torusAxis H (puncturedLine k)).left i α ≪≫
        (pullbackCongr (torusAxis_comp_toricProductMap G H (puncturedLine k) j p hp d hη)).app M =
          pullFramedAlong (d.left ≫ p) (firstAxis G).left e₁) ∧
      (pullFramedAlong (groupAxis H (puncturedLine k)).left i α ≪≫
        (pullbackCongr (groupAxis_comp_toricProductMap G H (puncturedLine k) j p hp d hη)).app M =
          pullFramedAlong p (secondAxis G).left e₂) := by
  let T := puncturedLine k
  let i := toricProductMap G H T j p hp d
  let s := (groupAxis H T).left
  let t := (torusAxis H T).left
  let a := (firstAxis G).left
  let b := (secondAxis G).left
  let hs := groupAxis_comp_toricProductMap G H T j p hp d hη
  let ht := torusAxis_comp_toricProductMap G H T j p hp d hη
  let eH := externalAxisFrame s i p b hs e₂
  let eT := externalAxisFrame t i (d.left ≫ p) a ht e₁
  have hreg := IsRegular.of_smooth H.hom
  have hUFD := IsRegular.uniqueFactorizationMonoid_stalk (scheme := H.left)
  have hY : IsIntegral (Limits.pullback H.hom (Spec.map (CommRingCat.ofHom
      (algebraMap k (Localization.Away (Polynomial.X : Polynomial k)))))) :=
    inferInstanceAs (IsIntegral ((H ⊗ puncturedLine k).left))
  have hηT : η[T].left ≫ T.hom = 𝟙 (Spec (.of k)) := Over.w η[T]
  obtain ⟨α₀⟩ := nonempty_iso_unit_product_of_section H.hom Polynomial.X_ne_zero
    hUFD η[T].left hηT ((pullback i).obj M) eH
  have hOrigins : η[H] ≫ groupAxis H T = η[T] ≫ torusAxis H T := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, groupAxis, lift_fst, Category.comp_id, Category.assoc, torusAxis,
        lift_fst, MonObj.comp_one, MonObj.one_eq_one]
    · rw [Category.assoc, groupAxis, lift_snd, MonObj.comp_one, Category.assoc, torusAxis,
        lift_snd, Category.comp_id, MonObj.one_eq_one]
  have htp : η[T].left ≫ (d.left ≫ p) = j ≫ η[G].left := by
    rw [← Category.assoc, ← Over.comp_left, IsMonHom.one_hom, hη]
  have hOriginR := pullFramedAlong_comp_of_agreement j η[G].left η[G].left a b
    (congrArg Over.Hom.left (axisOrigin_eq G)) e₁ e₂ hE
  have hFrame := externalAxisFrames_agree_at_origin t s i (d.left ≫ p) p a b ht hs
    η[T].left η[H].left (j ≫ η[G].left) htp hη
    (congrArg Over.Hom.left hOrigins.symm) _ e₁ e₂ hOriginR
  have hFrame' : pullFramedAlong η[H].left s eH ≪≫
      (pullbackCongr (congrArg Over.Hom.left hOrigins)).app ((pullback i).obj M) =
        pullFramedAlong η[T].left t eT := by
    apply Iso.ext
    have hh := congrArg Iso.hom hFrame
    simp only [Iso.trans_hom, Iso.app_hom, pullbackCongr_hom_app] at hh ⊢
    rw [← hh, Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  obtain ⟨α, hαH, hαT⟩ := exists_frame_matching_axes_of_origin α₀ (fst H T).left (snd H T).left
    s t H.hom T.hom η[H].left η[T].left
    (congrArg Over.Hom.left (lift_fst (𝟙 H) (1 : H ⟶ T)))
    (congrArg Over.Hom.left (lift_snd (1 : T ⟶ H) (𝟙 T)))
    (congrArg Over.Hom.left (lift_snd (𝟙 H) (1 : H ⟶ T)))
    (congrArg Over.Hom.left (lift_fst (1 : T ⟶ H) (𝟙 T)))
    hηT (congrArg Over.Hom.left hOrigins) eH eT hFrame'
  refine ⟨α, ?_, ?_⟩
  · change pullFramedAlong t i α ≪≫ _ = _
    unfold pullFramedAlong
    rw [hαT]
    exact externalAxisFrame_transport t i (d.left ≫ p) a ht e₁
  · change pullFramedAlong s i α ≪≫ _ = _
    unfold pullFramedAlong
    rw [hαH]
    exact externalAxisFrame_transport s i p b hs e₂

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.exists_normalized_toric_frame
