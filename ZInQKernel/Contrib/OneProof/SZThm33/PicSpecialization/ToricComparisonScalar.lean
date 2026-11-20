import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricProductMaps
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ModelAxisComparison
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.RankOneTorus

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open Scheme.Modules
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

open PicDict.Transport

variable {k : Type} [Field k] [IsAlgClosed k] {S : Scheme.{0}}
  (G : Over S) [GrpObj G] (H : Over (Spec (.of k))) [GrpObj H] [IsIntegral H.left]


variable (j : Spec (.of k) ⟶ S) (p : H.left ⟶ G.left)
  (hp : p ≫ G.hom = H.hom ≫ j) (d : (puncturedLine k) ⟶ H) [IsMonHom d]
  (hη : η[H].left ≫ p = j ≫ η[G].left)


set_option backward.isDefEq.respectTransparency false in
/-- A normalized frame of the polarization line on the rank-one toric
product makes the comparison defect a scalar from the base. -/
theorem toricComparison_scalar [IsIntegral ((H ⊗ puncturedLine k).left)] (n : ℕ)
    (hpm : (multiplyBy H n).left ≫ p = p ≫ (multiplyBy G n).left)
    (hc : Function.Surjective G.hom.appTop)
    (M : (G ⊗ G).left.Modules)
    (J : (pullback (powerFirst G n).left).obj M ≅ (pullback (powerSecond G n).left).obj M)
    (e₁ : unit G.left ≅ (pullback (firstAxis G).left).obj M)
    (e₂ : unit G.left ≅ (pullback (secondAxis G).left).obj M)
    (hE : pullFramedAlong η[G].left (firstAxis G).left e₁ ≪≫
      (pullbackCongr (congrArg Over.Hom.left (axisOrigin_eq G))).app M =
        pullFramedAlong η[G].left (secondAxis G).left e₂)
    (α : unit ((H ⊗ puncturedLine k).left) ≅ (pullback (toricProductMap G H (puncturedLine k) j p hp d)).obj M)
    (hα₁ : pullFramedAlong (torusAxis H (puncturedLine k)).left (toricProductMap G H (puncturedLine k) j p hp d) α ≪≫
      (pullbackCongr (torusAxis_comp_toricProductMap G H (puncturedLine k) j p hp d hη)).app M =
        pullFramedAlong (d.left ≫ p) (firstAxis G).left e₁)
    (hα₂ : pullFramedAlong (groupAxis H (puncturedLine k)).left (toricProductMap G H (puncturedLine k) j p hp d) α ≪≫
      (pullbackCongr (groupAxis_comp_toricProductMap G H (puncturedLine k) j p hp d hη)).app M =
        pullFramedAlong p (secondAxis G).left e₂) :
    comparisonDefect (toricProductMap G H (puncturedLine k) j p hp d) (torusDilation H (puncturedLine k) n).left (groupDilation H (puncturedLine k) n).left
      (powerFirst G n).left (powerSecond G n).left
      (toricProductMap_powerFirst G H (puncturedLine k) j p hp d n hpm)
      (toricProductMap_powerSecond G H (puncturedLine k) j p hp d n hpm) M J α =
      pullUnitIso ((H ⊗ (puncturedLine k)).hom ≫ j) (pullUnitIso η[G].left (firstAxisDefect G n M J e₁)) := by
  let D₁ := firstAxisDefect G n M J e₁
  let D₂ := secondAxisDefect G n M J e₂
  let u := pullUnitIso η[G].left D₁
  have hηG : η[G].left ≫ G.hom = 𝟙 S := Over.w η[G]
  have hD₁ : D₁ = pullUnitIso G.hom u := (pullUnitIso_origin_eq G.hom η[G].left hηG hc D₁).symm
  have hD₂ : D₂ = pullUnitIso G.hom u := by
    rw [show u = pullUnitIso η[G].left D₂ from axisDefect_origin_eq G n M J e₁ e₂ hE]
    exact (pullUnitIso_origin_eq G.hom η[G].left hηG hc D₂).symm
  let C := comparisonDefect (toricProductMap G H (puncturedLine k) j p hp d) (torusDilation H (puncturedLine k) n).left (groupDilation H (puncturedLine k) n).left
    (powerFirst G n).left (powerSecond G n).left
    (toricProductMap_powerFirst G H (puncturedLine k) j p hp d n hpm)
    (toricProductMap_powerSecond G H (puncturedLine k) j p hp d n hpm) M J α
  have ht : (d.left ≫ p) ≫ (multiplyBy G n).left =
      (multiplyBy (puncturedLine k) n).left ≫ d.left ≫ p := by
    have hd : (multiplyBy (puncturedLine k) n).left ≫ d.left = d.left ≫ (multiplyBy H n).left :=
      congrArg Over.Hom.left (multiplyBy_comp_monHom (puncturedLine k) d n)
    simp only [Category.assoc, reassoc_of% hd, hpm]
  have hT : pullUnitIso (torusAxis H (puncturedLine k)).left C = pullUnitIso (d.left ≫ p) D₁ := by
    apply pullUnitIso_comparisonDefect_of_common_restriction _ _ _ _
      (torusAxis_comp_toricProductMap G H (puncturedLine k) j p hp d hη) _ _ _ _
      (multiplyBy (puncturedLine k) n).left (𝟙 (puncturedLine k).left)
    · exact congrArg Over.Hom.left (torusAxis_comp_torusDilation H (puncturedLine k) n)
    · exact congrArg Over.Hom.left (torusAxis_comp_groupDilation H (puncturedLine k) n)
    · exact ht
    · simp
    · exact hα₁
  have hH : pullUnitIso (groupAxis H (puncturedLine k)).left C = pullUnitIso p D₂ := by
    apply pullUnitIso_comparisonDefect_of_common_restriction _ _ _ _
      (groupAxis_comp_toricProductMap G H (puncturedLine k) j p hp d hη) _ _ _ _
      (𝟙 H.left) (multiplyBy H n).left
    · exact congrArg Over.Hom.left (groupAxis_comp_torusDilation H (puncturedLine k) n)
    · exact congrArg Over.Hom.left (groupAxis_comp_groupDilation H (puncturedLine k) n)
    · simp
    · exact hpm.symm
    · exact hα₂
  have : IsIntegral (Limits.pullback H.hom (Spec.map (CommRingCat.ofHom
      (algebraMap k (Localization.Away (Polynomial.X : Polynomial k)))))) :=
    inferInstanceAs (IsIntegral ((H ⊗ puncturedLine k).left))
  change C = pullUnitIso ((H ⊗ (puncturedLine k)).hom ≫ j) u
  apply unitIso_eq_of_coordinate_sections H.hom (h := (Polynomial.X : Polynomial k))
    Polynomial.X_ne_zero (s := (groupAxis H (puncturedLine k)).left) (t := (torusAxis H (puncturedLine k)).left)
    (a := η[puncturedLine k].left)
  · exact congrArg Over.Hom.left (lift_fst (𝟙 H) (1 : H ⟶ (puncturedLine k)))
  · exact congrArg Over.Hom.left (lift_snd (𝟙 H) (1 : H ⟶ (puncturedLine k)))
  · exact congrArg Over.Hom.left (lift_snd (1 : (puncturedLine k) ⟶ H) (𝟙 (puncturedLine k)))
  · rw [hH, hD₂, pullUnitIso_comp p G.hom u,
      pullUnitIso_comp (groupAxis H (puncturedLine k)).left ((H ⊗ puncturedLine k).hom ≫ j) u,
      hp, reassoc_of% (Over.w (groupAxis H (puncturedLine k)))]
  · rw [hT, hD₁, pullUnitIso_comp (d.left ≫ p) G.hom u,
      pullUnitIso_comp (torusAxis H (puncturedLine k)).left ((H ⊗ puncturedLine k).hom ≫ j) u]
    simp only [Category.assoc, hp, Over.w_assoc]

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.toricComparison_scalar
