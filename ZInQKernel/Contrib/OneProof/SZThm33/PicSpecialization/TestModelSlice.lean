import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricProductMaps

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

variable {S W : Scheme.{0}} (G : Over S) [GrpObj G] (U : Over W) [GrpObj U]
  (j : W ⟶ S) (c : U.left ⟶ G.left) (hc : c ≫ G.hom = U.hom ≫ j)

/-- The torsion slice tested over a different base maps into the original
model product in the two original model coordinates. -/
def testPointSlice (y : 𝟙_ (Over W) ⟶ U) : U.left ⟶ (G ⊗ G).left :=
  pullback.lift c (U.hom ≫ y.left ≫ c) (by
    have hy : y.left ≫ U.hom = 𝟙 W := Over.w y
    simp only [Category.assoc, hc, reassoc_of% hy]
    exact congrArg (U.hom ≫ ·) (Category.id_comp j).symm)

omit [GrpObj G] [GrpObj U] in
@[reassoc (attr := simp)]
theorem testPointSlice_fst (y : 𝟙_ (Over W) ⟶ U) :
    testPointSlice G U j c hc y ≫ (fst G G).left = c :=
  pullback.lift_fst _ _ _

omit [GrpObj G] [GrpObj U] in
@[reassoc (attr := simp)]
theorem testPointSlice_snd (y : 𝟙_ (Over W) ⟶ U) :
    testPointSlice G U j c hc y ≫ (snd G G).left = U.hom ≫ y.left ≫ c :=
  pullback.lift_snd _ _ _

theorem testPointSlice_powerFirst (y : 𝟙_ (Over W) ⟶ U) (n : ℕ)
    (hm : (multiplyBy U n).left ≫ c = c ≫ (multiplyBy G n).left) :
    (multiplyBy U n).left ≫ testPointSlice G U j c hc y =
      testPointSlice G U j c hc y ≫ (powerFirst G n).left := by
  have ha : (powerFirst G n).left ≫ (fst G G).left =
      (fst G G).left ≫ (multiplyBy G n).left := by
    rw [← Over.comp_left, ← Over.comp_left, powerFirst, lift_fst, multiplyBy, MonObj.comp_pow,
      Category.comp_id]
  have hb : (powerFirst G n).left ≫ (snd G G).left = (snd G G).left := by
    rw [← Over.comp_left, powerFirst, lift_snd]
  apply modelProduct_hom_ext G
  · simp only [Category.assoc, testPointSlice_fst, ha, testPointSlice_fst_assoc, hm]
  · simp only [Category.assoc, testPointSlice_snd, hb, Over.w_assoc]

theorem testPointSlice_powerSecond (y : 𝟙_ (Over W) ⟶ U) (n : ℕ) (hy : y ^ n = 1)
    (hm : (multiplyBy U n).left ≫ c = c ≫ (multiplyBy G n).left)
    (hη : η[U].left ≫ c = j ≫ η[G].left) :
    testPointSlice G U j c hc y ≫ (powerSecond G n).left = c ≫ (firstAxis G).left := by
  have ha : (powerSecond G n).left ≫ (fst G G).left = (fst G G).left := by
    rw [← Over.comp_left, powerSecond, lift_fst]
  have hb : (powerSecond G n).left ≫ (snd G G).left =
      (snd G G).left ≫ (multiplyBy G n).left := by
    rw [← Over.comp_left, ← Over.comp_left, powerSecond, lift_snd, multiplyBy, MonObj.comp_pow,
      Category.comp_id]
  have hfa : (firstAxis G).left ≫ (fst G G).left = 𝟙 G.left := by
    rw [← Over.comp_left, firstAxis, lift_fst, Over.id_left]
  have hfb : (firstAxis G).left ≫ (snd G G).left = G.hom ≫ η[G].left := by
    rw [← Over.comp_left, firstAxis, lift_snd, CategoryTheory.Hom.one_def,
      Over.comp_left, Over.toUnit_left]
  have hy' : y.left ≫ (multiplyBy U n).left = η[U].left := by
    rw [← Over.comp_left, multiplyBy, MonObj.comp_pow, Category.comp_id, hy, MonObj.one_eq_one]
  apply modelProduct_hom_ext G
  · simp only [Category.assoc, ha, hfa, testPointSlice_fst, Category.comp_id]
  · simp only [Category.assoc, hb, hfb, testPointSlice_snd_assoc]
    rw [← hm, ← Category.assoc y.left, hy', hη, ← Category.assoc, ← hc, Category.assoc]

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.testPointSlice_powerSecond
