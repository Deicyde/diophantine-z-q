import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ModelSlice

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.MonObj

namespace ZInQ.ToricOrthogonality

variable {S V : Scheme.{0}} (G : Over S) [GrpObj G] (H T : Over V) [GrpObj H] [GrpObj T]

theorem multiplyBy_comp_monHom {U : Over V} [GrpObj U] (d : H ⟶ U) [IsMonHom d] (n : ℕ) :
    multiplyBy H n ≫ d = d ≫ multiplyBy U n := by
  simp [multiplyBy, MonObj.pow_comp, MonObj.comp_pow]

omit [GrpObj G] in
theorem modelProduct_hom_ext {W : Scheme.{0}} {a b : W ⟶ (G ⊗ G).left}
    (hf : a ≫ (fst G G).left = b ≫ (fst G G).left)
    (hs : a ≫ (snd G G).left = b ≫ (snd G G).left) : a = b :=
  pullback.hom_ext hf hs

/-- Compare the product of the two special-fibre groups to the model product,
placing the torus in the first coordinate. -/
def toricProductMap (j : V ⟶ S) (p : H.left ⟶ G.left)
    (hp : p ≫ G.hom = H.hom ≫ j) (d : T ⟶ H) : (H ⊗ T).left ⟶ (G ⊗ G).left :=
  pullback.lift ((snd H T).left ≫ d.left ≫ p) ((fst H T).left ≫ p) (by
    simp only [Category.assoc, hp, Over.w_assoc])

omit [GrpObj G] [GrpObj H] [GrpObj T] in
@[reassoc (attr := simp)]
theorem toricProductMap_fst (j : V ⟶ S) (p : H.left ⟶ G.left)
    (hp : p ≫ G.hom = H.hom ≫ j) (d : T ⟶ H) :
    toricProductMap G H T j p hp d ≫ (fst G G).left = (snd H T).left ≫ d.left ≫ p :=
  pullback.lift_fst _ _ _

omit [GrpObj G] [GrpObj H] [GrpObj T] in
@[reassoc (attr := simp)]
theorem toricProductMap_snd (j : V ⟶ S) (p : H.left ⟶ G.left)
    (hp : p ≫ G.hom = H.hom ≫ j) (d : T ⟶ H) :
    toricProductMap G H T j p hp d ≫ (snd G G).left = (fst H T).left ≫ p :=
  pullback.lift_snd _ _ _

/-- The section at the identity of the torus in the special product. -/
def groupAxis : H ⟶ H ⊗ T := lift (𝟙 H) (1 : H ⟶ T)

/-- The section at the identity of the group in the special product. -/
def torusAxis : T ⟶ H ⊗ T := lift (1 : T ⟶ H) (𝟙 T)

/-- Multiply the torus coordinate of the special product. -/
def torusDilation (n : ℕ) : H ⊗ T ⟶ H ⊗ T := lift (fst H T) ((snd H T) ^ n)

/-- Multiply the complementary group coordinate of the special product. -/
def groupDilation (n : ℕ) : H ⊗ T ⟶ H ⊗ T := lift ((fst H T) ^ n) (snd H T)

theorem toricProductMap_powerFirst (j : V ⟶ S) (p : H.left ⟶ G.left)
    (hp : p ≫ G.hom = H.hom ≫ j) (d : T ⟶ H) [IsMonHom d]
    (n : ℕ) (hpm : (multiplyBy H n).left ≫ p = p ≫ (multiplyBy G n).left) :
    toricProductMap G H T j p hp d ≫ (powerFirst G n).left =
      (torusDilation H T n).left ≫ toricProductMap G H T j p hp d := by
  have ha : (powerFirst G n).left ≫ (fst G G).left =
      (fst G G).left ≫ (multiplyBy G n).left := by
    rw [← Over.comp_left, ← Over.comp_left, powerFirst, lift_fst, multiplyBy, MonObj.comp_pow,
      Category.comp_id]
  have hb : (powerFirst G n).left ≫ (snd G G).left = (snd G G).left := by
    rw [← Over.comp_left, powerFirst, lift_snd]
  have hc : (torusDilation H T n).left ≫ (snd H T).left =
      (snd H T).left ≫ (multiplyBy T n).left := by
    rw [← Over.comp_left, ← Over.comp_left, torusDilation, lift_snd, multiplyBy, MonObj.comp_pow,
      Category.comp_id]
  have hd : (torusDilation H T n).left ≫ (fst H T).left = (fst H T).left := by
    rw [← Over.comp_left, torusDilation, lift_fst]
  have hm : (multiplyBy T n).left ≫ d.left = d.left ≫ (multiplyBy H n).left :=
    congrArg Over.Hom.left (multiplyBy_comp_monHom T d n)
  apply modelProduct_hom_ext G
  · simp only [Category.assoc, ha, toricProductMap_fst_assoc, toricProductMap_fst,
      reassoc_of% hc, reassoc_of% hm, hpm]
  · simp only [Category.assoc, hb, toricProductMap_snd, reassoc_of% hd]

omit [GrpObj T] in
theorem toricProductMap_powerSecond (j : V ⟶ S) (p : H.left ⟶ G.left)
    (hp : p ≫ G.hom = H.hom ≫ j) (d : T ⟶ H)
    (n : ℕ) (hpm : (multiplyBy H n).left ≫ p = p ≫ (multiplyBy G n).left) :
    toricProductMap G H T j p hp d ≫ (powerSecond G n).left =
      (groupDilation H T n).left ≫ toricProductMap G H T j p hp d := by
  have ha : (powerSecond G n).left ≫ (snd G G).left =
      (snd G G).left ≫ (multiplyBy G n).left := by
    rw [← Over.comp_left, ← Over.comp_left, powerSecond, lift_snd, multiplyBy, MonObj.comp_pow,
      Category.comp_id]
  have hb : (powerSecond G n).left ≫ (fst G G).left = (fst G G).left := by
    rw [← Over.comp_left, powerSecond, lift_fst]
  have hc : (groupDilation H T n).left ≫ (fst H T).left =
      (fst H T).left ≫ (multiplyBy H n).left := by
    rw [← Over.comp_left, ← Over.comp_left, groupDilation, lift_fst, multiplyBy, MonObj.comp_pow,
      Category.comp_id]
  have hd : (groupDilation H T n).left ≫ (snd H T).left = (snd H T).left := by
    rw [← Over.comp_left, groupDilation, lift_snd]
  apply modelProduct_hom_ext G
  · simp only [Category.assoc, hb, toricProductMap_fst, reassoc_of% hd]
  · simp only [Category.assoc, ha, toricProductMap_snd_assoc, toricProductMap_snd,
      reassoc_of% hc, hpm]

theorem groupAxis_comp_toricProductMap (j : V ⟶ S) (p : H.left ⟶ G.left)
    (hp : p ≫ G.hom = H.hom ≫ j) (d : T ⟶ H) [IsMonHom d]
    (hη : η[H].left ≫ p = j ≫ η[G].left) :
    (groupAxis H T).left ≫ toricProductMap G H T j p hp d = p ≫ (secondAxis G).left := by
  apply modelProduct_hom_ext G
  · simp only [Category.assoc, toricProductMap_fst]
    have ha : (groupAxis H T).left ≫ (snd H T).left ≫ d.left = (1 : H ⟶ H).left := by
      rw [← Over.comp_left, ← Over.comp_left, ← Category.assoc, groupAxis, lift_snd, MonObj.one_comp]
    have hb : (secondAxis G).left ≫ (fst G G).left = (1 : G ⟶ G).left := by
      rw [← Over.comp_left, secondAxis, lift_fst]
    rw [← Category.assoc (snd H T).left, ← Category.assoc (groupAxis H T).left, ha, hb]
    simp only [CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left, Category.assoc,
      hη, reassoc_of% hp]
  · simp only [Category.assoc, toricProductMap_snd]
    rw [← Category.assoc (groupAxis H T).left, ← Over.comp_left, ← Over.comp_left,
      groupAxis, secondAxis, lift_fst, lift_snd]
    simp only [Over.id_left, Category.id_comp, Category.comp_id]

omit [GrpObj T] in
theorem torusAxis_comp_toricProductMap (j : V ⟶ S) (p : H.left ⟶ G.left)
    (hp : p ≫ G.hom = H.hom ≫ j) (d : T ⟶ H)
    (hη : η[H].left ≫ p = j ≫ η[G].left) :
    (torusAxis H T).left ≫ toricProductMap G H T j p hp d =
      (d.left ≫ p) ≫ (firstAxis G).left := by
  apply modelProduct_hom_ext G
  · simp only [Category.assoc, toricProductMap_fst]
    rw [← Category.assoc (torusAxis H T).left, ← Over.comp_left, ← Over.comp_left,
      torusAxis, firstAxis, lift_snd, lift_fst]
    simp only [Over.id_left, Category.id_comp, Category.comp_id]
  · simp only [Category.assoc, toricProductMap_snd]
    rw [← Category.assoc (torusAxis H T).left, ← Over.comp_left, ← Over.comp_left,
      torusAxis, firstAxis, lift_fst, lift_snd]
    simp only [CategoryTheory.Hom.one_def, Over.comp_left, Over.toUnit_left, Category.assoc,
      hη, reassoc_of% hp, Over.w_assoc]

omit [GrpObj H] in
theorem groupAxis_comp_torusDilation (n : ℕ) :
    groupAxis H T ≫ torusDilation H T n = 𝟙 H ≫ groupAxis H T := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [groupAxis, torusDilation, Category.assoc, lift_fst, lift_snd,
      Category.id_comp, MonObj.comp_pow, one_pow]

theorem groupAxis_comp_groupDilation (n : ℕ) :
    groupAxis H T ≫ groupDilation H T n = multiplyBy H n ≫ groupAxis H T := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [groupAxis, groupDilation, Category.assoc, lift_fst, lift_snd, MonObj.comp_one,
      MonObj.comp_pow, Category.comp_id, multiplyBy]

theorem torusAxis_comp_torusDilation (n : ℕ) :
    torusAxis H T ≫ torusDilation H T n = multiplyBy T n ≫ torusAxis H T := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [torusAxis, torusDilation, Category.assoc, lift_fst, lift_snd, MonObj.comp_one,
      MonObj.comp_pow, Category.comp_id, multiplyBy]

omit [GrpObj T] in
theorem torusAxis_comp_groupDilation (n : ℕ) :
    torusAxis H T ≫ groupDilation H T n = 𝟙 T ≫ torusAxis H T := by
  apply CartesianMonoidalCategory.hom_ext <;>
    simp only [torusAxis, groupDilation, Category.assoc, lift_fst, lift_snd, MonObj.comp_pow,
      one_pow, Category.id_comp]

end ZInQ.ToricOrthogonality

#print axioms ZInQ.ToricOrthogonality.toricProductMap_powerFirst
