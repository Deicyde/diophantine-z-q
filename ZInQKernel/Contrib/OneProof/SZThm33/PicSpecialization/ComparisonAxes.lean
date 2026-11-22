import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.ToricDefectRestriction
import ZInQKernel.Contrib.OneProof.SZThm33.PicSpecialization.OriginFrames

noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace PicDict.Transport

variable {Z X Y P S : Scheme.{0}}

/-- A defect is unchanged by transporting the underlying subscheme and its frame. -/
theorem comparisonDefect_congr {i i' : Y ⟶ P} (hi : i = i') (a b : Y ⟶ Y) (l r : P ⟶ P)
    (hl : i ≫ l = a ≫ i) (hr : i ≫ r = b ≫ i)
    (hl' : i' ≫ l = a ≫ i') (hr' : i' ≫ r = b ≫ i')
    (M : P.Modules) (J : (pullback l).obj M ≅ (pullback r).obj M)
    (α : unit Y ≅ (pullback i).obj M) (α' : unit Y ≅ (pullback i').obj M)
    (hα : α ≪≫ (pullbackCongr hi).app M = α') :
    comparisonDefect i a b l r hl hr M J α =
      comparisonDefect i' a b l r hl' hr' M J α' := by
  subst hi
  have hEq : (pullbackCongr (rfl : i = i)).app M = Iso.refl _ := by
    apply Iso.ext
    simp [pullbackCongr]
  rw [hEq, Iso.trans_refl] at hα
  subst α'
  rfl

/-- Compare defect restrictions along two commuting paths agreeing in the
ambient scheme and in the chosen frames. -/
theorem pullUnitIso_comparisonDefect_of_common_restriction
    (j : Z ⟶ Y) (k : Z ⟶ X) (i : Y ⟶ P) (i' : X ⟶ P) (hi : j ≫ i = k ≫ i')
    (a b : Y ⟶ Y) (a' b' : X ⟶ X) (p q : Z ⟶ Z) (l r : P ⟶ P)
    (ha : j ≫ a = p ≫ j) (hb : j ≫ b = q ≫ j)
    (ha' : k ≫ a' = p ≫ k) (hb' : k ≫ b' = q ≫ k)
    (hl : i ≫ l = a ≫ i) (hr : i ≫ r = b ≫ i)
    (hl' : i' ≫ l = a' ≫ i') (hr' : i' ≫ r = b' ≫ i')
    (M : P.Modules) (J : (pullback l).obj M ≅ (pullback r).obj M)
    (α : unit Y ≅ (pullback i).obj M) (α' : unit X ≅ (pullback i').obj M)
    (hα : (pullFrame j α ≪≫ (pullbackComp j i).app M) ≪≫ (pullbackCongr hi).app M =
      pullFrame k α' ≪≫ (pullbackComp k i').app M) :
    pullUnitIso j (comparisonDefect i a b l r hl hr M J α) =
      pullUnitIso k (comparisonDefect i' a' b' l r hl' hr' M J α') := by
  rw [pullUnitIso_comparisonDefect_commuting j i p q a b l r ha hb hl hr,
    pullUnitIso_comparisonDefect_commuting k i' p q a' b' l r ha' hb' hl' hr']
  exact comparisonDefect_congr hi p q l r _ _ _ _ M J _ _ hα

end PicDict.Transport

#print axioms PicDict.Transport.pullUnitIso_comparisonDefect_of_common_restriction
