import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudR2Poincare.L1.Stabilizer
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Field

/-!
# ONE explicit native theorem-of-the-square input shared by B2 and B4

This is a labelled ordinary proposition, not an assumed Fact or a theorem.
It says exactly that a restricted polarization FAMILY is translation invariant
on a test scheme with Pic(T)=0 (in particular every field test). The identity
rational-point specialization is proved here, so L3 need not define a second
square input. No equality is asserted on arbitrary nontrivial-Pic parameters.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- The ONE UNPROVED native square statement, in the exact field-family
restriction form consumed by the original-field graph. -/
def NativeTheoremOfTheSquare : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (J B : PkgI3.AbVar k) (i : PkgI3.AbVar.Hom B J) (L : J.X.left.Pic)
    (T : Over (Spec (.of k))) [Subsingleton T.left.Pic]
    (x : T ⟶ J.X) (b : T ⟶ B.X),
    Scheme.Pic.map (L1.familyTranslate B.X b).left
      (Scheme.Pic.map (L1.picardFamilyMap i.hom T) (L1.polarizationFamily J.X L x)) =
    Scheme.Pic.map (L1.picardFamilyMap i.hom T) (L1.polarizationFamily J.X L x)

/-- Genuine identity specialization of the SAME ordinary square input.
Its output is literally L3.TranslationInvariant after unfolding that predicate. -/
theorem translationClass_invariant_of_nativeSquare
    (hSquare : NativeTheoremOfTheSquare.{u})
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] [CharZero Ω]
    (B : PkgI3.AbVar Ω) (M : B.X.left.Pic)
    (x : 𝟙_ (Over (Spec (.of Ω))) ⟶ B.X) :
    ∀ b : 𝟙_ (Over (Spec (.of Ω))) ⟶ B.X,
      Scheme.Pic.map (L1.translate B.X b).left (L1.translationClass B.X M x) =
      L1.translationClass B.X M x := by
  intro b
  let T := 𝟙_ (Over (Spec (.of Ω)))
  letI : Subsingleton T.left.Pic := inferInstanceAs (Subsingleton (Spec (.of Ω)).Pic)
  have hfamily := hSquare Ω B B (PkgI3.AbVar.Hom.mk' (𝟙 B.X)) M T x b
  have hid : Scheme.Pic.map (L1.picardFamilyMap (𝟙 B.X) T)
      (L1.polarizationFamily B.X M x) = L1.polarizationFamily B.X M x := by
    rw [L1.picardFamilyMap_id]
    exact Scheme.Pic.map_id _
  change Scheme.Pic.map (L1.familyTranslate B.X b).left
      (Scheme.Pic.map (L1.picardFamilyMap (𝟙 B.X) T) (L1.polarizationFamily B.X M x)) =
    Scheme.Pic.map (L1.picardFamilyMap (𝟙 B.X) T) (L1.polarizationFamily B.X M x) at hfamily
  rw [hid] at hfamily
  let s : B.X ⟶ B.X ⊗ T := lift (𝟙 B.X) (toUnit B.X)
  have hs : s ≫ L1.familyTranslate B.X b = L1.translate B.X b ≫ s := by
    ext <;> simp [s, L1.familyTranslate, L1.translationAction_section, Category.assoc]
  have h := congrArg (Scheme.Pic.map s.left) hfamily
  rw [← Scheme.Pic.map_comp, ← Over.comp_left, hs, Over.comp_left,
    Scheme.Pic.map_comp] at h
  simpa only [s, Scheme.Pic.map_id, L1.polarizationFamily_rationalPoint] using h

end ZInQ.Contrib.CloudR2Poincare.L2
