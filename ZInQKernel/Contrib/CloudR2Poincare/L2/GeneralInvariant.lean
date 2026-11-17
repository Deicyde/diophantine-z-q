import ZInQKernel.Contrib.CloudR2Poincare.L2.SymmetricVeryAmple
import ZInQKernel.Contrib.CloudR2Poincare.L2.MumfordSymmetry
import ZInQKernel.Contrib.CloudR2Poincare.L1.Normalization

/-!
# The Mumford contradiction on an arbitrary integral closed subscheme

The anti-diagonal uses the inversion of the ambient abelian variety, so the
parameter T need not itself be a group. This removes the need for Cartier or
an abelian identity-component construction in the finite-stabilizer lane.
The normalized all-T vanishing input still has to come from genuine seesaw /
closed-functor representability; it is never inferred from raw Pic(T) injectivity.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj
open Scheme.Modules

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Exact normalized family formula on an arbitrary test scheme; the unit
restriction is j^*M because the remaining term factors through Spec k. -/
theorem normalizedPointFamily_formula {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [MonObj A] (M : A.left.Pic)
    {T : Over (Spec (.of k))} (j : T ⟶ A) :
    L1.normalizedPolarizationFamily A M j =
      Scheme.Pic.map (L1.translationAction A j).left M *
        (Scheme.Pic.map (fst A T).left M)⁻¹ *
        (Scheme.Pic.map (snd A T).left (Scheme.Pic.map j.left M))⁻¹ := by
  let σ := sectionBaseChange A.hom η[A].left (L1.groupUnit_over A) T
  let s : T ⟶ A ⊗ T := lift (toUnit T ≫ η[A]) (𝟙 T)
  have hs : s.left = σ := rfl
  have hact : σ ≫ (L1.translationAction A j).left = j.left := by
    rw [← hs, ← Over.comp_left]
    have h : s ≫ L1.translationAction A j = j := by
      simp [s, L1.translationAction, MonObj.comp_mul]
      change j * (1 : T ⟶ A) = j
      exact _root_.mul_one _
    rw [h]
  have hfst : σ ≫ (fst A T).left = T.hom ≫ η[A].left := sectionBaseChange_fst ..
  have hsection : Scheme.Pic.map σ (L1.polarizationFamily A M j) = Scheme.Pic.map j.left M := by
    rw [L1.polarizationFamily, Scheme.Pic.map_mul, L1.pic_map_inv,
      ← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, hact, hfst,
      pic_map_constant_eq_one, inv_one, _root_.mul_one]
  rw [L1.normalizedPolarizationFamily_formula, hsection]
  rfl

/-- Ambient anti-diagonal pullback, valid even when T is not a group scheme. -/
theorem restrictedSymmetrizedClass_eq_one_of_normalizedInvariant
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A]
    (M : A.left.Pic) {T : Over (Spec (.of k))} (j : T ⟶ A)
    (h : L1.normalizedPolarizationFamily A M j = 1) :
    Scheme.Pic.map j.left M * Scheme.Pic.map j⁻¹.left M = 1 := by
  let a : T ⟶ A ⊗ T := lift j⁻¹ (𝟙 T)
  have hact : a ≫ L1.translationAction A j = 1 := by
    simp [a, L1.translationAction, MonObj.comp_mul]
  have h' := congrArg (Scheme.Pic.map a.left) h
  rw [normalizedPointFamily_formula, Scheme.Pic.map_mul, Scheme.Pic.map_mul,
    L1.pic_map_inv, L1.pic_map_inv, ← Scheme.Pic.map_comp,
    ← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, ← Over.comp_left,
    ← Over.comp_left, ← Over.comp_left, hact] at h'
  have hconst : Scheme.Pic.map (1 : T ⟶ A).left M = 1 := by
    change Scheme.Pic.map (T.hom ≫ η[A].left) M = 1
    exact pic_map_constant_eq_one _ _ _
  simp only [hconst, a, lift_fst, lift_snd, Over.id_left,
    Scheme.Pic.map_id, Scheme.Pic.map_one, _root_.one_mul] at h'
  have h'' := congrArg Inv.inv h'
  simpa only [mul_inv_rev, inv_inv, inv_one, _root_.mul_one, _root_.one_mul] using h''

/-- **No positive-dimensional integral closed subscheme of the normalized
stabilizer.** T is the actual closed subscheme; no group structure on T,
Cartier theorem, or identity-component dimension statement is assumed. -/
theorem dimension_le_zero_of_normalizedInvariant_integral_closedSubscheme
    {k : Type u} [Field k] (A : PkgI3.AbVar k)
    {T : Over (Spec (.of k))} [IsIntegral T.left]
    (j : T ⟶ A.X) [IsClosedImmersion j.left]
    (M : A.X.left.Modules) (hM : VeryAmple A.X.hom M)
    (hinvariant : letI : M.IsInvertible := hM.isInvertible
      L1.normalizedPolarizationFamily A.X (Scheme.Pic.mk M) j = 1) :
    topologicalKrullDim T.left ≤ 0 := by
  letI : M.IsInvertible := hM.isInvertible
  letI : IsIso ι[A.X].left := by
    change IsIso ((Over.forget (Spec (.of k))).map ι[A.X])
    infer_instance
  have : IsProper T.hom := by
    rw [← j.w]
    infer_instance
  have : IsClosedImmersion j⁻¹.left := by
    rw [Hom.inv_def, Over.comp_left]
    infer_instance
  let N := (Scheme.Modules.pullback j.left).obj M
  let N' := (Scheme.Modules.pullback j⁻¹.left).obj M
  have hN : VeryAmple T.hom N := by simpa only [j.w] using hM.closedRestriction j.left
  have hN' : VeryAmple T.hom N' := by simpa only [j⁻¹.w] using hM.closedRestriction j⁻¹.left
  have htensor : Nonempty (N ⊗ N' ≅ unit T.left) := by
    have hclass := restrictedSymmetrizedClass_eq_one_of_normalizedInvariant
      A.X (Scheme.Pic.mk M) j hinvariant
    rw [Scheme.Pic.map_mk, Scheme.Pic.map_mk, ← Scheme.Pic.mk_tensorObj,
      Scheme.Pic.one_eq_mk_unit] at hclass
    exact (Scheme.Pic.mk_eq_mk_iff _ _).mp hclass
  obtain ⟨sN', hsN'⟩ := hN'.exists_nonzero_unit_map
  exact dimension_le_zero_of_veryAmple_of_effective_inverse T.hom N N' hN sN' hsN' htensor

end ZInQ.Contrib.CloudR2Poincare.L2
