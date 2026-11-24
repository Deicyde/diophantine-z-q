import ZInQKernel.Contrib.CloudR2Poincare.L1.Normalization
import ZInQKernel.Contrib.CloudW07JacobiansCurves.Jacobian.AlgebraicGeometry.Picard.Field

/-!
# Pulling the normalized Mumford family back along the anti-diagonal

These are actual Scheme.Pic identities. The normalized self-family has its
standard m^*M / (p1^*M p2^*M) formula over a field. If that family is trivial,
pullback along y↦(y,−y) makes M⊗[-1]^*M trivial. The family-triviality input is
literal, not inferred from pointwise invariance or assumed as a seesaw Fact.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- Classes pulled back through Spec k are trivial, on the native Picard group. -/
theorem pic_map_constant_eq_one {k : Type u} [Field k] {X Y : Scheme.{u}}
    (p : X ⟶ Spec (.of k)) (q : Spec (.of k) ⟶ Y) (M : Y.Pic) :
    Scheme.Pic.map (p ≫ q) M = 1 := by
  rw [Scheme.Pic.map_comp,
    Subsingleton.elim (Scheme.Pic.map q M) (1 : (Spec (.of k)).Pic), Scheme.Pic.map_one]

/-- Exact normalized-self-family formula; the correction along the zero
section is M because Pic(Spec k)=0. -/
theorem normalizedSelfFamily_formula {k : Type u} [Field k]
    (A : Over (Spec (.of k))) [MonObj A] (M : A.left.Pic) :
    L1.normalizedPolarizationFamily A M (𝟙 A) =
      Scheme.Pic.map (L1.translationAction A (𝟙 A)).left M *
        (Scheme.Pic.map (fst A A).left M)⁻¹ *
        (Scheme.Pic.map (snd A A).left M)⁻¹ := by
  let σ := sectionBaseChange A.hom η[A].left (L1.groupUnit_over A) A
  let s : A ⟶ A ⊗ A := lift (toUnit A ≫ η[A]) (𝟙 A)
  have hs : s.left = σ := rfl
  have hact : σ ≫ (L1.translationAction A (𝟙 A)).left = 𝟙 A.left := by
    rw [← hs, ← Over.comp_left]
    have h : s ≫ L1.translationAction A (𝟙 A) = 𝟙 A := by
      simp [s, L1.translationAction, MonObj.comp_mul]
      change (𝟙 A) * (1 : A ⟶ A) = 𝟙 A
      exact _root_.mul_one _
    rw [h, Over.id_left]
  have hfst : σ ≫ (fst A A).left = A.hom ≫ η[A].left := sectionBaseChange_fst ..
  have hsection : Scheme.Pic.map σ (L1.polarizationFamily A M (𝟙 A)) = M := by
    rw [L1.polarizationFamily, Scheme.Pic.map_mul, L1.pic_map_inv,
      ← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, hact, hfst,
      Scheme.Pic.map_id, pic_map_constant_eq_one, inv_one, _root_.mul_one]
  rw [L1.normalizedPolarizationFamily_formula, hsection]
  rfl

/-- Anti-diagonal pullback of a trivial normalized self-family is exactly
triviality of the symmetrized class M⊗[-1]^*M. -/
theorem symmetrizedClass_eq_one_of_normalizedSelfFamily
    {k : Type u} [Field k] (A : Over (Spec (.of k))) [GrpObj A] (M : A.left.Pic)
    (hfamily : L1.normalizedPolarizationFamily A M (𝟙 A) = 1) :
    M * Scheme.Pic.map ι[A].left M = 1 := by
  let a : A ⟶ A ⊗ A := lift (𝟙 A) ι[A]
  have hact : a ≫ L1.translationAction A (𝟙 A) = 1 := by
    simp [a, L1.translationAction, MonObj.comp_mul]
    rw [GrpObj.inv_eq_inv]
    exact _root_.inv_mul_cancel _
  have h' := congrArg (Scheme.Pic.map a.left) hfamily
  rw [normalizedSelfFamily_formula, Scheme.Pic.map_mul, Scheme.Pic.map_mul,
    L1.pic_map_inv, L1.pic_map_inv, ← Scheme.Pic.map_comp,
    ← Scheme.Pic.map_comp, ← Scheme.Pic.map_comp, ← Over.comp_left,
    ← Over.comp_left, ← Over.comp_left, hact] at h'
  have hconst : Scheme.Pic.map (1 : A ⟶ A).left M = 1 := by
    change Scheme.Pic.map (A.hom ≫ η[A].left) M = 1
    exact pic_map_constant_eq_one _ _ _
  simp only [hconst, a, lift_fst, lift_snd, Over.id_left,
    Scheme.Pic.map_id, Scheme.Pic.map_one, _root_.one_mul] at h'
  have h'' := congrArg Inv.inv h'
  simpa only [mul_inv_rev, inv_inv, inv_one, _root_.mul_comm, _root_.mul_one,
    _root_.one_mul] using h''

end ZInQ.Contrib.CloudR2Poincare.L2
