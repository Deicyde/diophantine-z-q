import ZInQKernel.Contrib.CloudR2Poincare.L2.NativeSquare

/-!
# Native square deduction from an actual class-valued cube relation

H-72 L6 writing continuation, 2026-11-14. This file is new thin bridge code;
no Stacks source is vendored here. The geometric cube input in the reduction
below must be supplied by the sole shared c496 vendor, not by an axiom or an
assumed frontier leaf. The reduction alone is deliberately not advertised as
an unconditional proof of `NativeTheoremOfTheSquare`.

Unlike a field-point specialization, the deduction treats every parameter
scheme T with trivial native Picard group, exactly as the fixed L2 target.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L6

universe u

/-- Pullback along a map factoring through a scheme with trivial Picard group is trivial. -/
theorem pic_map_comp_eq_one {X T Y : Scheme.{u}} [Subsingleton T.Pic]
    (a : X ⟶ T) (b : T ⟶ Y) (L : Y.Pic) : Scheme.Pic.map (a ≫ b) L = 1 := by
  rw [Scheme.Pic.map_comp]
  have hb : Scheme.Pic.map b L = 1 := Subsingleton.elim _ _
  rw [hb, Scheme.Pic.map_one]

/-- The elementary quotient equality used after cancelling the three parameter classes. -/
theorem quotient_eq_of_cube_eq {G : Type*} [CommGroup G] {a b c d : G}
    (h : a * c = b * d) : a * d⁻¹ = b * c⁻¹ := by
  have h' : a = b * d * c⁻¹ := by
    simpa only [_root_.mul_assoc, _root_.mul_inv_cancel, _root_.mul_one] using
      congrArg (fun z : G => z * c⁻¹) h
  rw [h']
  calc
    (b * d * c⁻¹) * d⁻¹ = (b * c⁻¹) * (d * d⁻¹) := by ac_rfl
    _ = b * c⁻¹ := by rw [_root_.mul_inv_cancel, _root_.mul_one]

/-- Exact native square statement from the class-valued cube relation on each actual J.
The three classes pulled back from T vanish by the target's `Subsingleton T.Pic` hypothesis. -/
theorem nativeSquare_of_cubeRelation
    (hCube : ∀ (k : Type u) [Field k] [CharZero k] (J : PkgI3.AbVar k)
      (P : Over (Spec (.of k))) (f g h : P ⟶ J.X) (L : J.X.left.Pic),
      Scheme.Pic.map (f * g * h).left L * Scheme.Pic.map f.left L *
          Scheme.Pic.map g.left L * Scheme.Pic.map h.left L =
        Scheme.Pic.map (f * g).left L * Scheme.Pic.map (f * h).left L *
          Scheme.Pic.map (g * h).left L) : L2.NativeTheoremOfTheSquare.{u} := by
  intro k _ _ J B i L T _ x b
  let f : B.X ⊗ T ⟶ J.X := fst B.X T ≫ i.hom
  let g : B.X ⊗ T ⟶ J.X := snd B.X T ≫ x
  let h : B.X ⊗ T ⟶ J.X := snd B.X T ≫ b ≫ i.hom
  let tr : B.X ⊗ T ⟶ B.X ⊗ T := L1.familyTranslate B.X b
  have htrf : tr ≫ f = f * h := by
    simp [tr, f, h, L1.familyTranslate, L1.translationAction,
      MonObj.mul_comp, Category.assoc, mul_comm]
  have htrg : tr ≫ g = g := by
    simp [tr, g]
  have hfamily :
      Scheme.Pic.map (L1.picardFamilyMap i.hom T) (L1.polarizationFamily J.X L x) =
        Scheme.Pic.map (f * g).left L * (Scheme.Pic.map f.left L)⁻¹ := by
    rw [L1.picardFamilyMap_eq_tensor]
    have hp : (i.hom ⊗ₘ 𝟙 T) ≫ L1.translationAction J.X x = f * g := by
      simp [f, g, L1.translationAction, MonObj.comp_mul, mul_comm]
    simp only [L1.polarizationFamily, Scheme.Pic.map_mul, L1.pic_map_inv,
      ← Scheme.Pic.map_comp, ← Over.comp_left]
    rw [hp, tensorHom_fst]
  have hg : Scheme.Pic.map g.left L = 1 := by
    change Scheme.Pic.map (snd B.X T ≫ x).left L = 1
    rw [Over.comp_left]
    exact pic_map_comp_eq_one (snd B.X T).left x.left L
  have hh : Scheme.Pic.map h.left L = 1 := by
    change Scheme.Pic.map (snd B.X T ≫ (b ≫ i.hom)).left L = 1
    rw [Over.comp_left]
    exact pic_map_comp_eq_one (snd B.X T).left (b ≫ i.hom).left L
  have hgh : Scheme.Pic.map (g * h).left L = 1 := by
    have hfac : g * h = snd B.X T ≫ (x * (b ≫ i.hom)) := by
      simp [g, h, MonObj.comp_mul]
    rw [hfac, Over.comp_left]
    exact pic_map_comp_eq_one (snd B.X T).left (x * (b ≫ i.hom)).left L
  have hc := hCube k J (B.X ⊗ T) f g h L
  rw [hg, hh, hgh] at hc
  simp only [_root_.mul_one] at hc
  rw [hfamily]
  simp only [Scheme.Pic.map_mul, L1.pic_map_inv, ← Scheme.Pic.map_comp,
    ← Over.comp_left, MonObj.comp_mul]
  change Scheme.Pic.map (tr ≫ f * tr ≫ g).left L *
      (Scheme.Pic.map (tr ≫ f).left L)⁻¹ =
    Scheme.Pic.map (f * g).left L * (Scheme.Pic.map f.left L)⁻¹
  rw [htrf, htrg]
  have hreorder : (f * h) * g = (f * g) * h := by ac_rfl
  rw [hreorder]
  exact quotient_eq_of_cube_eq hc

end ZInQ.Contrib.CloudR2Poincare.L6
