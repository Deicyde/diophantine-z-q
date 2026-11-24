import ZInQKernel.HDecomp.Objects
import ZInQKernel.Contrib.CloudR2Poincare.L1.Normalization

/-!
# Restriction of the normalized Mumford family

Normalization commutes with pullback along an actual group homomorphism because
its unit section commutes with that map. This is an all-test-scheme identity;
no raw Picard-presheaf injectivity or representability fact is used.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory
  CartesianMonoidalCategory MonObj

namespace ZInQ.Contrib.CloudR2Poincare.L2

universe u

/-- An actual homomorphism makes the two normalized unit sections agree. -/
theorem sectionBaseChange_picardFamilyMap {S : Scheme.{u}}
    {A B T : Over S} [MonObj A] [MonObj B] (f : A ⟶ B) [IsMonHom f] :
    sectionBaseChange A.hom η[A].left (L1.groupUnit_over A) T ≫
        L1.picardFamilyMap f T =
      sectionBaseChange B.hom η[B].left (L1.groupUnit_over B) T := by
  apply pullback.hom_ext
  · simp only [Category.assoc, L1.picardFamilyMap, pullback.lift_fst,
      sectionBaseChange_fst_assoc]
    have h := congrArg Over.Hom.left (IsMonHom.one_hom f)
    simpa only [Over.comp_left, Category.assoc] using congrArg (T.hom ≫ ·) h
  · simp [L1.picardFamilyMap, sectionBaseChange, Category.assoc]

/-- **Normalized restriction identity.** A normalized polarization family
pulls back to the normalized family of the actual restricted line bundle. -/
theorem normalizedPolarizationFamily_pullback {S : Scheme.{u}}
    {A B T : Over S} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsMonHom f] (M : B.left.Pic) (x : T ⟶ A) :
    Scheme.Pic.map (L1.picardFamilyMap f T)
        (L1.normalizedPolarizationFamily B M (x ≫ f)) =
      L1.normalizedPolarizationFamily A (Scheme.Pic.map f.left M) x := by
  have hsection :
      Scheme.Pic.map (sectionBaseChange A.hom η[A].left (L1.groupUnit_over A) T)
        (L1.polarizationFamily A (Scheme.Pic.map f.left M) x) =
      Scheme.Pic.map (sectionBaseChange B.hom η[B].left (L1.groupUnit_over B) T)
        (L1.polarizationFamily B M (x ≫ f)) := by
    rw [← L1.polarizationFamily_pullback f M x, ← Scheme.Pic.map_comp,
      sectionBaseChange_picardFamilyMap]
  have hproj : L1.picardFamilyMap f T ≫ pullback.snd B.hom T.hom =
      pullback.snd A.hom T.hom := by simp [L1.picardFamilyMap]
  rw [L1.normalizedPolarizationFamily_formula, Scheme.Pic.map_mul, L1.pic_map_inv,
    ← Scheme.Pic.map_comp, hproj, L1.polarizationFamily_pullback,
    L1.normalizedPolarizationFamily_formula, hsection]

/-- In particular a literal normalized-stabilizer factorization on the test
scheme Y gives the trivial normalized self-family on the actual subvariety Y. -/
theorem normalizedSelfFamily_eq_one_of_normalizedRestriction
    {k : Type u} [Field k] {A Y : PkgI3.AbVar k}
    (j : PkgI3.AbVar.Hom Y A) (M : A.X.left.Pic)
    (h : L1.normalizedPolarizationFamily A.X M j.hom = 1) :
    L1.normalizedPolarizationFamily Y.X (Scheme.Pic.map j.hom.left M) (𝟙 Y.X) = 1 := by
  have hrestrict := normalizedPolarizationFamily_pullback j.hom M (𝟙 Y.X)
  rw [Category.id_comp, h, Scheme.Pic.map_one] at hrestrict
  exact hrestrict.symm

end ZInQ.Contrib.CloudR2Poincare.L2
