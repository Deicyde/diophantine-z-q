import ZInQKernel.HDecomp.Faltings.Leaves
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # GR14Printed (B2): an isogeny as printed is an isogeny in the Lean sense

Gaudron–Rémond, Duke Math. J. 163 (2014), §2, p. 2062, call an isogeny a homomorphism of abelian
varieties that is "surjectif de noyau fini". The leaves use `ZInQ.DefFaltings.IsIsogeny`: a
homomorphism that is finite and surjective. This file states the printed notion,
`IsIsogenyPrinted` (the kernel `A ×_{φ, B, e} Spec K` is a finite `K`-scheme), and proves the two
notions equal (`isIsogenyPrinted_iff`).

* §1 (any cartesian monoidal category with pullbacks): for a homomorphism `φ : G → H` of group
  objects, `G ×_H G ≅ G × ker φ` over the first factor, `(a, k) ↦ (a, a k)` (`translateIso`).
* §2 (schemes): Lean ⇒ print by base change (`isIsogenyPrinted_of_isIsogeny`); print ⇒ Lean: the
  first projection `A ×_B A → A` is a base change of `ker φ → Spec K`, hence finite, so every fibre
  of `φ` is finite (the fibre through `a` is the image of the fibre of the projection over `a`);
  `φ` is proper (`A` proper, `B` separated), so it is finite by Mathlib's
  `IsFinite.of_isProper_of_locallyQuasiFinite` (`isIsogeny_of_isIsogenyPrinted`).
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open PkgI3 (AbVar)
open ZInQ.DefFaltings

set_option linter.unusedSectionVars false

namespace ZInQ.GR14Printed

/-! ## §1. `G ×_H G ≅ G × ker φ` -/

section Translate

variable {C : Type*} [Category C] [CartesianMonoidalCategory C] [HasPullbacks C]
  {G H : C} [GrpObj G] [GrpObj H] (φ : G ⟶ H) [IsMonHom φ]

/-- The kernel of a homomorphism of group objects: `G ×_{φ, H, e} 𝟙`. -/
abbrev kerGrp : C := pullback φ (η[H] : 𝟙_ C ⟶ H)

/-- The inclusion of the kernel composed with `φ` is the unit. -/
theorem kerGrp_fst_comp : pullback.fst φ (η[H] : 𝟙_ C ⟶ H) ≫ φ = 1 := by
  rw [pullback.condition]
  have : pullback.snd φ (η[H] : 𝟙_ C ⟶ H) = toUnit _ := toUnit_unique _ _
  rw [this]
  rfl

/-- `(a, k) ↦ (a, a k)`. -/
def translate : G ⊗ kerGrp φ ⟶ pullback φ φ :=
  pullback.lift (fst _ _) (fst _ _ * (snd _ _ ≫ pullback.fst φ (η[H] : 𝟙_ C ⟶ H))) (by
    rw [MonObj.mul_comp, Category.assoc, kerGrp_fst_comp, MonObj.comp_one, _root_.mul_one])

/-- `(a, b) ↦ (a, a⁻¹ b)`. -/
def untranslate : pullback φ φ ⟶ G ⊗ kerGrp φ :=
  lift (pullback.fst φ φ)
    (pullback.lift ((pullback.fst φ φ)⁻¹ * pullback.snd φ φ) (toUnit _) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, pullback.condition, _root_.inv_mul_cancel]
      rfl))

/-- **`G ×_H G ≅ G × ker φ`** over the first factor. -/
def translateIso : G ⊗ kerGrp φ ≅ pullback φ φ where
  hom := translate φ
  inv := untranslate φ
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp [translate, untranslate]
    · apply pullback.hom_ext
      · simp only [translate, untranslate, Category.assoc, lift_snd, pullback.lift_fst,
          Category.id_comp, MonObj.comp_mul, GrpObj.comp_inv,
          pullback.lift_snd]
        group
      · exact toUnit_unique _ _
  inv_hom_id := by
    apply pullback.hom_ext
    · simp [translate, untranslate]
    · simp only [translate, untranslate, Category.assoc, pullback.lift_snd, MonObj.comp_mul,
        lift_fst, lift_snd_assoc, pullback.lift_fst, Category.id_comp]
      group

/-- The inverse of `translateIso` followed by the first factor is the first projection. -/
theorem translateIso_inv_fst :
    (translateIso φ).inv ≫ fst G (kerGrp φ) = pullback.fst φ φ := by
  simp [translateIso, untranslate]

end Translate

/-! ## §2. The two notions of isogeny -/

section Schemes

variable {K : Type} [Field K]

/-- **The kernel of `φ : A → B`** as a `K`-scheme: `A ×_{φ, B, e} Spec K`. -/
abbrev kerObj {A B : AbVar K} (φ : A.X ⟶ B.X) : Over (Spec (CommRingCat.of K)) :=
  kerGrp φ

/-- **An isogeny as printed** (Gaudron–Rémond, Duke Math. J. 163 (2014), §2, p. 2062: "surjectif
de noyau fini"): a homomorphism, surjective, whose kernel `A ×_{φ, B, e} Spec K` is a finite
`K`-scheme (the kernel as a group scheme; in characteristic `0` it is étale, so this is the same as
finitely many `K̄`-points). -/
def IsIsogenyPrinted {A B : AbVar K} (φ : A.X ⟶ B.X) : Prop :=
  IsMonHom φ ∧ Surjective φ.left ∧ IsFinite (kerObj φ).hom

/-- The structure morphism of the kernel is the second projection, read in schemes. -/
theorem kerObj_hom {A B : AbVar K} (φ : A.X ⟶ B.X) :
    (kerObj φ).hom = (PreservesPullback.iso (Over.forget _) φ
      (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B.X)).hom ≫
      pullback.snd φ.left (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B.X).left := by
  have h1 := PreservesPullback.iso_hom_snd (Over.forget (Spec (CommRingCat.of K))) φ
    (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B.X)
  have h2 := Over.w (pullback.snd φ (η[B.X] : 𝟙_ (Over (Spec (CommRingCat.of K))) ⟶ B.X))
  rw [Over.tensorUnit_hom] at h2
  rw [← h2]
  exact (Category.comp_id _).trans h1.symm

/-- **Lean ⇒ print**: a finite morphism has a finite kernel (base change). -/
theorem isIsogenyPrinted_of_isIsogeny {A B : AbVar K} {φ : A.X ⟶ B.X} (h : IsIsogeny φ) :
    IsIsogenyPrinted φ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨h1, h3, ?_⟩
  rw [kerObj_hom]
  infer_instance

/-- **`A ×_B A → A` is finite when the kernel is**: in schemes, the first projection is, up to
isomorphisms, the base change of `ker φ → Spec K` along `A → Spec K` (`translateIso`). -/
theorem isFinite_pullback_fst {A B : AbVar K} (φ : A.X ⟶ B.X) [IsMonHom φ]
    [IsFinite (kerObj φ).hom] : IsFinite (pullback.fst φ.left φ.left) := by
  let F := Over.forget (Spec (CommRingCat.of K))
  have e1 : pullback.fst φ.left φ.left =
      (PreservesPullback.iso F φ φ).inv ≫ (translateIso φ).inv.left ≫
        pullback.fst A.X.hom (kerObj φ).hom := by
    rw [Iso.eq_inv_comp]
    refine (PreservesPullback.iso_hom_fst F φ φ).trans ?_
    rw [← Over.fst_left, ← Over.comp_left, translateIso_inv_fst]
    rfl
  have : IsIso (translateIso φ).inv.left := F.map_isIso (translateIso φ).inv
  rw [e1]
  infer_instance

/-- **The fibres of `φ` are finite** when its kernel is finite: the fibre through `a` is the image
under the second projection of the fibre of `A ×_B A → A` over `a`. -/
theorem finite_preimage_singleton {A B : AbVar K} (φ : A.X ⟶ B.X) [IsMonHom φ]
    [IsFinite (kerObj φ).hom] (y : B.X.left) : (φ.left ⁻¹' {y}).Finite := by
  have := isFinite_pullback_fst φ
  have hfin := (locallyQuasiFinite_iff_finite_preimage_singleton
    (f := pullback.fst φ.left φ.left)).mp inferInstance
  rcases (φ.left ⁻¹' {y}).eq_empty_or_nonempty with h | ⟨a, ha⟩
  · rw [h]
    exact Set.finite_empty
  · refine ((hfin a).image (pullback.snd φ.left φ.left)).subset ?_
    intro x hx
    obtain ⟨z, hz1, hz2⟩ :=
      Scheme.Pullback.exists_preimage_pullback (f := φ.left) (g := φ.left) a x
        ((show φ.left a = y from ha).trans (show φ.left x = y from hx).symm)
    exact ⟨z, hz1, hz2⟩

/-- **A homomorphism with finite kernel is finite**: it is proper (`A` proper, `B` separated) and
has finite fibres, so it is finite (proper and locally quasi-finite). -/
theorem isFinite_of_finiteKer {A B : AbVar K} (φ : A.X ⟶ B.X) [IsMonHom φ]
    [IsFinite (kerObj φ).hom] : IsFinite φ.left := by
  have : IsProper (φ.left ≫ B.X.hom) := by
    rw [Over.w φ]
    infer_instance
  have : IsProper φ.left := IsProper.of_comp φ.left B.X.hom
  have : LocallyQuasiFinite φ.left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (finite_preimage_singleton φ)
  exact IsFinite.of_isProper_of_locallyQuasiFinite _

/-- **Print ⇒ Lean** (B2): an isogeny as printed is an isogeny in the Lean sense. -/
theorem isIsogeny_of_isIsogenyPrinted {A B : AbVar K} {φ : A.X ⟶ B.X}
    (h : IsIsogenyPrinted φ) : IsIsogeny φ := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, isFinite_of_finiteKer φ, h2⟩

/-- The two notions agree. -/
theorem isIsogenyPrinted_iff {A B : AbVar K} (φ : A.X ⟶ B.X) :
    IsIsogenyPrinted φ ↔ IsIsogeny φ :=
  ⟨isIsogeny_of_isIsogenyPrinted, isIsogenyPrinted_of_isIsogeny⟩

end Schemes

end ZInQ.GR14Printed
