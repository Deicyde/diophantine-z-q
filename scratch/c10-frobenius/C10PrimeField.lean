import C10Frobenius

set_option autoImplicit false

/-!
# Frobenius over the prime field

This specialization identifies the canonical twist only over `ZMod p`, where
base Frobenius is identity. It does not identify twists over general
characteristic-p fields or construct the C10 good-reduction comparison data.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

namespace C10Frobenius.PrimeField

variable (p : ℕ) [Fact p.Prime]

/-- Absolute Frobenius is identity on the spectrum of the prime field. -/
theorem baseFrobenius_eq_id :
    absoluteFrobenius (Spec (.of (ZMod p))) p
      (isInCharacteristic_spec (ZMod p) p) = 𝟙 _ := by
  simpa using absoluteFrobenius_pow_comp_hom
    (Over.mk (𝟙 (Spec (.of (ZMod p))))) p 1 (by simp)

/-- The canonical first-projection isomorphism from the prime-field twist. -/
def twistIso :
    frobeniusTwist (Spec (.of (ZMod p))) p
        (isInCharacteristic_spec (ZMod p) p) ≅ 𝟭 (Over (Spec (.of (ZMod p)))) := by
  letI : IsIso (absoluteFrobenius (Spec (.of (ZMod p))) p
      (isInCharacteristic_spec (ZMod p) p)) := by
    rw [baseFrobenius_eq_id]
    infer_instance
  refine NatIso.ofComponents
    (fun X => Over.isoMk (asIso (CategoryTheory.Limits.pullback.fst X.hom _)) ?_) ?_
  · change CategoryTheory.Limits.pullback.fst X.hom _ ≫ X.hom =
      CategoryTheory.Limits.pullback.snd X.hom _
    rw [CategoryTheory.Limits.pullback.condition, baseFrobenius_eq_id, Category.comp_id]
  · intro X Y f
    apply Over.OverMorphism.ext
    simp [frobeniusTwist, Over.pullback_map_left]

/-- The twist identification is the canonical first projection, not a chosen automorphism. -/
@[simp] theorem twistIso_hom_left (X : Over (Spec (.of (ZMod p)))) :
    ((twistIso p).hom.app X).left = CategoryTheory.Limits.pullback.fst X.hom
      (absoluteFrobenius (Spec (.of (ZMod p))) p
        (isInCharacteristic_spec (ZMod p) p)) := rfl

attribute [local instance] C10Frobenius.twistMonoidal

/-- The same canonical twist identification, lifted to the actual group schemes. -/
def groupTwistIso (A : Grp (Over (Spec (.of (ZMod p))))) :
    groupTwist (Spec (.of (ZMod p))) p (isInCharacteristic_spec (ZMod p) p) A ≅ A :=
  (Functor.mapGrpNatIso (twistIso p) ≪≫ Functor.mapGrpIdIso).app A

/-- The group isomorphism has the same canonical first projection on schemes. -/
@[simp] theorem groupTwistIso_hom_left (A : Grp (Over (Spec (.of (ZMod p))))) :
    (groupTwistIso p A).hom.hom.hom.left = CategoryTheory.Limits.pullback.fst A.X.hom
      (absoluteFrobenius (Spec (.of (ZMod p))) p
        (isInCharacteristic_spec (ZMod p) p)) := by
  change ((twistIso p).hom.app A.X).left ≫ 𝟙 _ = _
  rw [Category.comp_id, twistIso_hom_left]

/-- Frobenius as an endomorphism of any actual group scheme over the prime field. -/
def endomorphism (A : Grp (Over (Spec (.of (ZMod p))))) : A ⟶ A :=
  relativeHom (Spec (.of (ZMod p))) p (isInCharacteristic_spec (ZMod p) p) A ≫
    (groupTwistIso p A).hom

/-- The packaged endomorphism is exactly absolute Frobenius on the underlying scheme. -/
@[simp] theorem endomorphism_left (A : Grp (Over (Spec (.of (ZMod p))))) :
    (endomorphism p A).hom.hom.left = absoluteFrobenius A.X.left p
      (isInCharacteristic_of_over A.X) := by
  change (relativeHom (Spec (.of (ZMod p))) p
      (isInCharacteristic_spec (ZMod p) p) A).hom.hom.left ≫
        (groupTwistIso p A).hom.hom.hom.left = _
  rw [relativeHom_hom, groupTwistIso_hom_left]
  exact relativeFrobenius_fst _ p _ A.X

/-- This adapter packages the existing prime-field geometric Frobenius without changing its map. -/
@[simp] theorem endomorphism_hom_eq_geometricFrobenius
    (A : Grp (Over (Spec (.of (ZMod p))))) :
    (endomorphism p A).hom.hom = geometricFrobenius A.X p 1 (by simp) := by
  apply Over.OverMorphism.ext
  rw [endomorphism_left, geometricFrobenius_left]
  simp

/-- The existing geometric Frobenius preserves the actual prime-field group law. -/
theorem isMonHom_geometricFrobenius (A : Grp (Over (Spec (.of (ZMod p))))) :
    IsMonHom (geometricFrobenius A.X p 1 (by simp)) := by
  rw [← endomorphism_hom_eq_geometricFrobenius]
  infer_instance

/-- The prime-field group endomorphism is natural for genuine group-scheme morphisms. -/
theorem endomorphism_naturality {A B : Grp (Over (Spec (.of (ZMod p))))} (f : A ⟶ B) :
    endomorphism p A ≫ f = f ≫ endomorphism p B := by
  apply Grp.hom_ext
  apply Over.OverMorphism.ext
  change (endomorphism p A).hom.hom.left ≫ f.hom.hom.left =
    f.hom.hom.left ≫ (endomorphism p B).hom.hom.left
  rw [endomorphism_left, endomorphism_left]
  exact absoluteFrobenius_naturality f.hom.hom.left p _ _

/-- Frobenius on test-scheme points is precomposition by their absolute Frobenius. -/
theorem endomorphism_onPoints (A : Grp (Over (Spec (.of (ZMod p)))))
    {T : Over (Spec (.of (ZMod p)))} (x : T ⟶ A.X) :
    (x ≫ (endomorphism p A).hom.hom).left =
      absoluteFrobenius T.left p (isInCharacteristic_of_over T) ≫ x.left := by
  change x.left ≫ (endomorphism p A).hom.hom.left = _
  rw [endomorphism_left]
  exact (absoluteFrobenius_naturality x.left p _ _).symm

end C10Frobenius.PrimeField
