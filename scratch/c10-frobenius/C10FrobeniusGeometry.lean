import C10FiniteField
import StacksFrontier.AlgebraicGeometry.Variety.Frobenius.RelativeUniversalHomeomorphism

set_option autoImplicit false

/-!
# Geometric properties of the actual Frobenius group map

Reuse upstream universal-homeomorphism and local finite-type facts. Finite
and surjective Frobenius is an isogeny-type map of the actual group scheme;
this does not construct reduction models or the C10 comparison squares.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry Stacks.Frobenius

namespace C10Frobenius.Geometry

universe u

/-- Every iterate remains a universal homeomorphism by upstream composition stability. -/
theorem absolutePower_universalHomeomorphism (X : Scheme.{u}) (p : ℕ) [Fact p.Prime]
    (hX : IsInCharacteristic X p) (n : ℕ) :
    UniversalHomeomorphism (absoluteFrobeniusPow X p hX n) := by
  induction n with
  | zero =>
    rw [absoluteFrobeniusPow_zero]
    exact (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  | succ n ih =>
    rw [absoluteFrobeniusPow_succ_eq_comp]
    exact universalHomeomorphism_comp _ _
      (absoluteFrobenius_universalHomeomorphism X p hX) ih

variable {k : Type u} [Field k] [Fintype k] (p f : ℕ) [Fact p.Prime] [CharP k p]
  (hcard : Fintype.card k = p ^ f)

/-- The exact q-power group endomorphism is a universal homeomorphism. -/
theorem endomorphism_universalHomeomorphism (A : Grp (Over (Spec (.of k)))) :
    UniversalHomeomorphism (FiniteField.endomorphism p f hcard A).hom.hom.left := by
  rw [FiniteField.endomorphism_hom, geometricFrobenius_left]
  exact absolutePower_universalHomeomorphism A.X.left p _ f

/-- q-power Frobenius is surjective on the underlying actual scheme. -/
theorem endomorphism_surjective (A : Grp (Over (Spec (.of k)))) :
    Surjective (FiniteField.endomorphism p f hcard A).hom.hom.left :=
  ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
    (endomorphism_universalHomeomorphism p f hcard A)).2.2

/-- Frobenius is finite when the original group scheme is locally of finite type. -/
theorem endomorphism_isFinite (A : Grp (Over (Spec (.of k))))
    [LocallyOfFiniteType A.X.hom] :
    IsFinite (FiniteField.endomorphism p f hcard A).hom.hom.left := by
  let F : A.X ⟶ A.X := (FiniteField.endomorphism p f hcard A).hom.hom
  change IsFinite F.left
  let : IsIntegralHom F.left :=
    ((universalHomeomorphism_iff_integral_universallyInjective_surjective _).mp
      (endomorphism_universalHomeomorphism p f hcard A)).1
  let : LocallyOfFiniteType (F.left ≫ A.X.hom) := by
    rw [F.w]
    infer_instance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
    ⟨inferInstance, locallyOfFiniteType_of_comp F.left A.X.hom⟩

/-- The genuine Frobenius map of a proper finite-field group scheme is finite and surjective. -/
theorem endomorphism_finiteSurjective_of_proper (A : Grp (Over (Spec (.of k))))
    [IsProper A.X.hom] :
    IsFinite (FiniteField.endomorphism p f hcard A).hom.hom.left ∧
      Surjective (FiniteField.endomorphism p f hcard A).hom.hom.left :=
  ⟨endomorphism_isFinite p f hcard A, endomorphism_surjective p f hcard A⟩

end C10Frobenius.Geometry
