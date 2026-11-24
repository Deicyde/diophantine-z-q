import ZInQKernel.Contrib.OneProof.SZThm33.SemistableTateRank
import Mathlib.RingTheory.Flat.Localization

/-!
# The toric Tate map of a subgroup inclusion
-/

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

namespace SZRaynaud

variable {S : Scheme.{0}} {P U G : Over S} [GrpObj U] [GrpObj G] [IsCommMonObj G]
    {T : Type*} [CommGroup T] {ℓ : ℕ} [Fact ℓ.Prime]

/-- Rational Tate functoriality for a point map followed by a group
scheme homomorphism. -/
def rationalTatePointMap (i : U ⟶ G) [IsMonHom i] (e : T →* (P ⟶ U)) :
    TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive T)) →ₗ[ℚ_[ℓ]]
      TensorProduct ℤ_[ℓ] ℚ_[ℓ] (PkgI3.Tate.T ℓ (Additive (P ⟶ G))) :=
  let f := ((mapGroupPoint (S := S) (P := P) (G := U) (H := G) i).comp e).toAdditive
  (PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]

theorem rationalTatePointMap_injective (i : U ⟶ G) [IsMonHom i] [Mono i.left]
    (e : T →* (P ⟶ U)) (he : Function.Injective e) :
    Function.Injective (rationalTatePointMap (ℓ := ℓ) i e) := by
  let f := ((mapGroupPoint (S := S) (P := P) (G := U) (H := G) i).comp e).toAdditive
  have hf : Function.Injective f := by
    intro x y h
    apply Additive.toMul.injective
    apply he
    apply Over.OverMorphism.ext
    exact (cancel_mono i.left).mp (congrArg (fun point : Additive (P ⟶ G) =>
      (Additive.toMul point).left) h)
  have hT : Function.Injective (PkgI3.Tate.map f (ℓ := ℓ)) := by
    intro x y h
    apply Subtype.ext
    funext n
    apply hf
    exact congrArg (fun t : PkgI3.Tate.T ℓ (Additive (P ⟶ G)) => t.1 n) h
  have : Module.Flat ℤ_[ℓ] ℚ_[ℓ] := IsLocalization.flat ℚ_[ℓ] (nonZeroDivisors ℤ_[ℓ])
  exact Module.Flat.lTensor_preserves_injective_linearMap _ hT

#print axioms rationalTatePointMap_injective

end SZRaynaud
