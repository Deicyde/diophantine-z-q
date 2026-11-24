import ZInQKernel.Contrib.OneProof.SZThm33.FiniteSpecialization
import ZInQKernel.Contrib.OneProof.SZThm33.FiniteInertiaFixed
import ZInQKernel.Contrib.OneProof.SZThm33.TateLevelSurjectivity

/-!
# Level-two unipotence implies surjectivity on special Tate spaces
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open ReductSplit ReductGlue
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]
  [IsAlgClosure K Ω] [IsAlgClosure E Ω] [IsAlgClosed Ω]
  {O : ValuationSubring K} {P : ValuationSubring E} {w : ValuationSubring Ω}
  [IsDiscreteValuationRing O] [IsDiscreteValuationRing P]
  (hw : w.comap (algebraMap K Ω) = O) (hp : w.comap (algebraMap E Ω) = P)
  (hP : P.comap (algebraMap K E) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O) (hM : M.IsNeronModel)
  (N : GroupModelO (A.baseChange E) P) (hN : N.IsNeronModel)
  (ℓ : ℕ) [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

local instance : IsCommMonObj M.G := isCommMonObj_groupModelO M
local instance : IsCommMonObj N.G := isCommMonObj_groupModelO N

include hu hM in
/-- The canonical geometric special-fibre comparison is onto on rational
Tate modules under the level-two inertia hypothesis. -/
theorem specialRationalTateComparison_surjective_of_levelTwo
    (hTwo : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ x : VΩ A Ω ℓ,
      galVΩ A ℓ σ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x) :
    Function.Surjective (specialRationalTateComparison (ℓ := ℓ) hw hp hP A M N hN) := by
  have hu' : IsUnit (ℓ : P) := by simpa only [map_natCast] using hu.map (ReductSplit.comapHom hP)
  apply specialRationalTateComparison_surjective_of_fixed hw hp hP A M N hN hu hu' hM
  intro y hy
  exact fixed_of_intermediateFixed_of_levelTwo A E w ℓ hTwo y hy

include hu hM in
/-- Every coordinate of a Tate tower of the extended special fibre lies
in the image of the comparison on points. -/
theorem specialPointComparison_lifts_coord_of_levelTwo
    (hTwo : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ x : VΩ A Ω ℓ,
      galVΩ A ℓ σ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x)
    (t : PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hp) ⟶ N.G))) (n : ℕ) :
    ∃ p : Over.mk (res ≫ base hw) ⟶ M.G,
      specialPointComparison hw hp hP A M N hN p = Additive.toMul (t.1 n) := by
  let f := (specialPointComparison hw hp hP A M N hN).toAdditive
  have h : Function.Surjective ((PkgI3.Tate.map (ℓ := ℓ) f).baseChange ℚ_[ℓ]) := by
    change Function.Surjective ((PkgI3.Tate.map (ℓ := ℓ)
      (specialPointComparison hw hp hP A M N hN).toAdditive).baseChange ℚ_[ℓ])
    rw [← specialTateComparison_eq_map]
    exact specialRationalTateComparison_surjective_of_levelTwo E hw hp hP A M hM N hN ℓ hu hTwo
  obtain ⟨p, hp₀⟩ := mem_range_of_coord_of_rationalTate_surjective f h t n
  exact ⟨Additive.toMul p, congrArg Additive.toMul hp₀⟩

#print axioms specialRationalTateComparison_surjective_of_levelTwo
#print axioms specialPointComparison_lifts_coord_of_levelTwo

end SZRaynaud.Ambient
