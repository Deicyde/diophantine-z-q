import ZInQKernel.Contrib.OneProof.SZThm33.FiniteComparisonCriterion
import ZInQKernel.Contrib.OneProof.SZThm33.GeomTateNaturality

/-! Surjectivity of the finite-extension comparison on the specified geometric
special fibre of the models over the extended valuation ring. -/

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReductSplit ReductGlue SmoothGroup ZInQ.HeightSplit
open ZInQ.FaltingsRestate (isCommMonObj_groupModelO)

set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option linter.style.haveILetI false

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

attribute [local instance] isCommMonObj_groupModelO isCommMonObj_geomSpecialFibre
local instance : GrpObj ((Over.pullback (gD hP)).obj M.G) := Functor.grpObjObj
local instance : IsCommMonObj ((Over.pullback (gD hP)).obj M.G) :=
  Functor.isCommMonObj_obj (F := Over.pullback (gD hP))
local instance : IsMonHom (neronModelComparison (bcDVR hP M) N hN) := neronModelComparison_hom (bcDVR hP M) N hN

set_option backward.isDefEq.respectTransparency false in
include hw hp hM hu in
/-- The geometric special-fibre comparison over the algebraic closure
specified by the extended model is surjective on rational Tate modules
under the level-two inertia hypothesis. -/
theorem geomSpecialComparison_rationalTate_surjective_of_levelTwo
    (hTwo : ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ t : VΩ A Ω ℓ,
      galVΩ A ℓ σ (galVΩ A ℓ σ t - t) = galVΩ A ℓ σ t - t) :
    Function.Surjective ((mapModelTate (ℓ := ℓ)
      (geomSpecialModelMap (bcDVR hP M) N (neronModelComparison (bcDVR hP M) N hN))
      (Spec.map (CommRingCat.ofHom (algebraMap (ResBarO P) (ResBarO P))))).baseChange ℚ_[ℓ]) := by
  let F := mapModelTate (ℓ := ℓ)
      (geomSpecialModelMap (bcDVR hP M) N (neronModelComparison (bcDVR hP M) N hN))
      (Spec.map (CommRingCat.ofHom (algebraMap (ResBarO P) (ResBarO P))))
  let Fa := mapModelTate (ℓ := ℓ) (neronModelComparison (bcDVR hP M) N hN) (res ≫ base hp)
  let e : PkgI3.Tate.T ℓ (Additive (algPt (ResBarO P) (ResBarO P) ⟶ geomSpecialFibre (bcDVR hP M))) ≃ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hp) ⟶ (bcDVR hP M).G)) :=
    geomSpecialTateEquiv hp (A.baseChange E) (bcDVR hP M)
  let e' : PkgI3.Tate.T ℓ (Additive (algPt (ResBarO P) (ResBarO P) ⟶ geomSpecialFibre N)) ≃ₗ[ℤ_[ℓ]]
      PkgI3.Tate.T ℓ (Additive (Over.mk (res ≫ base hp) ⟶ N.G)) :=
    geomSpecialTateEquiv hp (A.baseChange E) N
  let E₀ := LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ e
  let E₁ := LinearEquiv.baseChange ℤ_[ℓ] ℚ_[ℓ] _ _ e'
  let b := pullbackTestTate (ℓ := ℓ) (gD hP) (res ≫ base hp) (res ≫ base hw)
    (by rw [Category.assoc, ambientBase_comp hw hp hP]) M.G
  have comm : e'.toLinearMap.comp F = Fa.comp e.toLinearMap :=
    LinearMap.ext (geomSpecialTateEquiv_modelHom hp (A.baseChange E) (bcDVR hP M) N (neronModelComparison (bcDVR hP M) N hN))
  have commQ : E₁.toLinearMap.comp (F.baseChange ℚ_[ℓ]) =
      (Fa.baseChange ℚ_[ℓ]).comp E₀.toLinearMap := by
    change (e'.toLinearMap.baseChange ℚ_[ℓ]).comp (F.baseChange ℚ_[ℓ]) =
      (Fa.baseChange ℚ_[ℓ]).comp (e.toLinearMap.baseChange ℚ_[ℓ])
    rw [← LinearMap.baseChange_comp, ← LinearMap.baseChange_comp, comm]
  have fac : specialRationalTateComparison (ℓ := ℓ) hw hp hP A M N hN =
      (Fa.baseChange ℚ_[ℓ]).comp (b.baseChange ℚ_[ℓ]) := by
    change (Fa.comp b).baseChange ℚ_[ℓ] = _
    exact LinearMap.baseChange_comp _ _
  intro t
  obtain ⟨s, hs⟩ := specialRationalTateComparison_surjective_of_levelTwo E hw hp hP A M hM
    N hN ℓ hu hTwo (E₁ t)
  let u := E₀.symm (b.baseChange ℚ_[ℓ] s)
  refine ⟨u, E₁.injective ?_⟩
  have h := DFunLike.congr_fun commQ u
  change E₁ (F.baseChange ℚ_[ℓ] u) = Fa.baseChange ℚ_[ℓ] (E₀ u) at h
  rw [show E₀ u = b.baseChange ℚ_[ℓ] s from E₀.apply_symm_apply _] at h
  have hs' := DFunLike.congr_fun fac s
  change specialRationalTateComparison (ℓ := ℓ) hw hp hP A M N hN s =
    Fa.baseChange ℚ_[ℓ] (b.baseChange ℚ_[ℓ] s) at hs'
  exact h.trans (hs'.symm.trans hs)

#print axioms geomSpecialComparison_rationalTate_surjective_of_levelTwo

end SZRaynaud.Ambient
