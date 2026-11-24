import ZInQKernel.Contrib.OneProof.SZThm33.SemistableToricCriterion
import ZInQKernel.Contrib.OneProof.SZThm33.SemistableDimensions
import ZInQKernel.Contrib.OneProof.DirectWeil.AmbientWeilPairing

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReductSplit ZInQ.HeightSplit
open PicDict.DirectPairing

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] [IsAlgClosed Ω] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {w : ValuationSubring Ω} (hw : w.comap (algebraMap K Ω) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O) {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

attribute [local instance] isCommMonObj_geomSpecialFibre

set_option synthInstance.maxHeartbeats 150000 in
set_option maxHeartbeats 1000000 in
/-- Finite-level Weil vanishing for the given polarization, tested on the
geometric special fibre and its actual split torus, implies the inertia condition. -/
theorem levelTwo_of_semistable_weil_levels (hM : M.IsNeronModel)
    (U : (Over (Spec (CommRingCat.of (ResBarO O))))) [GrpObj U] [ConnectedSpace U.left]
    (inc : U ⟶ geomSpecialFibre M) [IsOpenImmersion inc.left] [IsMonHom inc]
    (C : PkgI3.AbVar (ResBarO O)) (π : U ⟶ C.X) [IsMonHom π] [Flat π.left] [Surjective π.left]
    (r : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (ResBarO O) R], (Fin r → Rˣ) →* (algPt (ResBarO O) R ⟶ U))
    (he : ∀ (R : Type) [CommRing R] [Algebra (ResBarO O) R], Function.Injective (e R))
    (hk : ∀ (R : Type) [CommRing R] [Algebra (ResBarO O) R] (u : algPt (ResBarO O) R ⟶ U),
      u ≫ π = 1 ↔ u ∈ (e R).range)
    (hn : ∀ (R S' : Type) [CommRing R] [CommRing S'] [Algebra (ResBarO O) R] [Algebra (ResBarO O) S']
      (f : R →ₐ[(ResBarO O)] S') (t : Fin r → Rˣ),
      e S' (fun j => Units.map (f : R →* S') (t j)) = algPtMap f ≫ e R t)
    (L : A.X.left.Pic) (hL : {x : A.Pt (AlgebraicClosure K) | polarization A L x = 1}.Finite)
    (eΩ : AlgebraicClosure K ≃ₐ[K] Ω) (hℓ : (ℓ : K) ≠ 0)
    (hvanish : ∀ (x : PkgI3.Tate.T ℓ (Additive (algPt (ResBarO O) (ResBarO O) ⟶ geomSpecialFibre M)))
        (y : PkgI3.Tate.T ℓ (Additive (Fin r → (ResBarO O)ˣ))) (n : ℕ),
      let x' := (tateEquiv A eΩ).symm (geomSpecialEmbedTate hw A M hu x)
      let y' := (tateEquiv A eΩ).symm
        (geomSpecialEmbedTate hw A M hu (integralTatePointMap inc (e (ResBarO O)) y))
      (levelPairing A L hℓ n (levelPoint A x' n) (levelPoint A y' n)).val = 1) :
    ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      ∀ x : (VΩ A Ω ℓ), galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  obtain ⟨g, b, hg, _, hb, hgb⟩ :=
    ZInQ.SemistableDimensions.semistable_dimensions_of_split_presentation M U inc C π r e he hk (fun R S' _ _ _ _ f t => hn R S' f t)
  obtain ⟨hfin, B, hdim, hB, _, hGal, hZero⟩ :=
    exists_ambientWeilForm_of_finite_kernel A L eΩ hℓ hL g hg
  have hℓw : IsUnit (ℓ : w) := by simpa using hu.map (comapHom hw)
  have hI (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) (x y : (VΩ A Ω ℓ)) :
      B (galVΩ A ℓ σ x) (galVΩ A ℓ σ y) = B x y := by
    rw [hGal, cyclotomicCharacter_eq_one_of_inertia w hℓw σ hσ, Units.val_one, map_one, _root_.one_mul]
  refine levelTwo_of_semistable_toric_orthogonality hw A M hu hM U inc C π r b hb (e (ResBarO O))
    (he (ResBarO O)) (hk (ResBarO O)) (hdim.trans (congrArg (2 * ·) hgb)) B hB hI ?_
  intro x y
  apply (hZero _ _).mpr
  apply Subtype.ext
  funext n
  rw [tatePairing_apply]
  exact congrArg Additive.ofMul (hvanish x y n)

end SZRaynaud.Ambient
