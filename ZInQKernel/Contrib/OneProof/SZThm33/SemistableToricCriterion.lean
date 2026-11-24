import ZInQKernel.Contrib.OneProof.SZThm33.GeomTateNaturality
import ZInQKernel.Contrib.OneProof.SZThm33.SemistableFixedRank
import ZInQKernel.Contrib.OneProof.SZThm33.ToricTateAssembly
import ZInQKernel.Contrib.OneProof.SZThm33.ToricOrthogonalityAssembly

noncomputable section

open CategoryTheory AlgebraicGeometry Limits MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReductSplit ZInQ.HeightSplit

namespace SZRaynaud.Ambient

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] [IsAlgClosed Ω] {O : ValuationSubring K} [IsDiscreteValuationRing O]
  {w : ValuationSubring Ω} (hw : w.comap (algebraMap K Ω) = O)
  (A : PkgI3.AbVar K) (M : GroupModelO A O) {ℓ : ℕ} [Fact ℓ.Prime] (hu : IsUnit (ℓ : O))

attribute [local instance] isCommMonObj_geomSpecialFibre

set_option synthInstance.maxHeartbeats 150000 in
set_option maxHeartbeats 1000000 in
/-- The ranks of the geometric special fibre and its split torus turn
orthogonality of their actual specializations into the two-factor inertia condition. -/
theorem levelTwo_of_semistable_toric_orthogonality (hM : M.IsNeronModel)
    (U : (Over (Spec (CommRingCat.of (ResBarO O))))) [GrpObj U] [ConnectedSpace U.left]
    (inc : U ⟶ geomSpecialFibre M) [IsOpenImmersion inc.left] [IsMonHom inc]
    (C : PkgI3.AbVar (ResBarO O)) (π : U ⟶ C.X) [IsMonHom π] [Surjective π.left]
    (r b : ℕ) (hb : C.dim = (b : WithBot ℕ∞))
    (e : (Fin r → (ResBarO O)ˣ) →* (algPt (ResBarO O) (ResBarO O) ⟶ U)) (he : Function.Injective e)
    (hk : ∀ u : algPt (ResBarO O) (ResBarO O) ⟶ U, u ≫ π = 1 ↔ u ∈ e.range)
    [FiniteDimensional ℚ_[ℓ] (VΩ A Ω ℓ)] (hdim : Module.finrank ℚ_[ℓ] (VΩ A Ω ℓ) = 2 * (b + r))
    (B : LinearMap.BilinForm ℚ_[ℓ] (VΩ A Ω ℓ)) (hB : B.Nondegenerate)
    (hI : ∀ (σ : Ω ≃ₐ[K] Ω), PkgI2.IsInertia w σ → ∀ x y : (VΩ A Ω ℓ),
      B (galVΩ A ℓ σ x) (galVΩ A ℓ σ y) = B x y)
    (hO : ∀ (x : PkgI3.Tate.T ℓ (Additive (algPt (ResBarO O) (ResBarO O) ⟶ geomSpecialFibre M)))
      (y : PkgI3.Tate.T ℓ (Additive (Fin r → (ResBarO O)ˣ))),
      B (1 ⊗ₜ[ℤ_[ℓ]] geomSpecialEmbedTate hw A M hu x)
        (1 ⊗ₜ[ℤ_[ℓ]] geomSpecialEmbedTate hw A M hu (integralTatePointMap inc e y)) = 0) :
    ∀ σ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w σ → ∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ →
      ∀ x : (VΩ A Ω ℓ), galVΩ A ℓ τ (galVΩ A ℓ σ x - x) = galVΩ A ℓ σ x - x := by
  have : IsCommMonObj (geomSpecialFibre M) := isCommMonObj_geomSpecialFibre A M
  let i := geomSpecialEmbedTate hw A M hu
  let j := i.comp (integralTatePointMap inc e)
  have hi : i.baseChange ℚ_[ℓ] = geomSpecialEmbedRational hw A M hu :=
    geomSpecialEmbedTate_baseChange hw A M hu
  have hiInj : Function.Injective (i.baseChange ℚ_[ℓ]) :=
    hi ▸ geomSpecialEmbedRational_injective hw A M hu
  have hF : (i.baseChange ℚ_[ℓ]).range = inertiaFixedSpace A w ℓ := by
    rw [hi]
    ext x
    exact (mem_range_geomSpecialEmbedRational_iff hw A M hu hM x).trans
      (mem_inertiaFixedSpace A w ℓ x).symm
  have hT : (j.baseChange ℚ_[ℓ]).range ≤ (i.baseChange ℚ_[ℓ]).range := by
    change ((i.comp (integralTatePointMap inc e)).baseChange ℚ_[ℓ]).range ≤ _
    rw [LinearMap.baseChange_comp]
    exact LinearMap.range_comp_le_range _ _
  have hdi : Module.finrank ℚ_[ℓ] (i.baseChange ℚ_[ℓ]).range = 2 * b + r := by
    rw [hi]
    exact finrank_inertiaFixedTateSubspace_of_split hw A M hu U inc C π r b hb e he hk
  have hdj : Module.finrank ℚ_[ℓ] (j.baseChange ℚ_[ℓ]).range = r :=
    finrank_range_toricTatePointMap inc r (prime_ne_zero_in_geometric_residue hu) e he i hiInj
  have hD : Module.finrank ℚ_[ℓ] (VΩ A Ω ℓ) ≤
      Module.finrank ℚ_[ℓ] (i.baseChange ℚ_[ℓ]).range +
      Module.finrank ℚ_[ℓ] (j.baseChange ℚ_[ℓ]).range := by
    rw [hdim, hdi, hdj]
    omega
  exact levelTwo_of_integral_toric_orthogonality A w ℓ i j hF hT hD B hB hI hO

end SZRaynaud.Ambient
