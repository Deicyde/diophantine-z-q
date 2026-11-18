import CommonFrobeniusFeedFirst
import ActualTorusMultiplierThird

/-!
# Native model hypotheses and one common Frobenius power

Quasi-compactness of the original model supplies compactness of its actual
special fibre. Smoothness and the actual open subgroup supply the local
finite presentation needed by the torus spread-out theorem. The original
prime-power torsion bounds for two generic varieties and the torus action
then use one arithmetic lift and one positive common power. No finite
point set, uniform bound, desired injection or eigenaction is an input.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace SemistableGeometry.CommonNativeModelData

open SemistableGeometry.CommonFrobeniusFeed
open SemistableGeometry.ActualTorusMultiplier
open SemistableGeometry.SpecialPointBinding
open SemistableGeometry.IntegralGalois
open RaynaudWild.FrobDescent

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- The original model's quasi-compact structure map supplies compactness of the actual special fibre. -/
theorem specialFibre_compact (N : Over (Spec (CommRingCat.of O))) [QuasiCompact N.hom] :
    CompactSpace (specialFibre N).left := by
  letI : QuasiCompact (specialFibre N).hom := by
    change QuasiCompact (CategoryTheory.Limits.pullback.snd N.hom (specialBase (O := O)))
    infer_instance
  exact QuasiCompact.compactSpace_of_compactSpace (specialFibre N).hom

/-- The closed original fixed-torsion bound requires only the native quasi-compact model data. -/
theorem uniform_bound_from_model {A : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [IsSeparated N.hom] [Smooth N.hom]
    [QuasiCompact N.hom]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O)) :
    ∃ (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
      (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1),
      ∀ r : ℕ, 0 < r → ∃ c : ℕ, ∀ n : ℕ,
        Nat.card (ToricFinitePart.fixedIn ℓ (σ ^ r) (ToricFinitePart.inertiaFixed ℓ A w n)) ∣ ℓ ^ c := by
  letI : CompactSpace (specialFibre N).left := specialFibre_compact N
  exact exists_common_lift_uniform_bound N gen hgen hN w hw ℓ hℓ

/-- Two actual original-variety torsion bounds and the natural torus action share one lift and one common power. -/
theorem common_power_two_bounds_and_torus {A A' : PkgI3.AbVar K}
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [IsSeparated N.hom] [Smooth N.hom]
    [QuasiCompact N.hom]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (N' : Over (Spec (CommRingCat.of O))) [GrpObj N'] [IsSeparated N'.hom] [Smooth N'.hom]
    [QuasiCompact N'.hom]
    (gen' : (Over.pullback (base (O := O))).obj N' ≅ A'.X)
    (hgen' : letI : GrpObj ((Over.pullback (base (O := O))).obj N') := Functor.grpObjObj
      IsMonHom gen'.hom)
    (hN' : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N' => (Over.pullback (base (O := O))).map f ≫ gen'.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O))
    (U : Over (Spec (CommRingCat.of (IsLocalRing.ResidueField O)))) [GrpObj U]
    (inc : U ⟶ specialFibre N) [IsOpenImmersion inc.left] (rk : ℕ)
    (e : ∀ (R : Type) [CommRing R] [Algebra (AlgebraicClosure (IsLocalRing.ResidueField O)) R],
      letI := algK' (φbar' (IsLocalRing.ResidueField O)) R
      (Fin rk → Rˣ) →* (algPt' (IsLocalRing.ResidueField O) R ⟶ U))
    (he : ResTTorusNat (IsLocalRing.ResidueField O) U rk e) :
    ∃ (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
      (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
      (p : ℕ), 0 < p ∧ ∀ r : ℕ, 0 < r →
        (∃ c : ℕ, ∀ n : ℕ,
          Nat.card (ToricFinitePart.fixedIn ℓ (σ ^ (p * r)) (ToricFinitePart.inertiaFixed ℓ A w n)) ∣ ℓ ^ c) ∧
        (∃ c' : ℕ, ∀ n : ℕ,
          Nat.card (ToricFinitePart.fixedIn ℓ (σ ^ (p * r)) (ToricFinitePart.inertiaFixed ℓ A' w n)) ∣ ℓ ^ c') ∧
        (∀ t : Fin rk → (IsLocalRing.ResidueField w)ˣ,
          specialActionArrow hw (σ ^ (p * r)) (pow_mem hD _) ≫ actualTorusPoint hw U rk e t =
            actualTorusPoint hw U rk e t ^ (Nat.card (IsLocalRing.ResidueField O) ^ (p * r))) := by
  letI : CompactSpace (specialFibre N).left := specialFibre_compact N
  letI : CompactSpace (specialFibre N').left := specialFibre_compact N'
  letI : LocallyOfFinitePresentation (specialFibre N).hom := lfp_baseChange_of_smooth N
  letI : LocallyOfFinitePresentation U.hom := lfp_of_openImmersion inc
  obtain ⟨σ, hD, hcong⟩ := FrobLift.exists_frobenius_lift hw
  obtain ⟨n, hn⟩ := actual_torus_frobenius_multiplier hw U rk e he σ hD hcong
  refine ⟨σ, hD, hcong, n.factorial, Nat.factorial_pos n, ?_⟩
  intro r hr
  have hpr : 0 < n.factorial * r := Nat.mul_pos (Nat.factorial_pos n) hr
  exact ⟨uniform_bound_for_lift N gen hgen hN w hw ℓ hℓ σ hD hcong _ hpr,
    uniform_bound_for_lift N' gen' hgen' hN' w hw ℓ hℓ σ hD hcong _ hpr, hn r⟩

end SemistableGeometry.CommonNativeModelData
