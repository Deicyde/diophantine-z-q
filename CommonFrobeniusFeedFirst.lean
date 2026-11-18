import OriginalFixedPrimaryFeedSecond

/-!
# One common arithmetic Frobenius for the original uniform torsion bound

The finite original subgroup bound is derived for any given actual
Frobenius lift. The existence form retains the lift's integral congruence,
so the same element and same positive power can be used for the special
points, cyclotomic pairing action and toric multiplier. Iterated
congruence is the previously proved native Frobenius theorem.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace SemistableGeometry.CommonFrobeniusFeed

open SemistableGeometry.OriginalFixedPrimary
open SemistableGeometry.OriginalFixedPrimaryFeed
open SemistableGeometry.IntegralGalois
open SemistableGeometry.SpecialPointBinding

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω] {A : PkgI3.AbVar K}

/-- The uniform bound is proved for the same actual lift chosen for all other geometric suppliers. -/
theorem uniform_bound_for_lift
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [IsSeparated N.hom] [Smooth N.hom]
    [CompactSpace (specialFibre N).left]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O))
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
    (r : ℕ) (hr : 0 < r) : ∃ c : ℕ, ∀ n : ℕ,
      Nat.card (ToricFinitePart.fixedIn ℓ (σ ^ r) (ToricFinitePart.inertiaFixed ℓ A w n)) ∣ ℓ ^ c := by
  letI : Finite (fixedPrimary ℓ (σ ^ r) w A) :=
    finite_fixedPrimary N gen hgen hN w hw ℓ hℓ σ hD hcong r hr
  letI : Finite (Additive (fixedPrimary ℓ (σ ^ r) w A)) := inferInstance
  refine ⟨(Nat.card (Additive (fixedPrimary ℓ (σ ^ r) w A))).factorization ℓ, ?_⟩
  exact ToricFinitePart.fixed_card_dvd_of_injective ℓ (σ ^ r)
    (ToricFinitePart.inertiaFixed ℓ A w)
    (levelInclusion ℓ A w (σ ^ r)) (levelInclusion_injective ℓ A w (σ ^ r))

/-- Existence retains the actual Frobenius congruence rather than losing the common-lift binding. -/
theorem exists_common_lift_uniform_bound
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [IsSeparated N.hom] [Smooth N.hom]
    [CompactSpace (specialFibre N).left]
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
  obtain ⟨σ, hD, hcong⟩ := FrobLift.exists_frobenius_lift hw
  exact ⟨σ, hD, hcong, fun r hr ↦ uniform_bound_for_lift N gen hgen hN w hw ℓ hℓ σ hD hcong r hr⟩

/-- The multiplier power is the literal iterated valuation congruence of that same original lift. -/
theorem frobenius_power_congruence (w : ValuationSubring Ω)
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K) (q : ℕ)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ q) < 1) (r : ℕ) :
    ∀ x ∈ w, w.valuation ((σ ^ r) x - x ^ (q ^ r)) < 1 :=
  FrobLift.pow_congr hD hcong r

end SemistableGeometry.CommonFrobeniusFeed
