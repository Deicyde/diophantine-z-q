import OriginalFixedPrimaryFifth
import ToricFinitePart.InertiaDefectV002

/-!
# The actual uniform finite-group feed for original inertia-fixed torsion

The finite group is the actual original prime-power torsion subgroup proved
finite by inertia descent, Frobenius-fixed special points and reduction
injection. Every Frobenius-fixed inertia-fixed level point includes into it.
This inclusion is an injective additive homomorphism, so the existing
finite-group order theorem gives the uniform divisibility bound. No finite
group, desired injection or fixed-point bound is supplied as an input.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace SemistableGeometry.OriginalFixedPrimaryFeed

open SemistableGeometry.OriginalFixedPrimary
open SemistableGeometry.IntegralGalois
open SemistableGeometry.SpecialPointBinding

variable {K : Type} [Field K] {Ω : Type} [Field Ω] [Algebra K Ω]

/-- The literal inclusion of an original fixed inertia-torsion level into the original fixed primary group. -/
def levelInclusion (ℓ : ℕ) (A : PkgI3.AbVar K) (w : ValuationSubring Ω)
    (ψ : Ω ≃ₐ[K] Ω) (n : ℕ) :
    ToricFinitePart.fixedIn ℓ ψ (ToricFinitePart.inertiaFixed ℓ A w n) →+
      Additive (fixedPrimary ℓ ψ w A) where
  toFun y := Additive.ofMul ⟨Additive.toMul y.1.1, by
    refine ⟨⟨n, ?_⟩, ?_, ?_⟩
    · have h : (ℓ ^ n) • y.1.1 = 0 := y.1.2
      exact congrArg Additive.toMul h
    · intro τ hτ
      exact congrArg (fun z : ToricFinitePart.level ℓ A Ω n ↦ Additive.toMul z.1)
        (y.2.1 τ hτ)
    · exact congrArg (fun z : ToricFinitePart.level ℓ A Ω n ↦ Additive.toMul z.1) y.2.2⟩
  map_zero' := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Additive.toMul.injective
    apply Subtype.ext
    rfl

/-- This actual inclusion is injective. -/
theorem levelInclusion_injective (ℓ : ℕ) (A : PkgI3.AbVar K) (w : ValuationSubring Ω)
    (ψ : Ω ≃ₐ[K] Ω) (n : ℕ) : Function.Injective (levelInclusion ℓ A w ψ n) := by
  intro x y h
  apply Subtype.ext
  apply Subtype.ext
  have hxy := congrArg (fun z : Additive (fixedPrimary ℓ ψ w A) ↦
    (Additive.toMul z).1) h
  exact congrArg Additive.ofMul hxy

variable [NumberField K] [IsAlgClosure K Ω]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O] {A : PkgI3.AbVar K}

/-- A uniform original fixed-torsion order bound derived from the actual finite original subgroup. -/
theorem uniform_fixedOrder_bound
    (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [IsSeparated N.hom] [Smooth N.hom]
    [CompactSpace (specialFibre N).left]
    (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
    (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
      IsMonHom gen.hom)
    (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
      Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
    (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : IsUnit (ℓ : O)) :
    ∃ (σ : Ω ≃ₐ[K] Ω), σ ∈ w.decompositionSubgroup K ∧
      ∀ (r : ℕ), 0 < r → ∃ c : ℕ, ∀ n : ℕ,
        Nat.card (ToricFinitePart.fixedIn ℓ (σ ^ r) (ToricFinitePart.inertiaFixed ℓ A w n)) ∣ ℓ ^ c := by
  obtain ⟨σ, hD, hfin⟩ := exists_frobenius_finite_original_fixedPrimary N gen hgen hN w hw ℓ hℓ
  refine ⟨σ, hD, ?_⟩
  intro r hr
  letI : Finite (fixedPrimary ℓ (σ ^ r) w A) := hfin r hr
  letI : Finite (Additive (fixedPrimary ℓ (σ ^ r) w A)) := inferInstance
  refine ⟨(Nat.card (Additive (fixedPrimary ℓ (σ ^ r) w A))).factorization ℓ, ?_⟩
  intro n
  exact ToricFinitePart.fixed_card_dvd_of_injective ℓ (σ ^ r)
    (ToricFinitePart.inertiaFixed ℓ A w)
    (levelInclusion ℓ A w (σ ^ r)) (levelInclusion_injective ℓ A w (σ ^ r)) n

end SemistableGeometry.OriginalFixedPrimaryFeed
