import SpecialFrobeniusBindingFourth
import NeronCommutativityCoreSecond
import InertiaNeronGlueV002
import HenselDivision.ValuationPointTorsionV002

/-!
# Finiteness of actual original inertia- and Frobenius-fixed prime-power torsion

The subgroup is formed inside the original A.Pt(Ω). Every member has an
actual inertia-descent integral torsion lift, and its actual special point
is Frobenius-fixed by the native covariance proofs. Reduction is injective
on prime-power torsion even when the two orders differ. The already proved
finite fixed special-point set therefore makes this original subgroup
finite, uniformly over all torsion levels. The Néron model data and the
invertible prime are intrinsic inputs; no lifting or finite-bound premise
is supplied.
-/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj

namespace SemistableGeometry.OriginalFixedPrimary

open SemistableGeometry.IntegralGalois
open SemistableGeometry.ActualResidueFrobenius
open SemistableGeometry.SpecialPointBinding
open SemistableGeometry.SpecialFrobeniusBinding
open SemistableGeometry.FrobeniusFixed

variable {K : Type} [Field K] [NumberField K]
variable {O : ValuationSubring K} [IsDiscreteValuationRing O]
variable {Ω : Type} [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]

/-- The actual original prime-power torsion subgroup fixed by inertia and the indicated automorphism. -/
def fixedPrimary (ℓ : ℕ) (σ : Ω ≃ₐ[K] Ω) (w : ValuationSubring Ω) (A : PkgI3.AbVar K) :
    Subgroup (A.Pt Ω) where
  carrier := {x | (∃ n : ℕ, x ^ (ℓ ^ n) = 1) ∧
    (∀ τ : Ω ≃ₐ[K] Ω, PkgI2.IsInertia w τ → A.galAct τ x = x) ∧ A.galAct σ x = x}
  one_mem' := ⟨⟨0, one_pow _⟩, fun τ _ ↦ map_one (A.galAct τ), map_one (A.galAct σ)⟩
  mul_mem' {x y} hx hy := by
    obtain ⟨a, ha⟩ := hx.1
    obtain ⟨b, hb⟩ := hy.1
    have hx' : x ^ (ℓ ^ (a + b)) = 1 := by rw [pow_add, pow_mul, ha, one_pow]
    have hy' : y ^ (ℓ ^ (a + b)) = 1 := by rw [pow_add, mul_comm, pow_mul, hb, one_pow]
    refine ⟨⟨a + b, ?_⟩, ?_, ?_⟩
    · rw [mul_pow, hx', hy', _root_.one_mul]
    · intro τ hτ
      rw [map_mul, hx.2.1 τ hτ, hy.2.1 τ hτ]
    · rw [map_mul, hx.2.2, hy.2.2]
  inv_mem' {x} hx := by
    obtain ⟨a, ha⟩ := hx.1
    refine ⟨⟨a, ?_⟩, ?_, ?_⟩
    · rw [inv_pow, ha, inv_one]
    · intro τ hτ
      rw [map_inv, hx.2.1 τ hτ]
    · rw [map_inv, hx.2.2]

/-- An annihilating level is chosen from the member's actual prime-power torsion property. -/
def exponent {ℓ : ℕ} {σ : Ω ≃ₐ[K] Ω} {w : ValuationSubring Ω} {A : PkgI3.AbVar K}
    (x : fixedPrimary ℓ σ w A) : ℕ := Classical.choose x.2.1

/-- This level annihilates the actual original point. -/
theorem exponent_annihilates {ℓ : ℕ} {σ : Ω ≃ₐ[K] Ω} {w : ValuationSubring Ω}
    {A : PkgI3.AbVar K} (x : fixedPrimary ℓ σ w A) : x.1 ^ (ℓ ^ exponent x) = 1 :=
  Classical.choose_spec x.2.1

variable {A : PkgI3.AbVar K} (N : Over (Spec (CommRingCat.of O))) [GrpObj N] [IsSeparated N.hom]
variable (gen : (Over.pullback (base (O := O))).obj N ≅ A.X)
variable (hgen : letI : GrpObj ((Over.pullback (base (O := O))).obj N) := Functor.grpObjObj
  IsMonHom gen.hom)
variable (hN : ∀ (Y : Over (Spec (CommRingCat.of O))) [Smooth Y.hom],
  Function.Bijective (fun f : Y ⟶ N => (Over.pullback (base (O := O))).map f ≫ gen.hom))
variable (w : ValuationSubring Ω) (hw : w.comap (algebraMap K Ω) = O)

/-- The integral lift comes from genuine inertia point descent and the actual Néron mapping property. -/
def integralPrimaryLift {ℓ : ℕ} {σ : Ω ≃ₐ[K] Ω} (x : fixedPrimary ℓ σ w A) :
    valuationDomain w hw ⟶ N :=
  Classical.choose (ExistsUnique.exists (InertiaNeronGlue.inertia_fixed_torsion_section
    O w hw gen hgen hN x.1 x.2.2.1 (ℓ ^ exponent x) (exponent_annihilates x)))

/-- Its native torsion order and its literal original generic point are proved, not assumed. -/
theorem integralPrimaryLift_spec {ℓ : ℕ} {σ : Ω ≃ₐ[K] Ω} (x : fixedPrimary ℓ σ w A) :
    integralPrimaryLift N gen hgen hN w hw x ^ (ℓ ^ exponent x) = 1 ∧
      originalPoint N gen w hw (integralPrimaryLift N gen hgen hN w hw x) = x.1 :=
  Classical.choose_spec (ExistsUnique.exists (InertiaNeronGlue.inertia_fixed_torsion_section
    O w hw gen hgen hN x.1 x.2.2.1 (ℓ ^ exponent x) (exponent_annihilates x)))

/-- The actual special point lies in the actual Frobenius-power-fixed geometric point set. -/
def fixedSpecialPoint (ℓ : ℕ) (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
    (r : ℕ) (x : fixedPrimary ℓ (σ ^ r) w A) :
    letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
    fixedPoints (residueFrobeniusAlg hw σ hD hcong) r (specialFibre N) := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  refine ⟨specialPoint hw N (reductionArrow w hw ≫ integralPrimaryLift N gen hgen hN w hw x), ?_⟩
  apply specialPoint_fixed_of_original_fixed hw N gen σ hD hcong r
  rw [(integralPrimaryLift_spec N gen hgen hN w hw x).2]
  exact x.2.2.2

/-- Actual reduction is injective on this original prime-power subgroup, independent of each chosen level. -/
theorem fixedSpecialPoint_injective [Smooth N.hom] (ℓ : ℕ) (hℓ : IsUnit (ℓ : O))
    (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1) (r : ℕ) :
    letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
    Function.Injective (fixedSpecialPoint N gen hgen hN w hw ℓ σ hD hcong r) := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  letI : IsCommMonObj N := SemistableGeometry.NeronCommutativityCore.model_commutative N gen hgen hN
  intro x y h
  have hr : reductionArrow w hw ≫ integralPrimaryLift N gen hgen hN w hw x =
      reductionArrow w hw ≫ integralPrimaryLift N gen hgen hN w hw y := by
    apply specialPoint_injective hw N
    exact congrArg (fun z : fixedPoints (residueFrobeniusAlg hw σ hD hcong) r (specialFibre N) ↦ z.1) h
  have hxunit : IsUnit ((ℓ ^ exponent x : ℕ) : O) := by rw [Nat.cast_pow]; exact hℓ.pow _
  have hyunit : IsUnit ((ℓ ^ exponent y : ℕ) : O) := by rw [Nat.cast_pow]; exact hℓ.pow _
  letI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hs := HenselDivision.valuation_point_torsion_eq_of_reduction w hw N
    (ℓ ^ exponent x) (ℓ ^ exponent y) hxunit hyunit (reductionArrow w hw) rfl
    (integralPrimaryLift N gen hgen hN w hw x) (integralPrimaryLift N gen hgen hN w hw y)
    (integralPrimaryLift_spec N gen hgen hN w hw x).1
    (integralPrimaryLift_spec N gen hgen hN w hw y).1 hr
  apply Subtype.ext
  rw [← (integralPrimaryLift_spec N gen hgen hN w hw x).2,
    ← (integralPrimaryLift_spec N gen hgen hN w hw y).2, hs]

include gen hgen hN hw

/-- The original fixed prime-power torsion group is genuinely finite; no uniform-bound hypothesis is used. -/
theorem finite_fixedPrimary [Smooth N.hom] [CompactSpace (specialFibre N).left]
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : O)) (σ : Ω ≃ₐ[K] Ω) (hD : σ ∈ w.decompositionSubgroup K)
    (hcong : ∀ x ∈ w, w.valuation (σ x - x ^ Nat.card (IsLocalRing.ResidueField O)) < 1)
    (r : ℕ) (hr : 0 < r) : Finite (fixedPrimary ℓ (σ ^ r) w A) := by
  letI : Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField w) := residueAlgebra hw
  letI : LocallyOfFiniteType (specialFibre N).hom := by
    change LocallyOfFiniteType (CategoryTheory.Limits.pullback.snd N.hom (specialBase (O := O)))
    infer_instance
  letI : Finite (fixedPoints (residueFrobeniusAlg hw σ hD hcong) r (specialFibre N)) :=
    finite_fixedPoints (residueFrobeniusAlg hw σ hD hcong) (Nat.card (IsLocalRing.ResidueField O))
      (FrobLift.two_le_card_residueField O) (FrobLift.residue_toRingAut_apply hD hcong) r hr (specialFibre N)
  exact Finite.of_injective _ (fixedSpecialPoint_injective N gen hgen hN w hw ℓ hℓ σ hD hcong r)

/-- The actual arithmetic Frobenius supplies the finite original fixed subgroup for every positive power. -/
theorem exists_frobenius_finite_original_fixedPrimary [Smooth N.hom] [CompactSpace (specialFibre N).left]
    (ℓ : ℕ) (hℓ : IsUnit (ℓ : O)) :
    ∃ (σ : Ω ≃ₐ[K] Ω), σ ∈ w.decompositionSubgroup K ∧
      ∀ (r : ℕ), 0 < r → Finite (fixedPrimary ℓ (σ ^ r) w A) := by
  obtain ⟨σ, hD, hcong⟩ := FrobLift.exists_frobenius_lift hw
  exact ⟨σ, hD, fun r hr ↦ finite_fixedPrimary N gen hgen hN w hw ℓ hℓ σ hD hcong r hr⟩

end SemistableGeometry.OriginalFixedPrimary
