import ActualTorsionFinitenessV003
import ActualCanonicalTateFactoringV001
import ActualFiniteQuotientV002
import ActualGaloisQuotientV002
import ActualUniformLevelPeriodV001
import ActualClosedFiniteImagesV001
import ActualCommonPointFieldV003

/-!
# Actual finite Galois division fields and original finite-level Tate factoring

All prime-power torsion points are finite by the proved native étale
multiplication theorem, transported by the original point bijection.
The actual division field lies inside the original algebraic closure.
Its genuine finite Galois group acts faithfully on the original torsion,
with compatible levels, original Tate evaluation, and actual inertia
and strict wild images. No finite-point or factoring model is an input.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualPrimePowerDivision
open ActualFiniteLevel ActualDivisionField ActualDivisionCompatibility ActualFiniteQuotient
open ActualClosedDivisionKernel
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [IsAlgClosure K Ω]

instance levelFinite (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Finite (torsionSubgroup A Ω (ℓ ^ n)) :=
  ActualTorsionFiniteness.finite_prime_power_torsion A ℓ n

def divisionFieldLevel (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    FiniteGaloisIntermediateField K Ω := finiteDivisionField A (ℓ ^ n)

def rho (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (divisionFieldLevel (Ω := Ω) A ℓ n ≃ₐ[K] divisionFieldLevel (Ω := Ω) A ℓ n) →*
      MulAut (torsionSubgroup A Ω (ℓ ^ n)) := canonicalAction A (ℓ ^ n)

def rhoLinear (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Representation (ZMod (ℓ ^ n))
      (divisionFieldLevel (Ω := Ω) A ℓ n ≃ₐ[K] divisionFieldLevel (Ω := Ω) A ℓ n)
      (Additive (torsionSubgroup A Ω (ℓ ^ n))) := canonicalLinearAction A (ℓ ^ n)

lemma rho_factors_original (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (σ : Ω ≃ₐ[K] Ω) : rho A ℓ n (restriction A (ℓ ^ n) σ) = action A (ℓ ^ n) σ :=
  canonicalAction_restriction A (ℓ ^ n) σ

lemma rho_faithful (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    Function.Injective (rho (Ω := Ω) A ℓ n) := canonicalAction_injective A (ℓ ^ n)

lemma rhoLinear_factors_original (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (σ : Ω ≃ₐ[K] Ω) :
    rhoLinear A ℓ n (restriction A (ℓ ^ n) σ) = ActualFiniteLinearAction.linearAction A (ℓ ^ n) σ :=
  canonicalLinearAction_restriction A (ℓ ^ n) σ

lemma original_kernel_exact (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    (restriction (Ω := Ω) A (ℓ ^ n)).ker = (action (Ω := Ω) A (ℓ ^ n)).ker :=
  restriction_kernel_exact A (ℓ ^ n)

lemma rho_continuous (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    @Continuous _ _ inferInstance ⊥ (rho (Ω := Ω) A ℓ n) := by
  letI : TopologicalSpace (MulAut (torsionSubgroup A Ω (ℓ ^ n))) := ⊥
  exact continuous_of_discreteTopology

lemma original_action_continuous (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    @Continuous _ _ inferInstance ⊥ (action (Ω := Ω) A (ℓ ^ n)) := action_continuous A (ℓ ^ n)

lemma fixes_every_point (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ a ∈ divisionField (Ω := Ω) A (ℓ ^ n), σ a = a)
    (x : A.Pt Ω) (hx : x ^ (ℓ ^ n) = 1) : A.galAct σ x = x :=
  (scalarFixing_iff_torsionFixing A (ℓ ^ n) σ).mp hσ x hx

lemma tate_original_factoring (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (σ : Ω ≃ₐ[K] Ω) (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω))) :
    tateEvaluation A ℓ n (PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct σ)) t) =
      Additive.ofMul (rho A ℓ n (restriction A (ℓ ^ n) σ)
        (Additive.toMul (tateEvaluation A ℓ n t))) := canonical_tateEvaluation A ℓ n σ t

lemma adjacent_level_factoring (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (τ : divisionFieldLevel (Ω := Ω) A ℓ (n + 1) ≃ₐ[K] divisionFieldLevel (Ω := Ω) A ℓ (n + 1))
    (x : torsionSubgroup A Ω (ℓ ^ (n + 1))) :
    transition A ℓ n (rho A ℓ (n + 1) τ x) =
      rho A ℓ n (levelRestriction A ℓ n τ) (transition A ℓ n x) := canonical_transition A ℓ n τ x

lemma actual_inertia_restricts (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω) (hσ : PkgI2.IsInertia w σ) :
    PkgI2.IsInertia (w.comap (divisionField (Ω := Ω) A (ℓ ^ n)).val.toRingHom)
      (restriction A (ℓ ^ n) σ) :=
  ActualInertiaRestriction.restrict_inertia w (divisionFieldLevel A ℓ n) σ hσ

lemma actual_wild_restricts (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    (w : ValuationSubring Ω) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ a : Ω, a ≠ 0 → w.valuation (σ a - a) < w.valuation a) :
    restriction A (ℓ ^ n) σ ∈ WildFiniteGroup.strictDisplacementGroup (K := K)
      (w.comap (divisionField (Ω := Ω) A (ℓ ^ n)).val.toRingHom) :=
  ActualFiniteRamification.restriction_strict w (divisionFieldLevel A ℓ n) σ hσ

lemma actual_wild_image_pGroup (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (n p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField O) p] :
    IsPGroup p (ActualFiniteRamification.wildImage w (divisionFieldLevel A ℓ n)) :=
  ActualClosedFiniteImages.wildImage_isPGroup_base O w hw (divisionFieldLevel A ℓ n) p

lemma original_wild_action_pGroup (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]
    (n p : ℕ) [Fact p.Prime] [CharP (IsLocalRing.ResidueField O) p] :
    IsPGroup p (wildActionImage A (ℓ ^ n) w) :=
  ActualClosedFiniteImages.actionImage_isPGroup_base O w hw A (ℓ ^ n) p

lemma uniform_original_period (O : ValuationSubring K) (w : ValuationSubring Ω)
    (hw : w.comap (algebraMap K Ω) = O) (A : PkgI3.AbVar K)
    (ℓ : ℕ) [Fact ℓ.Prime] (hu : IsUnit (ℓ : O)) (n : ℕ) (σ : Ω ≃ₐ[K] Ω)
    (hσ : ∀ a : Ω, a ≠ 0 → w.valuation (σ a - a) < w.valuation a) :
    ∃ r : ℕ, 0 < r ∧ Nat.Coprime r (ℓ ^ n) ∧
      ∀ x : A.Pt Ω, x ^ (ℓ ^ n) = 1 → (A.galAct σ)^[r] x = x :=
  ActualUniformLevelPeriod.exists_uniform_period O w hw A ℓ hu n σ hσ

lemma all_torsion_common_defining_field (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ) :
    ∃ E : FiniteGaloisIntermediateField K Ω,
      (∀ x : torsionSubgroup A Ω (ℓ ^ n), ∃ y : A.Pt E,
        Spec.map (CommRingCat.ofHom E.toIntermediateField.val.toRingHom) ≫ y.left = x.1.left) ∧
      E.fixingSubgroup ≤ (action (Ω := Ω) A (ℓ ^ n)).ker :=
  ActualCommonPointField.exists_common_defining_field A (ℓ ^ n)

lemma zero_level_field (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] :
    (divisionFieldLevel (Ω := Ω) A ℓ 0).toIntermediateField = ⊥ := divisionField_zero A ℓ

end ActualPrimePowerDivision
