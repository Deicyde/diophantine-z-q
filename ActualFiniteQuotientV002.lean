import ActualDivisionCompatibilityV002
import ActualWildInertiaV001

/-!
# Continuous actual finite actions and their ramification images

The finite field action is faithful and the original action is its
composition with continuous field restriction. Image equalities retain
the actual finite Galois group and its literal inherited valuation.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualFiniteQuotient
open ActualFiniteLevel ActualDivisionField ActualDivisionCompatibility
open ActualInertiaRestriction ActualFiniteRamification
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]
variable [CharZero K] [IsAlgClosure K Ω]

lemma factoredAction_continuous (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    @Continuous _ _ inferInstance ⊥ (factoredAction (Ω := Ω) A m) := by
  letI : TopologicalSpace (MulAut (torsionSubgroup A Ω m)) := ⊥
  exact continuous_of_discreteTopology

lemma action_continuous (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    @Continuous _ _ inferInstance ⊥ (action (Ω := Ω) A m) := by
  letI : TopologicalSpace (MulAut (torsionSubgroup A Ω m)) := ⊥
  have h := (factoredAction_continuous (Ω := Ω) A m).comp (restriction_continuous A m)
  have he : (factoredAction (Ω := Ω) A m) ∘ restriction A m = action A m :=
    congrArg DFunLike.coe (factoredAction_comp (Ω := Ω) A m)
  rw [he] at h
  exact h

lemma transition_factored (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime] (n : ℕ)
    [Finite (torsionSubgroup A Ω (ℓ ^ n))] [Finite (torsionSubgroup A Ω (ℓ ^ (n + 1)))]
    (τ : divisionField (Ω := Ω) A (ℓ ^ (n + 1)) ≃ₐ[K] divisionField (Ω := Ω) A (ℓ ^ (n + 1)))
    (x : torsionSubgroup A Ω (ℓ ^ (n + 1))) :
    transition A ℓ n (factoredAction A (ℓ ^ (n + 1)) τ x) =
      factoredAction A (ℓ ^ n) (levelRestriction A ℓ n τ) (transition A ℓ n x) := by
  obtain ⟨σ, rfl⟩ := restriction_surjective A (ℓ ^ (n + 1)) τ
  rw [levelRestriction_absolute, factoredAction_restriction, factoredAction_restriction]
  exact transition_galois A ℓ n σ x

def wildActionImage (A : PkgI3.AbVar K) (m : ℕ) (w : ValuationSubring Ω) :
    Subgroup (MulAut (torsionSubgroup A Ω m)) :=
  (WildFiniteGroup.strictDisplacementGroup (K := K) w).map (action A m)

def inertiaActionImage (A : PkgI3.AbVar K) (m : ℕ) (w : ValuationSubring Ω) :
    Subgroup (MulAut (torsionSubgroup A Ω m)) :=
  (inertiaGroup (K := K) w).map (action A m)

lemma wildActionImage_actual (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)]
    (w : ValuationSubring Ω) :
    wildActionImage A m w = (wildImage w (finiteDivisionField A m)).map (factoredAction A m) := by
  change (WildFiniteGroup.strictDisplacementGroup (K := K) w).map (action A m) =
    ((WildFiniteGroup.strictDisplacementGroup (K := K) w).map (restriction A m)).map (factoredAction A m)
  rw [Subgroup.map_map, factoredAction_comp]

lemma inertiaActionImage_actual (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)]
    (w : ValuationSubring Ω) :
    inertiaActionImage A m w =
      ((inertiaGroup (K := K) w).map (restriction A m)).map (factoredAction A m) := by
  rw [Subgroup.map_map, factoredAction_comp]
  rfl

lemma wildActionImage_isPGroup (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)]
    (w : ValuationSubring Ω) (p : ℕ) [Fact p.Prime]
    [CharP (IsLocalRing.ResidueField (w.comap (divisionField (Ω := Ω) A m).val.toRingHom)) p] :
    IsPGroup p (wildActionImage A m w) := by
  rw [wildActionImage_actual]
  haveI : CharP (IsLocalRing.ResidueField (w.comap (finiteDivisionField (Ω := Ω) A m).val.toRingHom)) p := by
    change CharP (IsLocalRing.ResidueField (w.comap (divisionField (Ω := Ω) A m).val.toRingHom)) p
    infer_instance
  exact (wildImage_isPGroup w (finiteDivisionField A m) p).map (factoredAction A m)

lemma wildActionImage_le_inertia (A : PkgI3.AbVar K) (m : ℕ) (w : ValuationSubring Ω) :
    wildActionImage A m w ≤ inertiaActionImage A m w := Subgroup.map_mono (strictGroup_le_inertia w)

lemma every_point_fixed_by_restriction_kernel (A : PkgI3.AbVar K) (m : ℕ)
    [Finite (torsionSubgroup A Ω m)] (σ : Ω ≃ₐ[K] Ω)
    (hσ : restriction A m σ = 1) (x : A.Pt Ω) (hx : x ^ m = 1) : A.galAct σ x = x := by
  apply (mem_action_ker A m σ).mp
  · rw [← restriction_ker]
    exact hσ
  · exact hx

end ActualFiniteQuotient
