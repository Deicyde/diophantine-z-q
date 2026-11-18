import ActualDivisionFieldV004

/-!
# Compatibility and minimality of actual division fields

The original torsion inclusions imply increasing division fields. Finite
field restriction commutes with the original absolute restriction, and
Tate evaluation factors through the corresponding actual finite action.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualDivisionCompatibility
open ActualFiniteLevel ActualDivisionField
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

lemma kernel_antitone_of_dvd (A : PkgI3.AbVar K) {m r : ℕ} (h : m ∣ r) :
    (action (Ω := Ω) A r).ker ≤ (action (Ω := Ω) A m).ker := by
  intro σ hσ
  apply (mem_action_ker A m σ).mpr
  intro x hx
  apply (mem_action_ker A r σ).mp hσ x
  obtain ⟨q, rfl⟩ := h
  rw [pow_mul, hx, one_pow]

lemma divisionField_mono (A : PkgI3.AbVar K) {m r : ℕ} (h : m ∣ r) :
    divisionField (Ω := Ω) A m ≤ divisionField (Ω := Ω) A r :=
  IntermediateField.fixedField_le (kernel_antitone_of_dvd A h)

lemma divisionField_le_iff [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] (F : IntermediateField K Ω) :
    divisionField A m ≤ F ↔ F.fixingSubgroup ≤ (action A m).ker := by
  constructor
  · intro h
    rw [← fixingSubgroup_eq_kernel A m]
    exact (divisionField A m).fixingSubgroup_le h
  · intro h
    have h' := IntermediateField.fixedField_le h
    rw [InfiniteGalois.fixedField_fixingSubgroup F] at h'
    exact h'

lemma divisionField_zero [IsGalois K Ω] (A : PkgI3.AbVar K) (ℓ : ℕ) :
    divisionField (Ω := Ω) A (ℓ ^ 0) = ⊥ := by
  have hk : (action (Ω := Ω) A 1).ker = ⊤ := by
    apply top_unique
    intro σ _
    apply (mem_action_ker A 1 σ).mpr
    intro x hx
    have hx' : x = 1 := by simpa using hx
    rw [hx', map_one]
  change IntermediateField.fixedField (action (Ω := Ω) A 1).ker = ⊥
  rw [hk, InfiniteGalois.fixedField_bot]

variable [CharZero K] [IsAlgClosure K Ω] (A : PkgI3.AbVar K) (ℓ : ℕ) [Fact ℓ.Prime]

def levelRestriction (n : ℕ) :
    (divisionField (Ω := Ω) A (ℓ ^ (n + 1)) ≃ₐ[K] divisionField (Ω := Ω) A (ℓ ^ (n + 1))) →*
      (divisionField (Ω := Ω) A (ℓ ^ n) ≃ₐ[K] divisionField (Ω := Ω) A (ℓ ^ n)) := by
  let h : divisionField (Ω := Ω) A (ℓ ^ n) ≤ divisionField (Ω := Ω) A (ℓ ^ (n + 1)) :=
    divisionField_mono A ⟨ℓ, pow_succ ℓ n⟩
  letI : Algebra (divisionField (Ω := Ω) A (ℓ ^ n)) (divisionField (Ω := Ω) A (ℓ ^ (n + 1))) :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower K (divisionField (Ω := Ω) A (ℓ ^ n)) (divisionField (Ω := Ω) A (ℓ ^ (n + 1))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  exact AlgEquiv.restrictNormalHom (divisionField (Ω := Ω) A (ℓ ^ n))

lemma levelRestriction_absolute (n : ℕ) (σ : Ω ≃ₐ[K] Ω) :
    levelRestriction A ℓ n (restriction A (ℓ ^ (n + 1)) σ) = restriction A (ℓ ^ n) σ := by
  apply AlgEquiv.ext
  intro x
  apply Subtype.ext
  let h : divisionField (Ω := Ω) A (ℓ ^ n) ≤ divisionField (Ω := Ω) A (ℓ ^ (n + 1)) :=
    divisionField_mono A ⟨ℓ, pow_succ ℓ n⟩
  letI : Algebra (divisionField (Ω := Ω) A (ℓ ^ n)) (divisionField (Ω := Ω) A (ℓ ^ (n + 1))) :=
    (IntermediateField.inclusion h).toAlgebra
  letI : IsScalarTower K (divisionField (Ω := Ω) A (ℓ ^ n)) (divisionField (Ω := Ω) A (ℓ ^ (n + 1))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have he := AlgEquiv.restrictNormal_commutes (restriction A (ℓ ^ (n + 1)) σ)
    (divisionField (Ω := Ω) A (ℓ ^ n)) x
  have he' := congrArg (fun z : divisionField (Ω := Ω) A (ℓ ^ (n + 1)) => (z : Ω)) he
  exact he'.trans (AlgEquiv.restrictNormal_commutes σ (divisionField A (ℓ ^ (n + 1)))
    ((IntermediateField.inclusion h) x)) |>.trans
      (AlgEquiv.restrictNormal_commutes σ (divisionField A (ℓ ^ n)) x).symm

lemma tateEvaluation_factored (n : ℕ) [Finite (torsionSubgroup A Ω (ℓ ^ n))]
    (σ : Ω ≃ₐ[K] Ω) (t : PkgI3.Tate.T ℓ (Additive (A.Pt Ω))) :
    tateEvaluation A ℓ n (PkgI3.Tate.map (MonoidHom.toAdditive (A.galAct σ)) t) =
      Additive.ofMul (factoredAction A (ℓ ^ n) (restriction A (ℓ ^ n) σ)
        (Additive.toMul (tateEvaluation A ℓ n t))) := by
  rw [factoredAction_restriction]
  exact tateEvaluation_galois A ℓ n σ t

end ActualDivisionCompatibility
