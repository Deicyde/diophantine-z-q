import ActualClosedDivisionKernelV001
import ActualFiniteLinearActionV001

/-!
# Faithfulness and minimality of the original division-field action

The original closed kernel, not a supplied representation model,
determines the field. The action of its actual Galois group is faithful,
and scalar fixing is exactly fixing every original torsion point.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualClosedDivisionKernel
open ActualFiniteLevel ActualDivisionField
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [CharZero K] [IsAlgClosure K Ω]

lemma canonicalAction_injective (A : PkgI3.AbVar K) (m : ℕ) :
    Function.Injective (canonicalAction (Ω := Ω) A m) := by
  intro σ τ h
  obtain ⟨s, rfl⟩ := restriction_surjective A m σ
  obtain ⟨t, rfl⟩ := restriction_surjective A m τ
  rw [canonicalAction_restriction, canonicalAction_restriction] at h
  have hk : s⁻¹ * t ∈ (action A m).ker := by
    change action A m (s⁻¹ * t) = 1
    rw [map_mul, map_inv, h, inv_mul_cancel]
  have hr : s⁻¹ * t ∈ (restriction A m).ker := by
    rw [restriction_kernel_exact]
    exact hk
  change restriction A m (s⁻¹ * t) = 1 at hr
  rw [map_mul, map_inv, inv_mul_eq_one] at hr
  exact hr

lemma scalarFixing_iff_torsionFixing (A : PkgI3.AbVar K) (m : ℕ) (σ : Ω ≃ₐ[K] Ω) :
    (∀ a ∈ divisionField (Ω := Ω) A m, σ a = a) ↔
      ∀ x : A.Pt Ω, x ^ m = 1 → A.galAct σ x = x := by
  rw [← IntermediateField.mem_fixingSubgroup_iff (divisionField (Ω := Ω) A m) σ,
    fixingSubgroup_eq_original_kernel, mem_action_ker]

lemma divisionField_minimal (A : PkgI3.AbVar K) (m : ℕ) (F : IntermediateField K Ω) :
    divisionField A m ≤ F ↔ F.fixingSubgroup ≤ (action A m).ker := by
  constructor
  · intro h
    rw [← fixingSubgroup_eq_original_kernel A m]
    exact (divisionField A m).fixingSubgroup_le h
  · intro h
    have h' := IntermediateField.fixedField_le h
    rw [InfiniteGalois.fixedField_fixingSubgroup F] at h'
    exact h'

def canonicalLinearAction (A : PkgI3.AbVar K) (m : ℕ) :
    Representation (ZMod m)
      (divisionField (Ω := Ω) A m ≃ₐ[K] divisionField (Ω := Ω) A m)
      (Additive (torsionSubgroup A Ω m)) where
  toFun σ := ((canonicalAction A m σ).toMonoidHom.toAdditive).toZModLinearMap m
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (canonicalAction A m 1 (Additive.toMul x)) = x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (canonicalAction A m (σ * τ) (Additive.toMul x)) =
      Additive.ofMul (canonicalAction A m σ (canonicalAction A m τ (Additive.toMul x)))
    rw [map_mul]
    rfl

lemma canonicalLinearAction_restriction (A : PkgI3.AbVar K) (m : ℕ) (σ : Ω ≃ₐ[K] Ω) :
    canonicalLinearAction A m (restriction A m σ) = ActualFiniteLinearAction.linearAction A m σ := by
  apply LinearMap.ext
  intro x
  change Additive.ofMul (canonicalAction A m (restriction A m σ) (Additive.toMul x)) =
    Additive.ofMul (action A m σ (Additive.toMul x))
  rw [canonicalAction_restriction]

end ActualClosedDivisionKernel
