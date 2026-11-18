import ActualFiniteQuotientV002
import Mathlib.Algebra.Module.ZMod

/-!
# The original torsion representation is linear

The canonical residue-ring module structure is induced by integer
multiplication on the actual torsion subgroup. No basis or representation
model is assumed. Field factoring retains this original linear action.
-/

noncomputable section
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry MonObj

namespace ActualFiniteLinearAction
open ActualFiniteLevel ActualDivisionField
variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω]

instance torsionZModModule (A : PkgI3.AbVar K) (m : ℕ) :
    Module (ZMod m) (Additive (torsionSubgroup A Ω m)) :=
  AddCommGroup.zmodModule (fun x => by
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (Additive.toMul x).2)

def linearAction (A : PkgI3.AbVar K) (m : ℕ) :
    Representation (ZMod m) (Ω ≃ₐ[K] Ω) (Additive (torsionSubgroup A Ω m)) where
  toFun σ := ((action A m σ).toMonoidHom.toAdditive).toZModLinearMap m
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (action A m 1 (Additive.toMul x)) = x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (action A m (σ * τ) (Additive.toMul x)) =
      Additive.ofMul (action A m σ (action A m τ (Additive.toMul x)))
    rw [map_mul]
    rfl

@[simp] lemma linearAction_apply (A : PkgI3.AbVar K) (m : ℕ) (σ : Ω ≃ₐ[K] Ω)
    (x : Additive (torsionSubgroup A Ω m)) :
    linearAction A m σ x = Additive.ofMul (action A m σ (Additive.toMul x)) := rfl

def factoredLinearAction [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] :
    Representation (ZMod m)
      (divisionField (Ω := Ω) A m ≃ₐ[K] divisionField (Ω := Ω) A m)
      (Additive (torsionSubgroup A Ω m)) where
  toFun σ := ((factoredAction A m σ).toMonoidHom.toAdditive).toZModLinearMap m
  map_one' := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (factoredAction A m 1 (Additive.toMul x)) = x
    rw [map_one]
    rfl
  map_mul' σ τ := by
    apply LinearMap.ext
    intro x
    change Additive.ofMul (factoredAction A m (σ * τ) (Additive.toMul x)) =
      Additive.ofMul (factoredAction A m σ (factoredAction A m τ (Additive.toMul x)))
    rw [map_mul]
    rfl

lemma factoredLinearAction_restriction [CharZero K] [IsAlgClosure K Ω]
    (A : PkgI3.AbVar K) (m : ℕ) [Finite (torsionSubgroup A Ω m)] (σ : Ω ≃ₐ[K] Ω) :
    factoredLinearAction A m (restriction A m σ) = linearAction A m σ := by
  apply LinearMap.ext
  intro x
  change Additive.ofMul (factoredAction A m (restriction A m σ) (Additive.toMul x)) =
    Additive.ofMul (action A m σ (Additive.toMul x))
  rw [factoredAction_restriction]

lemma linearAction_kernel (A : PkgI3.AbVar K) (m : ℕ) (σ : Ω ≃ₐ[K] Ω) :
    linearAction A m σ = 1 ↔ σ ∈ (action (Ω := Ω) A m).ker := by
  constructor
  · intro h
    apply (mem_action_ker A m σ).mpr
    intro x hx
    have h' := congrArg (fun f => f (Additive.ofMul (⟨x, hx⟩ : torsionSubgroup A Ω m))) h
    exact congrArg (fun y : Additive (torsionSubgroup A Ω m) => (Additive.toMul y).1) h'
  · intro h
    change action A m σ = 1 at h
    apply LinearMap.ext
    intro x
    change Additive.ofMul (action A m σ (Additive.toMul x)) = x
    rw [h]
    rfl

end ActualFiniteLinearAction
