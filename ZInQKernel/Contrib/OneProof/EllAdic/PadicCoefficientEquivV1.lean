import ZInQKernel.Contrib.OneProof.EllAdic.PadicReductionLiftV1
import Mathlib.Topology.ContinuousMap.Basic

set_option autoImplicit false

namespace RC53.EllAdic

/-- Compatible locally constant sections of the finite residue rings on the
same topological space. Successive reduction is the actual `ZMod.cast`. -/
def CompatibleResidues (p : ℕ) (U : Type*) [TopologicalSpace U] :=
  {r : (n : ℕ) → U → ZMod (p ^ n) //
    (∀ n, IsLocallyConstant (r n)) ∧
      ∀ (n : ℕ) (x : U), (ZMod.cast (r (n + 1) x) : ZMod (p ^ n)) = r n x}

variable {p : ℕ} [Fact p.Prime] {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]

/-- The pointwise reduction map on actual continuous coefficient sections. -/
noncomputable def residuesOfContinuousMap (f : C(U, ℤ_[p])) : CompatibleResidues p U :=
  ⟨fun n x => PadicInt.toZModPow n (f x),
    (continuous_iff_locallyConstant_padicReductions f).1 f.continuous,
    fun n x => PadicInt.cast_toZModPow n (n + 1) (Nat.le_succ n) (f x)⟩

private theorem continuousResidueLift_exists (r : CompatibleResidues p U) :
    ∃ f : U → ℤ_[p], Continuous f ∧ ∀ (n : ℕ) (x : U), PadicInt.toZModPow n (f x) = r.1 n x :=
  (existsUnique_continuous_lift_padicReductions r.1 r.2.1 r.2.2).exists

noncomputable def continuousResidueLift (r : CompatibleResidues p U) : C(U, ℤ_[p]) :=
  ⟨Classical.choose (continuousResidueLift_exists r),
    (Classical.choose_spec (continuousResidueLift_exists r)).1⟩

theorem reduce_continuousResidueLift (r : CompatibleResidues p U) (n : ℕ) (x : U) :
    PadicInt.toZModPow n (continuousResidueLift r x) = r.1 n x :=
  (Classical.choose_spec (continuousResidueLift_exists r)).2 n x

/-- The coefficient comparison on every object, using its actual continuous-map type. -/
noncomputable def continuousMapEquivCompatibleResidues : C(U, ℤ_[p]) ≃ CompatibleResidues p U where
  toFun := residuesOfContinuousMap
  invFun := continuousResidueLift
  left_inv f := by
    apply ContinuousMap.ext
    intro x
    apply PadicInt.ext_of_toZModPow.mp
    intro n
    exact reduce_continuousResidueLift (residuesOfContinuousMap f) n x
  right_inv r := by
    apply Subtype.ext
    funext n x
    exact reduce_continuousResidueLift r n x

/-- The finite tower's restriction along an actual continuous map is componentwise. -/
def compatibleResiduesPullback (g : C(V, U)) (r : CompatibleResidues p U) :
    CompatibleResidues p V :=
  ⟨fun n x => r.1 n (g x), fun n => (r.2.1 n).comp_continuous g.continuous,
    fun n x => r.2.2 n (g x)⟩

/-- The coefficient comparison commutes with the same precomposition map in both models. -/
theorem continuousMapEquivCompatibleResidues_comp (f : C(U, ℤ_[p])) (g : C(V, U)) :
    continuousMapEquivCompatibleResidues (f.comp g) =
      compatibleResiduesPullback g (continuousMapEquivCompatibleResidues f) := by
  apply Subtype.ext
  funext n x
  rfl

end RC53.EllAdic
