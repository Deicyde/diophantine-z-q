import ZInQKernel.Contrib.OneProof.EllAdic.PadicCoefficientEquivV1
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Topology.ContinuousMap.Algebra

set_option autoImplicit false

namespace RC53.EllAdic

private def residueStep (p n : ℕ) : ZMod (p ^ (n + 1)) →+* ZMod (p ^ n) :=
  ZMod.castHom (pow_dvd_pow p (Nat.le_succ n)) (ZMod (p ^ n))

/-- The additively closed space of compatible locally constant residue sections.
The addition is inherited from the product of the actual residue groups. -/
def compatibleResiduesAddSubgroup (p : ℕ) (U : Type*) [TopologicalSpace U] :
    AddSubgroup ((n : ℕ) → U → ZMod (p ^ n)) where
  carrier := {r | (∀ n, IsLocallyConstant (r n)) ∧
    ∀ (n : ℕ) (x : U), (ZMod.cast (r (n + 1) x) : ZMod (p ^ n)) = r n x}
  zero_mem' := by
    refine ⟨fun _ => IsLocallyConstant.const _, ?_⟩
    intro n x
    change residueStep p n 0 = 0
    exact map_zero _
  add_mem' := by
    intro a b ha hb
    refine ⟨fun n => (ha.1 n).comp₂ (hb.1 n) (· + ·), ?_⟩
    intro n x
    change residueStep p n (a (n + 1) x + b (n + 1) x) = a n x + b n x
    rw [map_add]
    exact congrArg₂ (· + ·) (ha.2 n x) (hb.2 n x)
  neg_mem' := by
    intro a ha
    refine ⟨fun n => (ha.1 n).comp Neg.neg, ?_⟩
    intro n x
    change residueStep p n (-a (n + 1) x) = -a n x
    rw [map_neg]
    exact congrArg Neg.neg (ha.2 n x)

variable {p : ℕ} [Fact p.Prime] {U V : Type*} [TopologicalSpace U] [TopologicalSpace V]

/-- The objectwise coefficient comparison is additive with respect to the
pointwise operations, not merely a bijection of the underlying types. -/
noncomputable def continuousMapAddEquivCompatibleResidues :
    C(U, ℤ_[p]) ≃+ ↥(compatibleResiduesAddSubgroup p U) where
  toEquiv := continuousMapEquivCompatibleResidues
  map_add' f g := by
    apply Subtype.ext
    funext n x
    change PadicInt.toZModPow n (f x + g x) =
      PadicInt.toZModPow n (f x) + PadicInt.toZModPow n (g x)
    exact map_add _ _ _

/-- In the finite-residue model, pullback is the actual componentwise additive map. -/
def compatibleResiduesPullbackHom (g : C(V, U)) :
    ↥(compatibleResiduesAddSubgroup p U) →+ ↥(compatibleResiduesAddSubgroup p V) where
  toFun r := compatibleResiduesPullback g r
  map_zero' := by
    apply Subtype.ext
    funext n x
    rfl
  map_add' _ _ := by
    apply Subtype.ext
    funext n x
    rfl

/-- Naturality for the literal precomposition of continuous sections. -/
theorem continuousMapAddEquivCompatibleResidues_comp (f : C(U, ℤ_[p])) (g : C(V, U)) :
    continuousMapAddEquivCompatibleResidues (f.comp g) =
      compatibleResiduesPullbackHom g (continuousMapAddEquivCompatibleResidues f) :=
  continuousMapEquivCompatibleResidues_comp f g

end RC53.EllAdic
