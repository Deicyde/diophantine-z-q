module

public import Mathlib.Topology.Algebra.Module.Equiv.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Continuous character coefficient lines

The underlying additive group, scalar module, and topology are those of the coefficient ring.
The character changes only the group action. In particular, no discrete topology is imposed.
The singleton basis exhibits the line as a finite free module. Reduction along a ring homomorphism
is semilinear and is equivariant when the two characters are compatible.
-/

@[expose] public section

namespace ZInQ.Contrib.RC53Assist.IntegralDuality

universe u v w

/-- The coefficient ring as a module with a separately specified character action. -/
@[nolint unusedArguments]
def ContinuousCharacterLine (A : Type u) [CommRing A] {G : Type v} [Monoid G]
    (_χ : G →* Aˣ) : Type u := A

namespace ContinuousCharacterLine

variable (A : Type u) [CommRing A] {G : Type v} [Monoid G] (χ : G →* Aˣ)

instance instAddCommGroup : AddCommGroup (ContinuousCharacterLine A χ) :=
  inferInstanceAs (AddCommGroup A)

instance instModule : Module A (ContinuousCharacterLine A χ) :=
  inferInstanceAs (Module A A)

/-- The underlying linear equivalence with the coefficient ring. -/
def equiv : ContinuousCharacterLine A χ ≃ₗ[A] A := LinearEquiv.refl A A

@[simp] theorem equiv_symm_apply (a : A) : equiv A χ ((equiv A χ).symm a) = a := rfl

instance instDistribMulAction : DistribMulAction G (ContinuousCharacterLine A χ) where
  smul g a := show A from (χ g : A) * (show A from a)
  one_smul a := by
    change (χ 1 : A) * (show A from a) = a
    rw [map_one, Units.val_one, one_mul]
  mul_smul g h a := by
    change (χ (g * h) : A) * (show A from a) =
      (χ g : A) * ((χ h : A) * (show A from a))
    rw [map_mul, Units.val_mul, mul_assoc]
  smul_zero g := mul_zero (χ g : A)
  smul_add g a b := mul_add (χ g : A) (show A from a) (show A from b)

/-- In ring coordinates the character action is multiplication by the character value. -/
@[simp] theorem smul_def (g : G) (a : ContinuousCharacterLine A χ) :
    equiv A χ (g • a) = (χ g : A) * equiv A χ a := rfl

instance instSMulCommClass : SMulCommClass G A (ContinuousCharacterLine A χ) where
  smul_comm g a b := by
    change (χ g : A) * (a * (show A from b)) = a * ((χ g : A) * (show A from b))
    exact mul_left_comm _ _ _

instance instTopologicalSpace [TopologicalSpace A] :
    TopologicalSpace (ContinuousCharacterLine A χ) := inferInstanceAs (TopologicalSpace A)

/-- The topology is exactly the given topology on the coefficient ring. -/
theorem topology_eq [t : TopologicalSpace A] :
    (inferInstance : TopologicalSpace (ContinuousCharacterLine A χ)) = t := rfl

instance instContinuousAdd [TopologicalSpace A] [ContinuousAdd A] :
    ContinuousAdd (ContinuousCharacterLine A χ) := inferInstanceAs (ContinuousAdd A)

instance instContinuousConstSMul [TopologicalSpace A] [ContinuousConstSMul A A] :
    ContinuousConstSMul A (ContinuousCharacterLine A χ) :=
  inferInstanceAs (ContinuousConstSMul A A)

instance instContinuousSMulRing [TopologicalSpace A] [ContinuousSMul A A] :
    ContinuousSMul A (ContinuousCharacterLine A χ) := inferInstanceAs (ContinuousSMul A A)

instance instIsTopologicalAddGroup [TopologicalSpace A] [IsTopologicalAddGroup A] :
    IsTopologicalAddGroup (ContinuousCharacterLine A χ) :=
  inferInstanceAs (IsTopologicalAddGroup A)

/-- The identity in ring coordinates is also a homeomorphism. -/
def homeomorph [TopologicalSpace A] : ContinuousCharacterLine A χ ≃ₜ A :=
  Homeomorph.refl A

/-- Both the algebraic and topological identifications in one equivalence. -/
def continuousLinearEquiv [TopologicalSpace A] : ContinuousCharacterLine A χ ≃L[A] A where
  toLinearEquiv := equiv A χ
  continuous_toFun := continuous_id
  continuous_invFun := continuous_id

/-- The single generator is the element with coefficient one. -/
noncomputable def basis : Module.Basis Unit A (ContinuousCharacterLine A χ) :=
  (Module.Basis.singleton Unit A).map (equiv A χ).symm

@[simp] theorem basis_apply (i : Unit) :
    equiv A χ (basis A χ i) = 1 := by
  simp [basis]

instance instFree : Module.Free A (ContinuousCharacterLine A χ) :=
  Module.Free.of_basis (basis A χ)

instance instModuleFinite : Module.Finite A (ContinuousCharacterLine A χ) :=
  Module.Finite.of_basis (basis A χ)

/-- The module has rank one over its coefficient ring. -/
theorem rank_eq_one : Module.rank A (ContinuousCharacterLine A χ) = 1 :=
  (equiv A χ).rank_eq.trans (CommSemiring.rank_self A)

/-- The finite rank is one. -/
theorem finrank_eq_one : Module.finrank A (ContinuousCharacterLine A χ) = 1 :=
  (equiv A χ).finrank_eq.trans (CommSemiring.finrank_self A)

instance instFinite [Finite A] : Finite (ContinuousCharacterLine A χ) :=
  inferInstanceAs (Finite A)

/-- Continuity of the character in coefficient-ring coordinates. -/
class IsContinuous [TopologicalSpace A] [TopologicalSpace G] : Prop where
  continuous_coe : Continuous (fun g : G => (χ g : A))

/-- A continuous coefficient-valued character gives a continuous action on the line. -/
theorem continuousSMul [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G]
    (hχ : Continuous (fun g : G => (χ g : A))) :
    ContinuousSMul G (ContinuousCharacterLine A χ) where
  continuous_smul := by
    change Continuous (fun p : G × A => (χ p.1 : A) * p.2)
    exact (hχ.comp continuous_fst).mul continuous_snd

instance instContinuousSMul [TopologicalSpace A] [IsTopologicalRing A] [TopologicalSpace G]
    [IsContinuous A χ] : ContinuousSMul G (ContinuousCharacterLine A χ) :=
  continuousSMul A χ (IsContinuous.continuous_coe (A := A) (χ := χ))

section Reduction

variable {B : Type w} [CommRing B] (ψ : G →* Bˣ) (π : A →+* B)

/-- Coefficient reduction, without imposing any extra topology on either line. -/
def reduction : ContinuousCharacterLine A χ →ₛₗ[π] ContinuousCharacterLine B ψ where
  toFun a := π (equiv A χ a)
  map_add' a b := map_add π (equiv A χ a) (equiv A χ b)
  map_smul' a b := map_mul π a (equiv A χ b)

@[simp] theorem reduction_apply (a : ContinuousCharacterLine A χ) :
    equiv B ψ (reduction A χ ψ π a) = π (equiv A χ a) := rfl

/-- Character compatibility is the precise additional condition for group equivariance. -/
theorem reduction_smul (hχψ : ∀ g : G, π (χ g : A) = (ψ g : B))
    (g : G) (a : ContinuousCharacterLine A χ) :
    reduction A χ ψ π (g • a) = g • reduction A χ ψ π a := by
  apply (equiv B ψ).injective
  simp only [reduction_apply, smul_def, map_mul, hχψ]

/-- Surjective coefficient reduction is surjective on the corresponding lines. -/
theorem reduction_surjective (hπ : Function.Surjective π) :
    Function.Surjective (reduction A χ ψ π) := by
  intro b
  obtain ⟨a, ha⟩ := hπ (equiv B ψ b)
  exact ⟨(equiv A χ).symm a, (equiv B ψ).injective ha⟩

/-- Continuous ring reduction is continuous on the inherited line topologies. -/
theorem continuous_reduction [TopologicalSpace A] [TopologicalSpace B]
    (hπ : Continuous π) : Continuous (reduction A χ ψ π) := hπ

/-- Coefficient reduction as a bundled continuous semilinear map. -/
def continuousReduction [TopologicalSpace A] [TopologicalSpace B] (hπ : Continuous π) :
    ContinuousCharacterLine A χ →SL[π] ContinuousCharacterLine B ψ where
  toLinearMap := reduction A χ ψ π
  cont := continuous_reduction A χ ψ π hπ

end Reduction

end ContinuousCharacterLine
end ZInQ.Contrib.RC53Assist.IntegralDuality
