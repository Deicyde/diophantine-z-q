module

public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp

/-! # Extending geometric points along an integral inclusion -/

@[expose] public section

namespace RC.ModelInvariants

variable {R A B k : Type*} [CommRing R] [CommRing A] [CommRing B] [Field k]
  [Algebra R A] [Algebra R B] [Algebra R k] [Algebra A B] [IsScalarTower R A B]

/-- An integral inclusion is surjective on geometric points over any base. -/
theorem liftIntegralPoint [Algebra.IsIntegral A B] [IsAlgClosed k]
    (hinj : Function.Injective (algebraMap A B)) (f : A →ₐ[R] k) :
    ∃ F : B →ₐ[R] k, F.comp (IsScalarTower.toAlgHom R A B) = f := by
  let p := RingHom.ker f.toRingHom
  let : p.IsPrime := RingHom.ker_isPrime _
  obtain ⟨q, -, hq, hover⟩ := Ideal.exists_ideal_over_prime_of_isIntegral p (⊥ : Ideal B)
    (by simp [← RingHom.ker_eq_comap_bot,
      (RingHom.injective_iff_ker_eq_bot _).mp hinj])
  let : q.IsPrime := hq
  let : q.LiesOver p := (Ideal.liesOver_iff _ _).2 hover.symm
  let : Algebra (A ⧸ p) k := (RingHom.kerLift f.toRingHom).toAlgebra
  let : FaithfulSMul (A ⧸ p) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective _)
  let : Algebra.IsIntegral (A ⧸ p) (B ⧸ q) := by
    constructor
    intro x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact (Algebra.IsIntegral.isIntegral (R := A) b).map_of_comp_eq
      (Ideal.Quotient.mk p) (Ideal.Quotient.mk q) (RingHom.ext fun _ => rfl)
  let lift : B ⧸ q →ₐ[A ⧸ p] k := IsAlgClosed.lift
  have hlift (a : A) : lift (Ideal.Quotient.mk q (algebraMap A B a)) = f a :=
    lift.commutes (Ideal.Quotient.mk p a)
  let F : B →ₐ[R] k :=
    { lift.toRingHom.comp (Ideal.Quotient.mk q) with
      commutes' := fun r => by
        change lift (Ideal.Quotient.mk q (algebraMap R B r)) = _
        rw [IsScalarTower.algebraMap_apply R A B, hlift, f.commutes] }
  exact ⟨F, AlgHom.ext hlift⟩

#print axioms liftIntegralPoint

end RC.ModelInvariants
