import ZInQKernel.HDecomp.Conductor.I6Base

/-!
# Actual ring automorphisms and canonical restriction in T22

These bridges use Mathlib 4.35's `galRestrict`, not an abstract filtration or a
chosen identification of unrelated groups. The rings are finite integrally
closed domains, so their automorphisms are precisely the automorphisms of their
fraction fields. No finite-residue or local-compactness assumption is used.
-/

namespace ZInQ.Contrib.Herbrand

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section FractionAut

variable (A B : Type*) [CommRing A] [IsDomain A] [CommRing B] [IsDomain B]
  [Algebra A B] [Module.Finite A B] [Module.IsTorsionFree A B] [IsIntegrallyClosed B]

/-- The actual restriction from fraction-field automorphisms to ring automorphisms. -/
noncomputable def fractionAutEquiv :
    (FractionRing B ≃ₐ[FractionRing A] FractionRing B) ≃* (B ≃ₐ[A] B) :=
  galRestrict A (FractionRing A) (FractionRing B) B

@[simp]
theorem fractionAutEquiv_apply (σ : FractionRing B ≃ₐ[FractionRing A] FractionRing B)
    (b : B) :
    algebraMap B (FractionRing B) (fractionAutEquiv A B σ b) =
      σ (algebraMap B (FractionRing B) b) :=
  algebraMap_galRestrict_apply A σ b

@[simp]
theorem fractionAutEquiv_symm_apply (σ : B ≃ₐ[A] B) (b : B) :
    (fractionAutEquiv A B).symm σ (algebraMap B (FractionRing B) b) =
      algebraMap B (FractionRing B) (σ b) :=
  galRestrict_symm_algebraMap_apply A (FractionRing A) σ b

/-- Finiteness is derived from the finite ring extension, not a new leaf hypothesis. -/
theorem finite_ringAut : Finite (B ≃ₐ[A] B) := inferInstance

/-- The ring automorphism action has invariant ring exactly `A` when the fraction extension
is Galois. This is the invariant-ring input needed by the coset polynomial proof. -/
theorem ringAut_isGaloisGroup [IsIntegrallyClosed A]
    [IsGalois (FractionRing A) (FractionRing B)] : IsGaloisGroup (B ≃ₐ[A] B) A B := by
  let : MulSemiringAction (FractionRing B ≃ₐ[FractionRing A] FractionRing B) B :=
    IsIntegralClosure.MulSemiringAction A (FractionRing A) (FractionRing B) B
  have : IsGaloisGroup (FractionRing B ≃ₐ[FractionRing A] FractionRing B) A B :=
    IsGaloisGroup.of_isFractionRing _ A B (FractionRing A) (FractionRing B)
  apply IsGaloisGroup.of_mulEquiv (fractionAutEquiv A B).symm
  intro σ b
  change fractionAutEquiv A B ((fractionAutEquiv A B).symm σ) b = σ b
  rw [MulEquiv.apply_symm_apply]

end FractionAut

section Tower

variable (A C B : Type*) [CommRing A] [IsDomain A]
  [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra A C]
  [Module.Finite A C] [Module.IsTorsionFree A C]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B]
  [Module.Finite A B] [Module.IsTorsionFree A B]
  [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]
  [Normal (FractionRing A) (FractionRing C)]

/-- Restriction in the actual tower, transported through the canonical fraction/ring
isomorphisms. It is not an arbitrary map between filtration carriers. -/
noncomputable def canonicalRestriction : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C) :=
  (fractionAutEquiv A C).toMonoidHom.comp
    ((AlgEquiv.restrictNormalHom (FractionRing C)).comp
      (fractionAutEquiv A B).symm.toMonoidHom)

theorem canonicalRestriction_commutes (σ : B ≃ₐ[A] B) (c : C) :
    algebraMap C B (canonicalRestriction A C B σ c) = σ (algebraMap C B c) := by
  apply IsFractionRing.injective B (FractionRing B)
  have h := AlgEquiv.restrictNormal_commutes ((fractionAutEquiv A B).symm σ)
    (FractionRing C) (algebraMap C (FractionRing C) c)
  change algebraMap B (FractionRing B) (algebraMap C B
      (fractionAutEquiv A C (AlgEquiv.restrictNormalHom (FractionRing C)
        ((fractionAutEquiv A B).symm σ)) c)) = _
  rw [← IsScalarTower.algebraMap_apply C B (FractionRing B),
    IsScalarTower.algebraMap_apply C (FractionRing C) (FractionRing B),
    fractionAutEquiv_apply]
  change algebraMap (FractionRing C) (FractionRing B)
      (((fractionAutEquiv A B).symm σ).restrictNormal (FractionRing C)
        (algebraMap C (FractionRing C) c)) = _
  rw [h, ← IsScalarTower.algebraMap_apply C (FractionRing C) (FractionRing B),
    IsScalarTower.algebraMap_apply C B (FractionRing B), fractionAutEquiv_symm_apply]

/-- The compatibility equation in the target uniquely determines restriction. -/
theorem restriction_unique (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) :
    r = canonicalRestriction A C B := by
  ext σ c
  apply FaithfulSMul.algebraMap_injective C B
  exact (hr σ c).trans (canonicalRestriction_commutes A C B σ c).symm

/-- Surjectivity is proved from normality of the fraction fields. -/
theorem canonicalRestriction_surjective [Normal (FractionRing A) (FractionRing B)] :
    Function.Surjective (canonicalRestriction A C B) :=
  (fractionAutEquiv A C).surjective.comp
    ((AlgEquiv.restrictNormalHom_surjective (F := FractionRing A)
      (K₁ := FractionRing C) (E := FractionRing B)).comp
      (fractionAutEquiv A B).symm.surjective)

theorem restriction_surjective [Normal (FractionRing A) (FractionRing B)]
    (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) :
    Function.Surjective r := by
  rw [restriction_unique A C B r hr]
  exact canonicalRestriction_surjective A C B

end Tower

section Kernel

variable (A C B : Type*) [CommRing A] [CommRing C] [CommRing B]
  [Algebra A C] [Algebra A B] [Algebra C B] [IsScalarTower A C B] [FaithfulSMul C B]

/-- The kernel in the target is precisely the actual ring automorphisms fixing `C`.
This statement does not need normality of `C/A`, only the supplied compatibility. -/
theorem restriction_ker_eq_range (r : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C))
    (hr : ∀ σ c, algebraMap C B (r σ c) = σ (algebraMap C B c)) :
    r.ker = (AlgEquiv.restrictScalarsHom (S := C) A).range := by
  ext σ
  constructor
  · intro hσ
    have hσ' : r σ = 1 := hσ
    let τ : B ≃ₐ[C] B := { σ with
      commutes' := fun c => by
        change σ (algebraMap C B c) = algebraMap C B c
        have h := hr σ c
        rw [hσ'] at h
        simpa only [AlgEquiv.one_apply] using h.symm }
    exact ⟨τ, AlgEquiv.ext fun _ => rfl⟩
  · rintro ⟨τ, rfl⟩
    apply AlgEquiv.ext
    intro c
    apply FaithfulSMul.algebraMap_injective C B
    rw [hr]
    exact τ.commutes c

end Kernel

end ZInQ.Contrib.Herbrand

#print axioms ZInQ.Contrib.Herbrand.ringAut_isGaloisGroup
#print axioms ZInQ.Contrib.Herbrand.restriction_unique
#print axioms ZInQ.Contrib.Herbrand.restriction_surjective
