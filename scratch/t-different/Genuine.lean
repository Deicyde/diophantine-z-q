import Mathlib

open IsLocalRing Polynomial

namespace TDifferent

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

section GaloisSetup

variable (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
  [IsGalois (FractionRing A) (FractionRing B)]

omit [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
theorem isGaloisGroup_algEquiv : IsGaloisGroup (B ≃ₐ[A] B) A B := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) :=
    .of_isLocalization A B (nonZeroDivisors A)
  exact ⟨inferInstance, inferInstance,
    Algebra.isInvariant_of_isGalois' A (FractionRing A) (FractionRing B) B⟩

omit [Algebra.IsSeparable (FractionRing A) (FractionRing B)] [IsGalois (FractionRing A) (FractionRing B)] in
theorem finite_algEquiv : Finite (B ≃ₐ[A] B) := by
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) (FractionRing B) :=
    IsIntegralClosure.isLocalization _ (FractionRing A) _ _
  have : FiniteDimensional (FractionRing A) (FractionRing B) :=
    .of_isLocalization A B (nonZeroDivisors A)
  exact Finite.of_equiv _ (galRestrict A (FractionRing A) (FractionRing B) B).toEquiv

end GaloisSetup

section Tower

variable (A C B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing C] [IsDomain C] [IsIntegrallyClosed C] [Algebra A C] [Module.Finite A C]
  [Module.IsTorsionFree A C] [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]

/-- The restriction `Gal(B/A) → Gal(C/A)`. -/
noncomputable def resHom : (B ≃ₐ[A] B) →* (C ≃ₐ[A] C) :=
  haveI := finite_algEquiv A B
  haveI := finite_algEquiv A C
  haveI := isGaloisGroup_algEquiv A B
  haveI := isGaloisGroup_algEquiv A C
  IsGaloisGroup.restrictHom (B ≃ₐ[A] B) (C ≃ₐ[A] C) A C B

theorem resHom_apply (g : B ≃ₐ[A] B) (c : C) :
    algebraMap C B (resHom A C B g c) = g (algebraMap C B c) := by
  have := finite_algEquiv A B
  have := finite_algEquiv A C
  have := isGaloisGroup_algEquiv A B
  have := isGaloisGroup_algEquiv A C
  exact IsGaloisGroup.algebraMap_restrictHom_smul (B ≃ₐ[A] B) (C ≃ₐ[A] C) A C B g c

theorem resHom_surjective : Function.Surjective (resHom A C B) := by
  have := finite_algEquiv A B
  have := finite_algEquiv A C
  have := isGaloisGroup_algEquiv A B
  have := isGaloisGroup_algEquiv A C
  exact IsGaloisGroup.restrictHom_surjective (B ≃ₐ[A] B) (C ≃ₐ[A] C) A C B

theorem resHom_eq_one_iff (g : B ≃ₐ[A] B) :
    resHom A C B g = 1 ↔ ∃ h : B ≃ₐ[C] B, AlgEquiv.restrictScalarsHom A h = g := by
  have hinj : Function.Injective (algebraMap C B) := FaithfulSMul.algebraMap_injective C B
  constructor
  · intro h1
    refine ⟨AlgEquiv.ofRingEquiv (f := (g : B ≃+* B)) (fun c => ?_), ?_⟩
    · have := resHom_apply A C B g c
      rw [h1] at this
      exact this.symm
    · ext b; rfl
  · rintro ⟨h, rfl⟩
    ext c
    apply hinj
    rw [resHom_apply]
    exact h.commutes c

include A in
omit [IsGalois (FractionRing A) (FractionRing C)] [Module.Finite A C] in
/-- `B ≃ₐ[C] B` is a Galois group of `B/C`. -/
theorem isGaloisGroup_tower : IsGaloisGroup (B ≃ₐ[C] B) C B := by
  have := finite_algEquiv A B
  have := isGaloisGroup_algEquiv A B
  have hG := IsGaloisGroup.of_isScalarTower (B ≃ₐ[A] B) A B C
  refine ⟨inferInstance, inferInstance, ⟨fun b hb => ?_⟩⟩
  refine hG.isInvariant.isInvariant b (fun g => ?_)
  have hg : ∀ c : C, (g : B ≃ₐ[A] B) (algebraMap C B c) = algebraMap C B c := fun c =>
    (mem_fixingSubgroup_iff _).mp g.2 _ ⟨c, rfl⟩
  have := hb (AlgEquiv.ofRingEquiv (f := ((g : B ≃ₐ[A] B) : B ≃+* B)) hg)
  exact this

end Tower

section Product

/-- If `S = R[x]` and `|Aut_R(S)| = deg minpoly`, the minimal polynomial splits as
`∏_σ (X - σ x)`. -/
theorem minpoly_map_eq_prod {R S : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    [CommRing S] [IsDomain S] [Algebra R S] [Module.IsTorsionFree R S]
    [Fintype (S ≃ₐ[R] S)] {x : S} (hint : IsIntegral R x) (hx : Algebra.adjoin R {x} = ⊤)
    (hcard : Fintype.card (S ≃ₐ[R] S) = (minpoly R x).natDegree) :
    (minpoly R x).map (algebraMap R S) = ∏ σ : S ≃ₐ[R] S, (X - C (σ x)) := by
  classical
  have hinj : Function.Injective (fun σ : S ≃ₐ[R] S => σ x) := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    exact AlgHom.ext_of_adjoin_eq_top hx (fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact h)
  set T : Multiset S := Finset.univ.val.map (fun σ : S ≃ₐ[R] S => σ x)
  set f := (minpoly R x).map (algebraMap R S)
  have hf0 : f ≠ 0 := ((minpoly.monic hint).map _).ne_zero
  have hTroots : T ≤ f.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)]
    intro y hy
    obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.mp hy
    rw [mem_roots hf0, IsRoot.def, eval_map_algebraMap]
    have : aeval (σ x) (minpoly R x) = σ (aeval x (minpoly R x)) :=
      (Polynomial.aeval_algHom_apply (σ : S →ₐ[R] S) x _)
    rw [this, minpoly.aeval, map_zero]
  have hfT : f = (T.map fun a => X - C a).prod := by
    refine eq_of_monic_of_dvd_of_natDegree_le (monic_multiset_prod_of_monic _ _
      fun a _ => monic_X_sub_C a) ((minpoly.monic hint).map _)
      ((Multiset.prod_X_sub_C_dvd_iff_le_roots hf0 T).mpr hTroots) ?_
    rw [natDegree_multiset_prod_X_sub_C_eq_card, (minpoly.monic hint).natDegree_map, ← hcard]
    simp [T]
  rw [hfT, Finset.prod_eq_multiset_prod, Multiset.map_map]
  rfl

end Product

end TDifferent
