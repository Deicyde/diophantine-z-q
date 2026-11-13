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

section Prop3

variable (A C B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing C] [IsDomain C] [IsDiscreteValuationRing C] [Algebra A C] [Module.Finite A C]
  [Module.IsTorsionFree A C] [IsGalois (FractionRing A) (FractionRing C)]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [IsGalois (FractionRing A) (FractionRing B)]
  [Algebra C B] [IsScalarTower A C B] [Module.IsTorsionFree C B]

omit [IsDiscreteValuationRing C] [Module.Finite A C] [IsGalois (FractionRing A) (FractionRing C)] in
theorem adjoin_tower_eq_top {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    Algebra.adjoin C {x} = ⊤ := by
  rw [eq_top_iff]
  intro b hb0
  clear hb0
  have hb : b ∈ Algebra.adjoin A {x} := hx ▸ Algebra.mem_top
  induction hb using Algebra.adjoin_induction with
  | mem z hz => exact Algebra.subset_adjoin hz
  | algebraMap r =>
      rw [IsScalarTower.algebraMap_apply A C B]; exact Subalgebra.algebraMap_mem _ _
  | add a b _ _ ha hb => exact add_mem ha hb
  | mul a b _ _ ha hb => exact mul_mem ha hb

include A in
omit [Module.Finite A C] [IsGalois (FractionRing A) (FractionRing C)] in
theorem finite_tower : Finite (B ≃ₐ[C] B) := by
  have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
  have := isGaloisGroup_tower A C B
  exact IsGaloisGroup.finite (B ≃ₐ[C] B) C B

omit [Module.Finite A C] [IsGalois (FractionRing A) (FractionRing C)] in
theorem card_tower_eq [Fintype (B ≃ₐ[C] B)] {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    Fintype.card (B ≃ₐ[C] B) = (minpoly C x).natDegree := by
  have hxC := adjoin_tower_eq_top A C B hx
  have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
  have := isGaloisGroup_tower A C B
  have : Finite (B ≃ₐ[C] B) := IsGaloisGroup.finite (B ≃ₐ[C] B) C B
  rw [← Nat.card_eq_fintype_card, IsGaloisGroup.card_eq_finrank' (B ≃ₐ[C] B) C B,
    (IsAdjoinRootMonic.mkOfAdjoinEqTop' hxC).finrank]

open Classical in
/-- **Serre, *Corps locaux*, IV §1, Prop. 3, ideal form.** If `B = A[x]` and `C = A[y]`, then for
`σ ∈ Gal(C/A)`, `(σ y - y) B = (∏_{s ↦ σ} (x - s x))`. -/
theorem span_sub_eq_span_prod {x : B} (hx : Algebra.adjoin A {x} = ⊤) {y : C}
    (hy : Algebra.adjoin A {y} = ⊤) [Fintype (B ≃ₐ[A] B)] (σ : C ≃ₐ[A] C) :
    Ideal.span {algebraMap C B (σ y - y)} =
      Ideal.span {∏ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), (x - s x)} := by
  classical
  have := finite_tower A C B
  have := Fintype.ofFinite (B ≃ₐ[C] B)
  have hxC := adjoin_tower_eq_top A C B hx
  have hint : IsIntegral C x := by
    have : Module.Finite C B := Module.Finite.of_restrictScalars_finite A C B
    exact Algebra.IsIntegral.isIntegral x
  have hprod := minpoly_map_eq_prod hint hxC (card_tower_eq A C B hx)
  obtain ⟨s0, hs0⟩ := resHom_surjective A C B σ
  have hs0c : ∀ c : C, s0 (algebraMap C B c) = algebraMap C B (σ c) := fun c => by
    rw [← resHom_apply, hs0]
  set f := minpoly C x with hf_def
  -- the fibre product
  have hfib : ∏ s ∈ Finset.univ.filter (fun s => resHom A C B s = σ), (x - s x) =
      ∏ h : B ≃ₐ[C] B, (x - s0 (h x)) := by
    symm
    apply Finset.prod_nbij (fun h => s0 * AlgEquiv.restrictScalarsHom A h)
    · intro h _
      have h1 : resHom A C B (AlgEquiv.restrictScalars A h) = 1 :=
        (resHom_eq_one_iff A C B _).mpr ⟨h, rfl⟩
      simp [Finset.mem_filter, map_mul, h1, hs0]
    · intro a _ b _ e
      have := mul_left_cancel e
      exact AlgEquiv.restrictScalars_injective A this
    · intro s hs
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hs
      obtain ⟨h, hh⟩ := (resHom_eq_one_iff A C B (s0⁻¹ * s)).mp
        (by rw [map_mul, map_inv, hs, hs0, inv_mul_cancel])
      refine ⟨h, Finset.mem_coe.mpr (Finset.mem_univ _), ?_⟩
      show s0 * AlgEquiv.restrictScalarsHom A h = s
      rw [hh, mul_inv_cancel_left]
    · intro h _; rfl
  -- `P = f^σ(x)`
  have hP : ∏ h : B ≃ₐ[C] B, (x - s0 (h x)) = aeval x (f.map (σ : C →+* C)) := by
    have hcomp : (algebraMap C B).comp (σ : C →+* C) = (s0 : B →+* B).comp (algebraMap C B) := by
      ext c; simp [hs0c]
    rw [← eval_map_algebraMap, Polynomial.map_map, hcomp, ← Polynomial.map_map, hprod,
      Polynomial.map_prod, eval_prod]
    refine Finset.prod_congr rfl fun h _ => ?_
    simp
  rw [hfib, hP]
  apply le_antisymm
  · -- `(σ y - y) ∈ (f^σ(x))`
    rw [Ideal.span_singleton_le_iff_mem]
    obtain ⟨g, hg⟩ : ∃ g : A[X], aeval x g = algebraMap C B y := by
      have : algebraMap C B y ∈ Algebra.adjoin A {x} := hx ▸ Algebra.mem_top
      rw [Algebra.adjoin_singleton_eq_range_aeval] at this
      exact this
    set gC : C[X] := g.map (algebraMap A C) - Polynomial.C y
    have hgC : aeval x gC = 0 := by
      simp only [gC, map_sub, aeval_C, aeval_map_algebraMap, hg, sub_self]
    obtain ⟨q, hq⟩ := minpoly.isIntegrallyClosed_dvd hint hgC
    have hσA : (σ : C →+* C).comp (algebraMap A C) = algebraMap A C := by
      ext a; simp
    have hmap : gC.map (σ : C →+* C) = (f.map (σ : C →+* C)) * (q.map (σ : C →+* C)) := by
      rw [hq, Polynomial.map_mul]
    have hmap' : gC.map (σ : C →+* C) = g.map (algebraMap A C) - Polynomial.C (σ y) := by
      simp only [gC, Polynomial.map_sub, Polynomial.map_map, hσA, map_C]
      rfl
    have key : algebraMap C B y - algebraMap C B (σ y) =
        aeval x (f.map (σ : C →+* C)) * aeval x (q.map (σ : C →+* C)) := by
      rw [← map_mul, ← hmap, hmap', map_sub, aeval_C, aeval_map_algebraMap, hg]
    rw [Ideal.mem_span_singleton']
    exact ⟨-aeval x (q.map (σ : C →+* C)), by rw [map_sub, neg_mul, mul_comm, ← key]; ring⟩
  · -- `f^σ(x) ∈ (σ y - y)`
    rw [Ideal.span_singleton_le_iff_mem]
    have hcoef : ∀ c : C, σ c - c ∈ Ideal.span {σ y - y} := by
      intro c
      have hc : c ∈ Algebra.adjoin A {y} := hy ▸ Algebra.mem_top
      induction hc using Algebra.adjoin_induction with
      | mem z hz =>
          rw [Set.mem_singleton_iff.mp hz]; exact Ideal.mem_span_singleton_self _
      | algebraMap r => simp
      | add a b _ _ ha hb =>
          have : σ (a + b) - (a + b) = (σ a - a) + (σ b - b) := by rw [map_add]; ring
          rw [this]; exact Ideal.add_mem _ ha hb
      | mul a b _ _ ha hb =>
          have : σ (a * b) - a * b = σ a * (σ b - b) + (σ a - a) * b := by rw [map_mul]; ring
          rw [this]; exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hb) (Ideal.mul_mem_right _ _ ha)
    have h0 : aeval x f = 0 := minpoly.aeval C x
    have : aeval x (f.map (σ : C →+* C)) = aeval x (f.map (σ : C →+* C) - f) := by
      rw [map_sub, h0, sub_zero]
    rw [this, aeval_eq_sum_range]
    refine Ideal.sum_mem _ fun i _ => ?_
    rw [Algebra.smul_def]
    refine Ideal.mul_mem_right _ _ ?_
    rw [coeff_sub, coeff_map]
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hcoef (f.coeff i))
    rw [show (σ : C →+* C) (f.coeff i) = σ (f.coeff i) from rfl, ← hd, map_mul, mul_comm]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

end Prop3

end TDifferent
