import Mathlib

/-!
# t-different: Hilbert's different formula (local, T20 = PkgI6.HilbertDifferentFormula)
# from the monogenicity of the extension (Serre, *Corps locaux*, III §6, Prop. 12)

Check with `lake env lean scratch/t-different/HilbertLocal.lean`.
-/

open IsLocalRing Polynomial

namespace TDifferent

/-! ### Verbatim copy of the definitions of `PkgI6` used (Leaves.lean lines 5029-5045). -/

section Ramification

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

def lowerRam (i : ℕ) : Subgroup (B ≃ₐ[A] B) :=
  (maximalIdeal B ^ (i + 1)).toAddSubgroup.inertia (B ≃ₐ[A] B)

lemma mem_lowerRam {i : ℕ} {σ : B ≃ₐ[A] B} :
    σ ∈ lowerRam A B i ↔ ∀ b : B, σ b - b ∈ maximalIdeal B ^ (i + 1) := Iff.rfl

end Ramification

/-! ### Counting: `∑_{i<N} (|G_i| - 1) = ∑_{σ ≠ 1} i_G(σ)`. -/

section Counting

variable {G : Type*} [Group G] [Fintype G] [DecidableEq G]

open Classical in
theorem card_sub_one_eq (H : Subgroup G) :
    Nat.card H - 1 = ((Finset.univ.erase 1).filter (· ∈ H)).card := by
  classical
  have h1 : Nat.card H = (Finset.univ.filter (· ∈ H)).card := by
    rw [Nat.card_eq_fintype_card]
    convert Fintype.card_subtype (fun σ => σ ∈ H)
  rw [h1, Finset.filter_erase, Finset.card_erase_of_mem (by simp [H.one_mem])]

theorem sum_card_sub_one (H : ℕ → Subgroup G) (n : G → ℕ) (N : ℕ)
    (hH : ∀ i σ, σ ≠ 1 → (σ ∈ H i ↔ i < n σ)) (hN : ∀ σ, σ ≠ 1 → n σ ≤ N) :
    ∑ i ∈ Finset.range N, (Nat.card (H i) - 1) = ∑ σ ∈ Finset.univ.erase 1, n σ := by
  classical
  calc ∑ i ∈ Finset.range N, (Nat.card (H i) - 1)
      = ∑ i ∈ Finset.range N, ((Finset.univ.erase 1).filter (fun σ => i < n σ)).card := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [card_sub_one_eq]
        exact congrArg Finset.card <| Finset.filter_congr fun σ hσ => hH i σ (Finset.ne_of_mem_erase hσ)
    _ = ∑ i ∈ Finset.range N, ∑ σ ∈ Finset.univ.erase 1, if i < n σ then 1 else 0 := by
        simp only [Finset.card_filter]
    _ = ∑ σ ∈ Finset.univ.erase 1, ∑ i ∈ Finset.range N, if i < n σ then 1 else 0 :=
        Finset.sum_comm
    _ = ∑ σ ∈ Finset.univ.erase 1, n σ := by
        refine Finset.sum_congr rfl fun σ hσ => ?_
        rw [← Finset.card_filter]
        have hle := hN σ (Finset.ne_of_mem_erase hσ)
        have : (Finset.range N).filter (fun i => i < n σ) = Finset.range (n σ) := by
          ext i; simp only [Finset.mem_filter, Finset.mem_range]; omega
        rw [this, Finset.card_range]

end Counting

/-! ### If `B = A[x]`, then `σ ∈ G_I ↔ σ x - x ∈ I`. -/

theorem mem_inertia_iff_of_adjoin {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {x : B} (hx : Algebra.adjoin A {x} = ⊤) (I : Ideal B) (σ : B ≃ₐ[A] B) :
    σ ∈ I.toAddSubgroup.inertia (B ≃ₐ[A] B) ↔ σ x - x ∈ I := by
  refine ⟨fun h => h x, fun h b => ?_⟩
  have hb : b ∈ Algebra.adjoin A {x} := hx ▸ Algebra.mem_top
  change σ b - b ∈ I
  induction hb using Algebra.adjoin_induction with
  | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact h
  | algebraMap r => simp
  | add y z _ _ hy hz =>
      have : σ (y + z) - (y + z) = (σ y - y) + (σ z - z) := by rw [map_add]; ring
      rw [this]; exact I.add_mem hy hz
  | mul y z _ _ hy hz =>
      have : σ (y * z) - y * z = σ y * (σ z - z) + (σ y - y) * z := by rw [map_mul]; ring
      rw [this]; exact I.add_mem (I.mul_mem_left _ hz) (I.mul_mem_right _ hy)

/-! ### Valuations in a DVR. -/

section DVR

variable {B : Type*} [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

theorem span_eq_maximalIdeal_pow {a : B} (ha : a ≠ 0) :
    ∃ n, Ideal.span {a} = maximalIdeal B ^ n := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨n, hn⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {a}) (by simpa using ha) hϖ
  exact ⟨n, by rw [hn, hϖ.maximalIdeal_eq, Ideal.span_singleton_pow]⟩

theorem maximalIdeal_pow_le_iff {m n : ℕ} :
    maximalIdeal B ^ m ≤ maximalIdeal B ^ n ↔ n ≤ m :=
  (Ideal.pow_right_strictAnti _ (IsDiscreteValuationRing.not_a_field B)
    (maximalIdeal.isMaximal B).ne_top).le_iff_ge

end DVR

/-! ### The derivative of the minimal polynomial of a generator, Galois case. -/

section Product

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

variable (A B : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
  [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

omit [IsIntegrallyClosed A] [Algebra.IsSeparable (FractionRing A) (FractionRing B)] in
/-- If `B = A[x]` then `Frac B = (Frac A)(x)`. -/
theorem adjoin_fractionRing_eq_top {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    Algebra.adjoin (FractionRing A) {algebraMap B (FractionRing B) x} = ⊤ := by
  set K := FractionRing A
  set L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B (nonZeroDivisors A)
  set S := Algebra.adjoin K {algebraMap B L x}
  have hB : ∀ b : B, algebraMap B L b ∈ S := by
    intro b
    have hb : b ∈ Algebra.adjoin A {x} := hx ▸ Algebra.mem_top
    induction hb using Algebra.adjoin_induction with
    | mem y hy => rw [Set.mem_singleton_iff.mp hy]; exact Algebra.subset_adjoin rfl
    | algebraMap r =>
        rw [← IsScalarTower.algebraMap_apply, IsScalarTower.algebraMap_apply A K L]
        exact S.algebraMap_mem _
    | add y z _ _ hy hz => rw [map_add]; exact S.add_mem hy hz
    | mul y z _ _ hy hz => rw [map_mul]; exact S.mul_mem hy hz
  rw [eq_top_iff]
  intro z _
  obtain ⟨b, s, _, rfl⟩ := IsFractionRing.div_surjective (A := B) z
  rw [div_eq_mul_inv]
  refine S.mul_mem (hB b) ?_
  exact S.inv_mem_of_algebraic (x := ⟨_, hB s⟩) (Algebra.IsAlgebraic.isAlgebraic _)

variable [IsGalois (FractionRing A) (FractionRing B)]

/-- `f'(x) = ∏_{σ ≠ 1} (x - σ x)` for `f` the minimal polynomial of a generator `x` of `B/A`. -/
theorem aeval_derivative_minpoly_eq_prod [Fintype (B ≃ₐ[A] B)] [DecidableEq (B ≃ₐ[A] B)]
    {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    aeval x (derivative (minpoly A x)) = ∏ σ ∈ Finset.univ.erase (1 : B ≃ₐ[A] B), (x - σ x) := by
  classical
  set K := FractionRing A
  set L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B (nonZeroDivisors A)
  have hAx : IsIntegral A x := Algebra.IsIntegral.isIntegral x
  have hKx : IsIntegral K (algebraMap B L x) := Algebra.IsIntegral.isIntegral _
  -- injectivity of `σ ↦ σ x`
  have hinj : Function.Injective (fun σ : B ≃ₐ[A] B => σ x) := by
    intro σ τ h
    apply AlgEquiv.coe_toAlgHom_injective
    exact AlgHom.ext_of_adjoin_eq_top hx (fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact h)
  -- the degree of the minimal polynomial is `|G|`
  have hdeg : (minpoly A x).natDegree = Fintype.card (B ≃ₐ[A] B) := by
    have h1 : (minpoly A x).natDegree = (minpoly K (algebraMap B L x)).natDegree := by
      rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hAx,
        (minpoly.monic hAx).natDegree_map]
    have h2 : IntermediateField.adjoin K {algebraMap B L x} = ⊤ := by
      rw [← IntermediateField.toSubalgebra_inj,
        IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hKx.isAlgebraic,
        IntermediateField.top_toSubalgebra]
      exact adjoin_fractionRing_eq_top A B hx
    have h3 : Fintype.card (B ≃ₐ[A] B) = Module.finrank K L := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_congr (galRestrict A K L B).toEquiv,
        IsGalois.card_aut_eq_finrank]
    rw [h1, h3, ← IntermediateField.adjoin.finrank hKx, h2, IntermediateField.finrank_top']
  -- `f = ∏_σ (X - σ x)` in `B[X]`
  set S : Multiset B := Finset.univ.val.map (fun σ : B ≃ₐ[A] B => σ x)
  set f := (minpoly A x).map (algebraMap A B)
  have hf0 : f ≠ 0 := ((minpoly.monic hAx).map _).ne_zero
  have hSroots : S ≤ f.roots := by
    rw [Multiset.le_iff_subset (Multiset.Nodup.map hinj Finset.univ.nodup)]
    intro y hy
    obtain ⟨σ, -, rfl⟩ := Multiset.mem_map.mp hy
    rw [mem_roots hf0, IsRoot.def, eval_map_algebraMap]
    have : aeval (σ x) (minpoly A x) = σ (aeval x (minpoly A x)) :=
      (Polynomial.aeval_algHom_apply (σ : B →ₐ[A] B) x _)
    rw [this, minpoly.aeval, map_zero]
  have hfS : f = (S.map fun a => X - C a).prod := by
    refine eq_of_monic_of_dvd_of_natDegree_le (monic_multiset_prod_of_monic _ _
      fun a _ => monic_X_sub_C a) ((minpoly.monic hAx).map _)
      ((Multiset.prod_X_sub_C_dvd_iff_le_roots hf0 S).mpr hSroots) ?_
    rw [natDegree_multiset_prod_X_sub_C_eq_card, (minpoly.monic hAx).natDegree_map, hdeg]
    simp [S]
  have hxS : x ∈ S := Multiset.mem_map.mpr ⟨1, Finset.mem_univ_val _, rfl⟩
  rw [← eval_map_algebraMap, ← derivative_map]
  change eval x (derivative f) = _
  rw [hfS, eval_multiset_prod_X_sub_C_derivative hxS]
  have : S.erase x = (Finset.univ.erase (1 : B ≃ₐ[A] B)).val.map (fun σ => σ x) := by
    rw [Finset.erase_val, Finset.univ.nodup.erase_eq_filter]
    rw [show x = (fun σ : B ≃ₐ[A] B => σ x) 1 from rfl, ← Multiset.map_erase _ hinj]
    simp [Finset.univ.nodup.erase_eq_filter]
  rw [this, Multiset.map_map, Finset.prod_eq_multiset_prod]
  rfl

end Product

/-! ### Hilbert's formula when `B = A[x]`. -/

section Main

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- **Hilbert's different formula for a monogenic Galois extension of DVRs.** If `B = A[x]`
(no completeness or residue-field hypothesis is needed for this step), then some `G_N` is trivial
and `𝔇_{B/A} = 𝔪_B ^ ∑_{i<N} (|G_i| - 1)`. -/
theorem hilbertDifferentFormula_of_adjoin_eq_top
    (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)] {x : B} (hx : Algebra.adjoin A {x} = ⊤) :
    ∃ N : ℕ, lowerRam A B N = ⊥ ∧
      differentIdeal A B =
        maximalIdeal B ^ (∑ i ∈ Finset.range N, (Nat.card (lowerRam A B i) - 1)) := by
  classical
  set K := FractionRing A
  set L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B (nonZeroDivisors A)
  have : Finite (B ≃ₐ[A] B) := Finite.of_equiv _ (galRestrict A K L B).toEquiv
  have := Fintype.ofFinite (B ≃ₐ[A] B)
  have hD : differentIdeal A B =
      Ideal.span {∏ σ ∈ Finset.univ.erase (1 : B ≃ₐ[A] B), (x - σ x)} := by
    have h := conductor_mul_differentIdeal A K L x (adjoin_fractionRing_eq_top A B hx)
    rw [conductor_eq_top_of_adjoin_eq_top hx, Ideal.top_mul,
      aeval_derivative_minpoly_eq_prod A B hx] at h
    exact h
  have hne : ∀ σ : B ≃ₐ[A] B, σ ≠ 1 → x - σ x ≠ 0 := by
    intro σ hσ h
    apply hσ
    apply AlgEquiv.coe_toAlgHom_injective
    exact AlgHom.ext_of_adjoin_eq_top hx (fun y hy => by
      rw [Set.mem_singleton_iff.mp hy]; exact (sub_eq_zero.mp h).symm)
  have hn : ∀ σ : B ≃ₐ[A] B, ∃ n : ℕ, σ ≠ 1 → Ideal.span {x - σ x} = maximalIdeal B ^ n := by
    intro σ
    by_cases hσ : σ = 1
    · exact ⟨0, fun h => (h hσ).elim⟩
    · obtain ⟨n, hn⟩ := span_eq_maximalIdeal_pow (hne σ hσ)
      exact ⟨n, fun _ => hn⟩
  choose n hn using hn
  have hmem : ∀ σ, σ ≠ 1 → ∀ k, (σ x - x ∈ maximalIdeal B ^ k ↔ k ≤ n σ) := by
    intro σ hσ k
    rw [← Submodule.neg_mem_iff, neg_sub, ← Ideal.span_singleton_le_iff_mem, hn σ hσ,
      maximalIdeal_pow_le_iff]
  have hH : ∀ i σ, σ ≠ 1 → (σ ∈ lowerRam A B i ↔ i < n σ) := by
    intro i σ hσ
    rw [lowerRam, mem_inertia_iff_of_adjoin hx, hmem σ hσ]
    omega
  set N := ∑ σ ∈ Finset.univ.erase (1 : B ≃ₐ[A] B), n σ
  have hN : ∀ σ, σ ≠ 1 → n σ ≤ N := fun σ hσ =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hσ, Finset.mem_univ _⟩)
  refine ⟨N, ?_, ?_⟩
  · rw [eq_bot_iff]
    intro σ hσ
    rw [Subgroup.mem_bot]
    by_contra h
    have h1 := (hH N σ h).mp hσ
    have h2 := hN σ h
    omega
  · rw [sum_card_sub_one (lowerRam A B) n N hH hN, hD, ← Ideal.prod_span_singleton,
      ← Finset.prod_pow_eq_pow_sum]
    exact Finset.prod_congr rfl fun σ hσ => hn σ (Finset.ne_of_mem_erase hσ)

end Main

end TDifferent

/-! ### The leaf `PkgI6.HilbertDifferentFormula` (verbatim, Leaves.lean lines 5089-5100) and its
reduction to monogenicity. -/

namespace PkgI6

open IsLocalRing

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- Verbatim copy of `PkgI6.HilbertDifferentFormula` (Leaves.lean line 5092), with `lowerRam`
the verbatim copy `TDifferent.lowerRam`. -/
def HilbertDifferentFormula : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    ∃ N : ℕ, TDifferent.lowerRam A B N = ⊥ ∧
      differentIdeal A B =
        maximalIdeal B ^ (∑ i ∈ Finset.range N, (Nat.card (TDifferent.lowerRam A B i) - 1))

/-- **Monogenicity (Serre, *Corps locaux*, III §6, Prop. 12; UNVERIFIED locator).** For a finite
separable extension of complete discrete valuation rings whose residue field extension is
separable (here: the residue field of `A` is perfect), `B = A[x]` for some `x ∈ B`. -/
def MonogenicDVR : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)],
    ∃ x : B, Algebra.adjoin A {x} = ⊤

/-- **T20 (local) from monogenicity.** -/
theorem hilbertDifferentFormula_of_monogenicDVR (h : MonogenicDVR) : HilbertDifferentFormula := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _
  obtain ⟨x, hx⟩ := h A B
  exact TDifferent.hilbertDifferentFormula_of_adjoin_eq_top A B hx

end PkgI6

#print axioms PkgI6.hilbertDifferentFormula_of_monogenicDVR
