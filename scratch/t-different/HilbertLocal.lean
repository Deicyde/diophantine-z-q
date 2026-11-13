import Mathlib

/-!
# t-different: Hilbert's different formula (local, T20 = PkgI6.HilbertDifferentFormula), proved

Route (Serre, *Corps locaux*, III §6 Prop. 12 and IV §1 Prop. 4): `B = A[x]` (monogenicity, proved
here by Nakayama's lemma: `TDifferent.exists_adjoin_eq_top`), so `𝔇 = (f'(x))` (Mathlib's
`conductor_mul_differentIdeal`), `f'(x) = ∏_{σ≠1} (x - σx)`, `v(x - σx) = i_G(σ)` and
`∑_{σ≠1} i_G(σ) = ∑_i (|G_i| - 1)`.

Check with `lake env lean scratch/t-different/HilbertLocal.lean`.
-/

open IsLocalRing Polynomial

namespace PkgI6

/-! ### Verbatim copy of the definitions of `PkgI6` used (Leaves.lean lines 5029-5045). -/

section Ramification

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B] [IsLocalRing B]

def lowerRam (i : ℕ) : Subgroup (B ≃ₐ[A] B) :=
  (maximalIdeal B ^ (i + 1)).toAddSubgroup.inertia (B ≃ₐ[A] B)

lemma mem_lowerRam {i : ℕ} {σ : B ≃ₐ[A] B} :
    σ ∈ lowerRam A B i ↔ ∀ b : B, σ b - b ∈ maximalIdeal B ^ (i + 1) := Iff.rfl

end Ramification

end PkgI6

namespace TDifferent

open PkgI6

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

/-- An element of `𝔪 \ 𝔪²` generates `𝔪`. -/
theorem maximalIdeal_eq_span_of_mem_of_notMem {t : B} (ht : t ∈ maximalIdeal B)
    (ht2 : t ∉ maximalIdeal B ^ 2) : maximalIdeal B = Ideal.span {t} := by
  have ht0 : t ≠ 0 := by rintro rfl; exact ht2 (Ideal.zero_mem _)
  obtain ⟨n, hn⟩ := span_eq_maximalIdeal_pow ht0
  have h1 : 1 ≤ n := by
    rw [← maximalIdeal_pow_le_iff (B := B), ← hn, pow_one, Ideal.span_singleton_le_iff_mem]; exact ht
  have h2 : ¬ 2 ≤ n := by
    rw [← maximalIdeal_pow_le_iff (B := B), ← hn, Ideal.span_singleton_le_iff_mem]; exact ht2
  rw [hn, show n = 1 by omega, pow_one]

end DVR

section Monogenic

variable (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [PerfectField (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

/-- **Monogenicity** (Serre, *Corps locaux*, III §6, Prop. 12; here without completeness: only
Nakayama's lemma over the local ring `A` is used). -/
theorem exists_adjoin_eq_top : ∃ x : B, Algebra.adjoin A {x} = ⊤ := by
  classical
  have hinjAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  have : Module.Finite (ResidueField A) (ResidueField B) := inferInstance
  have : Algebra.IsSeparable (ResidueField A) (ResidueField B) := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField B)
  have hαadj : Algebra.adjoin (ResidueField A) {α} = ⊤ := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
      (Algebra.IsAlgebraic.isAlgebraic α), hα, IntermediateField.top_toSubalgebra]
  have hlift : ∀ z : ResidueField B, ∃ P : A[X], aeval α P = z := by
    intro z
    have hz : z ∈ Algebra.adjoin (ResidueField A) {α} := hαadj ▸ Algebra.mem_top
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz
    obtain ⟨p, rfl⟩ := hz
    obtain ⟨P, rfl⟩ := Polynomial.map_surjective (residue A) residue_surjective p
    exact ⟨P, by rw [← ResidueField.algebraMap_eq]; exact (aeval_map_algebraMap _ _ _).symm⟩
  have hres : ∀ (P : A[X]) (y : B), residue B (aeval y P) = aeval (residue B y) P := by
    intro P y
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom A B (ResidueField B)) y P
    simpa [ResidueField.algebraMap_eq] using this.symm
  obtain ⟨g, hg⟩ := Polynomial.map_surjective (residue A) residue_surjective
    (minpoly (ResidueField A) α)
  have hgα : aeval α g = 0 := by
    rw [← minpoly.aeval (ResidueField A) α, ← hg, ← ResidueField.algebraMap_eq,
      aeval_map_algebraMap]
  have hg'α : aeval α (derivative g) ≠ 0 := by
    have := (Algebra.IsSeparable.isSeparable (ResidueField A) α).aeval_derivative_ne_zero
      (minpoly.aeval (ResidueField A) α)
    rwa [← hg, derivative_map, ← ResidueField.algebraMap_eq, aeval_map_algebraMap] at this
  obtain ⟨x, hx⟩ := residue_surjective α
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hπm : maximalIdeal B = Ideal.span {π} := hπ.maximalIdeal_eq
  have hπmem : π ∈ maximalIdeal B := hπm ▸ Ideal.mem_span_singleton_self π
  have hπ2 : π ∉ maximalIdeal B ^ 2 := by
    intro h
    have : maximalIdeal B ^ 1 ≤ maximalIdeal B ^ 2 := by
      rw [pow_one, hπm, Ideal.span_singleton_le_iff_mem, ← hπm]; exact h
    exact absurd (maximalIdeal_pow_le_iff.mp this) (by norm_num)
  -- a lift `y` of `α` with `g(y) ∈ 𝔪 \ 𝔪²`
  have key : ∃ y : B, residue B y = α ∧ aeval y g ∈ maximalIdeal B ∧
      aeval y g ∉ maximalIdeal B ^ 2 := by
    by_cases h2 : aeval x g ∈ maximalIdeal B ^ 2
    · have hy : residue B (x + π) = α := by
        rw [map_add, hx, (residue_eq_zero_iff π).mpr hπmem, add_zero]
      refine ⟨x + π, hy, (residue_eq_zero_iff _).mp (by rw [hres, hy, hgα]), ?_⟩
      intro h
      obtain ⟨k, hk⟩ := (g.map (algebraMap A B)).binomExpansion x π
      rw [eval_map_algebraMap, eval_map_algebraMap, derivative_map, eval_map_algebraMap] at hk
      have hu : IsUnit (aeval x (derivative g)) := by
        rw [← residue_ne_zero_iff_isUnit, hres, hx]; exact hg'α
      have hmem : aeval x (derivative g) * π ∈ maximalIdeal B ^ 2 := by
        have e : aeval x (derivative g) * π = aeval (x + π) g - aeval x g - k * π ^ 2 := by
          rw [hk]; ring
        rw [e]
        refine Ideal.sub_mem _ (Ideal.sub_mem _ h h2) (Ideal.mul_mem_left _ _ ?_)
        rw [hπm, Ideal.span_singleton_pow]; exact Ideal.mem_span_singleton_self _
      apply hπ2
      obtain ⟨u, hu⟩ := hu
      have : π = ↑u⁻¹ * (aeval x (derivative g) * π) := by
        rw [← hu, ← mul_assoc, Units.inv_mul, one_mul]
      rw [this]; exact Ideal.mul_mem_left _ _ hmem
    · exact ⟨x, hx, (residue_eq_zero_iff _).mp (by rw [hres, hx, hgα]), h2⟩
  obtain ⟨y, hy, hym, hym2⟩ := key
  set t := aeval y g
  have ht : maximalIdeal B = Ideal.span {t} := maximalIdeal_eq_span_of_mem_of_notMem hym hym2
  set C := Algebra.adjoin A {y}
  have hPC : ∀ P : A[X], aeval y P ∈ C := fun P => aeval_mem_adjoin_singleton A y
  have approx : ∀ j : ℕ, ∀ b : B, ∃ c ∈ C, b - c ∈ maximalIdeal B ^ j := by
    intro j
    induction j with
    | zero => intro b; exact ⟨0, C.zero_mem, by simp⟩
    | succ j ih =>
      intro b
      obtain ⟨P, hP⟩ := hlift (residue B b)
      have h1 : b - aeval y P ∈ maximalIdeal B := by
        rw [← residue_eq_zero_iff, map_sub, hres, hy, hP, sub_self]
      rw [ht, Ideal.mem_span_singleton'] at h1
      obtain ⟨b₁, hb₁⟩ := h1
      obtain ⟨c₁, hc₁, hbc⟩ := ih b₁
      refine ⟨aeval y P + t * c₁, C.add_mem (hPC P) (C.mul_mem (hPC g) hc₁), ?_⟩
      have e : b - (aeval y P + t * c₁) = t * (b₁ - c₁) := by
        rw [mul_sub, mul_comm t b₁, hb₁]; ring
      rw [e, pow_succ']
      exact Ideal.mul_mem_mul hym hbc
  have hmA : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective hinjAB]
    exact IsDiscreteValuationRing.not_a_field A
  obtain ⟨j, hj⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmA hπ
  rw [← Ideal.span_singleton_pow, ← hπm] at hj
  have hle : (⊤ : Submodule A B) ≤ Subalgebra.toSubmodule C ⊔ maximalIdeal A • ⊤ := by
    intro b _
    obtain ⟨c, hc, hbc⟩ := approx j b
    rw [Ideal.smul_top_eq_map, hj]
    exact Submodule.mem_sup.mpr ⟨c, hc, b - c, hbc, by ring⟩
  have hN := Submodule.le_of_le_smul_of_le_jacobson_bot (Module.Finite.fg_top)
    (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hle
  refine ⟨y, ?_⟩
  rw [eq_top_iff]
  intro b _
  exact hN Submodule.mem_top

end Monogenic

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

/-- Verbatim copy of `PkgI6.HilbertDifferentFormula` (Leaves.lean line 5092). -/
def HilbertDifferentFormula : Prop :=
  ∀ (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)],
    ∃ N : ℕ, lowerRam A B N = ⊥ ∧
      differentIdeal A B =
        maximalIdeal B ^ (∑ i ∈ Finset.range N, (Nat.card (lowerRam A B i) - 1))

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

/-- `MonogenicDVR` holds (`TDifferent.exists_adjoin_eq_top`; completeness is not needed). -/
theorem monogenicDVR : MonogenicDVR := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _
  exact TDifferent.exists_adjoin_eq_top A B

/-- **Hilbert's formula without completeness.** The proof of T20 uses neither
`IsAdicComplete (maximalIdeal A) A` nor any property of `B` beyond being a DVR finite over `A`
(so it applies, e.g., to the localization of `𝓞_L` at a prime of the decomposition field). -/
theorem hilbertDifferentFormula_of_dvr
    (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [PerfectField (ResidueField A)]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]
    [IsGalois (FractionRing A) (FractionRing B)] :
    ∃ N : ℕ, lowerRam A B N = ⊥ ∧
      differentIdeal A B =
        maximalIdeal B ^ (∑ i ∈ Finset.range N, (Nat.card (lowerRam A B i) - 1)) := by
  obtain ⟨x, hx⟩ := TDifferent.exists_adjoin_eq_top A B
  exact TDifferent.hilbertDifferentFormula_of_adjoin_eq_top A B hx

/-- **T20, local form (`PkgI6.HilbertDifferentFormula`, Leaves.lean line 5092): proved.** -/
theorem hilbertDifferentFormula : HilbertDifferentFormula :=
  hilbertDifferentFormula_of_monogenicDVR monogenicDVR

end PkgI6

#print axioms PkgI6.hilbertDifferentFormula
