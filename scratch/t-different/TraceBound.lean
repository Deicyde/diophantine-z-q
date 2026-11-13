import Mathlib

/-!
# t-different: Hensel roots in `B` and the trace statement `e ∈ Tr_{B/A}(B)` (development file)
-/

open IsLocalRing Polynomial

namespace TDifferent

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

attribute [local instance] FractionRing.liftAlgebra FractionRing.isScalarTower_liftAlgebra

/-- `𝔪_A B = 𝔪_B ^ e` with `e` Mathlib's `Ideal.ramificationIdx`. -/
theorem map_maximalIdeal_eq_pow (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
    [Module.IsTorsionFree A B] :
    (maximalIdeal A).map (algebraMap A B) =
      maximalIdeal B ^ Ideal.ramificationIdx (maximalIdeal B) A := by
  have hinjAB : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  have hmA : (maximalIdeal A).map (algebraMap A B) ≠ ⊥ := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective hinjAB]
    exact IsDiscreteValuationRing.not_a_field A
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨j, hj⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible hmA hπ
  rw [← Ideal.span_singleton_pow, ← hπ.maximalIdeal_eq] at hj
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B)
    (IsDiscreteValuationRing.not_a_field A)]
  rw [Ideal.ramificationIdx'_spec (n := j) (by rw [hj]) (by rw [hj, maximalIdeal_pow_le_iff]; omega)]
  exact hj


section Hensel

variable (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B]

omit [IsDiscreteValuationRing A] [IsAdicComplete (maximalIdeal A) A] [IsDomain B]
  [IsDiscreteValuationRing B] [Module.Finite A B] [Module.IsTorsionFree A B] in
lemma repr_mem_of_mem_smul_top {ι : Type*} (b : Module.Basis ι A B) (I : Ideal A) {x : B}
    (hx : x ∈ I • (⊤ : Submodule A B)) (i : ι) : b.repr x i ∈ I := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun y z hy hz => ?_)
  · rw [map_smul, Finsupp.smul_apply, smul_eq_mul]; exact I.mul_mem_right _ ha
  · rw [map_add, Finsupp.add_apply]; exact I.add_mem hy hz

/-- `B` is `𝔪_A`-adically precomplete (it is a finite free module over the complete ring `A`). -/
lemma exists_limit {f : ℕ → B}
    (hf : ∀ {m n}, m ≤ n → f m - f n ∈ (maximalIdeal A ^ m) • (⊤ : Submodule A B)) :
    ∃ L : B, ∀ n, f n - L ∈ (maximalIdeal A ^ n) • (⊤ : Submodule A B) := by
  classical
  let b := Module.Free.chooseBasis A B
  have hc : ∀ i, ∃ Li : A, ∀ n, b.repr (f n) i - Li ∈ maximalIdeal A ^ n := by
    intro i
    have hprec : IsPrecomplete (maximalIdeal A) A := inferInstance
    obtain ⟨Li, hLi⟩ := hprec.prec (f := fun n => b.repr (f n) i) (fun {m n} hmn => by
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
      have : b.repr (f m) i - b.repr (f n) i = b.repr (f m - f n) i := by simp
      rw [this]
      exact repr_mem_of_mem_smul_top A B b _ (hf hmn) i)
    refine ⟨Li, fun n => ?_⟩
    have := hLi n
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this
  choose Li hLi using hc
  refine ⟨∑ i, Li i • b i, fun n => ?_⟩
  rw [← b.sum_repr (f n), ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [← sub_smul]
  exact Submodule.smul_mem_smul (hLi i n) Submodule.mem_top

/-- **Hensel's lemma in `B`** (for a simple root modulo `𝔪_B`). -/
theorem exists_root_of_residue {g : A[X]} {x : B} (hgx : aeval x g ∈ maximalIdeal B)
    (hg'x : IsUnit (aeval x (derivative g))) :
    ∃ u : B, aeval u g = 0 ∧ u - x ∈ maximalIdeal B := by
  obtain ⟨w, hw⟩ : ∃ w, aeval x (derivative g) * w = 1 := hg'x.exists_right_inv
  have hG : ∀ (p : A[X]) (y : B), aeval y p = (p.map (algebraMap A B)).eval y :=
    fun p y => (eval_map_algebraMap ..).symm
  let u : ℕ → B := fun m => Nat.rec x (fun _ y => y - w * aeval y g) m
  have hu0 : u 0 = x := rfl
  have hu_succ : ∀ m, u (m + 1) = u m - w * aeval (u m) g := fun m => rfl
  have key : ∀ m, u m - x ∈ maximalIdeal B ∧ aeval (u m) g ∈ maximalIdeal B ^ (m + 1) := by
    intro m
    induction m with
    | zero => rw [hu0, sub_self, zero_add, pow_one]; exact ⟨Ideal.zero_mem _, hgx⟩
    | succ m ih =>
      obtain ⟨h1, h2⟩ := ih
      have hδ : w * aeval (u m) g ∈ maximalIdeal B ^ (m + 1) := Ideal.mul_mem_left _ _ h2
      constructor
      · rw [hu_succ, sub_right_comm]
        exact Ideal.sub_mem _ h1 (Ideal.pow_le_self (by omega) hδ)
      · obtain ⟨k, hk⟩ := (g.map (algebraMap A B)).binomExpansion (u m) (-(w * aeval (u m) g))
        rw [hu_succ, sub_eq_add_neg, hG, hk, derivative_map, ← hG, ← hG]
        have hd : aeval x (derivative g) - aeval (u m) (derivative g) ∈ maximalIdeal B := by
          obtain ⟨c, hc⟩ := sub_dvd_eval_sub x (u m) ((derivative g).map (algebraMap A B))
          rw [hG, hG, hc]
          exact Ideal.mul_mem_right _ _ (by rw [← neg_sub]; exact neg_mem h1)
        have e : aeval (u m) g + aeval (u m) (derivative g) * -(w * aeval (u m) g) +
            k * (-(w * aeval (u m) g)) ^ 2 =
            aeval (u m) g * ((aeval x (derivative g) - aeval (u m) (derivative g)) * w) +
              k * w ^ 2 * (aeval (u m) g) ^ 2 := by
          linear_combination (-(aeval (u m) g)) * hw
        rw [e]
        refine Ideal.add_mem _ ?_ ?_
        · rw [pow_succ]
          exact Ideal.mul_mem_mul h2 (Ideal.mul_mem_right _ _ hd)
        · apply Ideal.mul_mem_left
          have : (aeval (u m) g) ^ 2 ∈ (maximalIdeal B ^ (m + 1)) ^ 2 := Ideal.pow_mem_pow h2 2
          rw [← pow_mul] at this
          exact Ideal.pow_le_pow_right (by omega) this
  have tele : ∀ a b, a ≤ b → u a - u b ∈ maximalIdeal B ^ (a + 1) := by
    intro a b hab
    induction b, hab using Nat.le_induction with
    | base => rw [sub_self]; exact Ideal.zero_mem _
    | succ b hab ih =>
      have : u a - u (b + 1) = (u a - u b) + w * aeval (u b) g := by rw [hu_succ]; ring
      rw [this]
      exact Ideal.add_mem _ ih
        (Ideal.pow_le_pow_right (by omega) (Ideal.mul_mem_left _ _ (key b).2))
  -- the `𝔪_A`-adic topology on `B` is the `𝔪_B`-adic one
  set e := Ideal.ramificationIdx (maximalIdeal B) A
  have hmap : _ = maximalIdeal B ^ e := map_maximalIdeal_eq_pow A B
  have : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  have he1 : 1 ≤ e := by
    by_contra h0
    have h0 : e = 0 := by omega
    have hle : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B := by
      exact Ideal.map_le_iff_le_comap.mpr
        (Ideal.LiesOver.over (P := maximalIdeal B) (p := maximalIdeal A)).le
    rw [hmap, h0, pow_zero, Ideal.one_eq_top, top_le_iff] at hle
    exact (maximalIdeal.isMaximal B).ne_top hle
  have hsmul : ∀ m, (maximalIdeal A ^ m) • (⊤ : Submodule A B) =
      (maximalIdeal B ^ (e * m)).restrictScalars A := by
    intro m
    rw [Ideal.smul_top_eq_map, Ideal.map_pow, hmap, pow_mul]
  obtain ⟨L, hL⟩ := exists_limit A B (f := fun m => u (e * m)) (fun {m n} hmn => by
    rw [hsmul]
    exact Ideal.pow_le_pow_right (by omega)
      (tele _ _ (Nat.mul_le_mul_left e hmn)))
  have hL' : ∀ n, u (e * n) - L ∈ maximalIdeal B ^ (e * n) := fun n => by
    have := hL n; rwa [hsmul] at this
  refine ⟨L, ?_, ?_⟩
  · have hmem : ∀ n, aeval L g ∈ maximalIdeal B ^ n := by
      intro n
      have h1 : aeval (u (e * n)) g ∈ maximalIdeal B ^ (e * n) :=
        Ideal.pow_le_pow_right (by omega) (key _).2
      obtain ⟨c, hc⟩ := sub_dvd_eval_sub (u (e * n)) L (g.map (algebraMap A B))
      rw [← hG, ← hG] at hc
      have h2 : aeval L g = aeval (u (e * n)) g - (u (e * n) - L) * c := by rw [← hc]; ring
      rw [h2]
      refine Ideal.pow_le_pow_right (show n ≤ e * n by nlinarith) ?_
      exact Ideal.sub_mem _ h1 (Ideal.mul_mem_right _ _ (hL' n))
    by_contra hne
    obtain ⟨N, hN⟩ := span_eq_maximalIdeal_pow hne
    have : maximalIdeal B ^ N ≤ maximalIdeal B ^ (N + 1) := by
      rw [← hN, Ideal.span_singleton_le_iff_mem]; exact hmem _
    rw [maximalIdeal_pow_le_iff] at this
    omega
  · have h1 : u (e * 1) - L ∈ maximalIdeal B := Ideal.pow_le_self (by omega) (hL' 1)
    have h2 := (key (e * 1)).1
    have : L - x = (u (e * 1) - x) - (u (e * 1) - L) := by ring
    rw [this]
    exact Ideal.sub_mem _ h2 h1

end Hensel

section Trace

variable (A B : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
  [IsAdicComplete (maximalIdeal A) A] [PerfectField (ResidueField A)]
  [CommRing B] [IsDomain B] [IsDiscreteValuationRing B] [Algebra A B] [Module.Finite A B]
  [Module.IsTorsionFree A B] [Algebra.IsSeparable (FractionRing A) (FractionRing B)]

set_option linter.deprecated false in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
/-- **`e ∈ Tr_{B/A}(B)`.** With `u ∈ B` a Hensel root of a monic lift `g` of the minimal polynomial
of a generator of `k_B/k_A`, and `E = K(u)` (so `[E : K] = f`, `[L : E] = e`), the element
`z = u^{f-1} / g'(u) ∈ B` has `Tr_{E/K}(z) = 1` (Euler; Mathlib's `traceDual_powerBasis_eq`), hence
`Tr_{L/K}(z) = Tr_{E/K}(e z) = e`. -/
theorem exists_intTrace_eq_ramificationIdx :
    ∃ z : B, Algebra.intTrace A B z = ((Ideal.ramificationIdx (maximalIdeal B) A : ℕ) : A) := by
  classical
  set e := Ideal.ramificationIdx (maximalIdeal B) A
  set K := FractionRing A
  set L := FractionRing B
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) L :=
    IsIntegralClosure.isLocalization _ K _ _
  have : FiniteDimensional K L := .of_isLocalization A B (nonZeroDivisors A)
  have : Algebra.IsIntegral A B := Algebra.IsIntegral.of_finite A B
  have : IsLocalHom (algebraMap A B) := Algebra.IsIntegral.isLocalHom A B
  have : Module.Finite (ResidueField A) (ResidueField B) := inferInstance
  have : Algebra.IsSeparable (ResidueField A) (ResidueField B) := inferInstance
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (ResidueField A) (ResidueField B)
  have hαint : IsIntegral (ResidueField A) α := Algebra.IsIntegral.isIntegral α
  have hres : ∀ (P : A[X]) (y : B), residue B (aeval y P) = aeval (residue B y) P := by
    intro P y
    have := Polynomial.aeval_algHom_apply (IsScalarTower.toAlgHom A B (ResidueField B)) y P
    simpa [ResidueField.algebraMap_eq] using this.symm
  set f := (minpoly (ResidueField A) α).natDegree with hf_def
  have hf : Module.finrank (ResidueField A) (ResidueField B) = f := by
    rw [hf_def, ← IntermediateField.adjoin.finrank hαint, hα, IntermediateField.finrank_top']
  have hf0 : 0 < f := minpoly.natDegree_pos hαint
  obtain ⟨g, hgmap, hgdeg, hgmon⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
    ((Polynomial.mem_lifts _).mpr
      (Polynomial.map_surjective (residue A) residue_surjective (minpoly (ResidueField A) α)))
    (minpoly.monic hαint)
  have hgα : aeval α g = 0 := by
    rw [← minpoly.aeval (ResidueField A) α, ← hgmap, ← ResidueField.algebraMap_eq,
      aeval_map_algebraMap]
  have hg'α : aeval α (derivative g) ≠ 0 := by
    have := (Algebra.IsSeparable.isSeparable (ResidueField A) α).aeval_derivative_ne_zero
      (minpoly.aeval (ResidueField A) α)
    rwa [← hgmap, derivative_map, ← ResidueField.algebraMap_eq, aeval_map_algebraMap] at this
  obtain ⟨x, hx⟩ := residue_surjective α
  have hgx : aeval x g ∈ maximalIdeal B := (residue_eq_zero_iff _).mp (by rw [hres, hx, hgα])
  have hg'x : IsUnit (aeval x (derivative g)) := by
    rw [← residue_ne_zero_iff_isUnit, hres, hx]; exact hg'α
  obtain ⟨u, hu, hux⟩ := exists_root_of_residue A B hgx hg'x
  have hures : residue B u = α := by
    rw [← sub_add_cancel u x, map_add, (residue_eq_zero_iff _).mpr hux, zero_add, hx]
  have hg'u : IsUnit (aeval u (derivative g)) := by
    rw [← residue_ne_zero_iff_isUnit, hres, hures]; exact hg'α
  obtain ⟨w, hw⟩ := hg'u.exists_right_inv
  have hAu : IsIntegral A u := Algebra.IsIntegral.isIntegral u
  have hmin : minpoly A u = g := by
    have hdvd : minpoly A u ∣ g := minpoly.isIntegrallyClosed_dvd hAu hu
    refine (eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hAu) hgmon hdvd ?_).symm
    rw [hgdeg]
    have h1 : minpoly (ResidueField A) α ∣ (minpoly A u).map (residue A) := by
      apply minpoly.dvd
      rw [← ResidueField.algebraMap_eq, aeval_map_algebraMap, ← hures, ← hres, minpoly.aeval,
        map_zero]
    calc _
        ≤ ((minpoly A u).map (residue A)).natDegree :=
          natDegree_le_of_dvd h1 ((minpoly.monic hAu).map _).ne_zero
      _ = (minpoly A u).natDegree := (minpoly.monic hAu).natDegree_map _
  -- the field `E = K(u)`
  set u' := algebraMap B L u
  have hKu : IsIntegral K u' := Algebra.IsIntegral.isIntegral _
  have hminK : minpoly K u' = g.map (algebraMap A K) := by
    rw [minpoly.isIntegrallyClosed_eq_field_fractions K L hAu, hmin]
  have hfE : Module.finrank K (IntermediateField.adjoin K {u'}) = f := by
    rw [IntermediateField.adjoin.finrank hKu, hminK, hgmon.natDegree_map, hgdeg]
  -- the fundamental identity `e f = [L : K]`
  have hfund : e * f = Module.finrank K L := by
    have := Ideal.ramificationIdx_mul_inertiaDeg_of_isLocalRing (R := A) (S := B) K L
      (p := maximalIdeal A) (IsDiscreteValuationRing.not_a_field A)
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (maximalIdeal A) (maximalIdeal B)
      (IsDiscreteValuationRing.not_a_field A), Ideal.inertiaDeg'_algebraMap] at this
    rw [← this, ← hf]
    rfl
  have hEL : Module.finrank (IntermediateField.adjoin K {u'}) L = e := by
    have h := Module.finrank_mul_finrank K (IntermediateField.adjoin K {u'}) L
    rw [hfE, ← hfund] at h
    exact Nat.eq_of_mul_eq_mul_left hf0 (h.trans (mul_comm _ _))
  -- Euler: `Tr_{E/K}(u^{f-1} / g'(u)) = 1`
  let pb := IntermediateField.adjoin.powerBasis hKu
  have hdim : pb.dim = f := by
    rw [IntermediateField.adjoin.powerBasis_dim, hminK, hgmon.natDegree_map, hgdeg]
  let i : Fin pb.dim := ⟨f - 1, by omega⟩
  have hgen : pb.gen = IntermediateField.AdjoinSimple.gen K u' := rfl
  have h1 := Module.Basis.trace_traceDual_mul pb.basis i i
  rw [if_pos rfl, Module.Basis.traceDual_powerBasis_eq, PowerBasis.coe_basis] at h1
  have hcoeff : (minpolyDiv K pb.gen).coeff (f - 1) = 1 := by
    have hnd : (minpolyDiv K pb.gen).natDegree = f - 1 := by
      rw [natDegree_minpolyDiv, hgen, IntermediateField.minpoly_gen, hminK,
        hgmon.natDegree_map, hgdeg]
    rw [← hnd]
    exact minpolyDiv_monic (IntermediateField.adjoin.powerBasis hKu).isIntegral_gen
  simp only [i, hcoeff] at h1
  -- transport to `L`
  set cE : IntermediateField.adjoin K {u'} :=
    1 / aeval pb.gen (derivative (minpoly K pb.gen)) * pb.gen ^ (f - 1) with hcE
  have hcEL : algebraMap (IntermediateField.adjoin K {u'}) L cE = algebraMap B L (w * u ^ (f - 1)) := by
    have hw' : algebraMap B L w = (algebraMap B L (aeval u (derivative g)))⁻¹ :=
      eq_inv_of_mul_eq_one_right (by rw [← map_mul, hw, map_one])
    rw [hcE, map_mul, map_div₀, map_one, map_pow, ← aeval_algebraMap_apply, hgen,
      IntermediateField.AdjoinSimple.algebraMap_gen, IntermediateField.minpoly_gen, hminK,
      derivative_map, aeval_map_algebraMap, map_mul, map_pow, hw', aeval_algebraMap_apply,
      one_div]
  refine ⟨w * u ^ (f - 1), ?_⟩
  apply IsFractionRing.injective A K
  rw [Algebra.algebraMap_intTrace_fractionRing, ← hcEL, ← Algebra.trace_trace (S := IntermediateField.adjoin K {u'}),
    Algebra.trace_algebraMap, hEL, map_nsmul, h1, map_natCast, nsmul_eq_mul, mul_one]

end Trace

end TDifferent

#print axioms TDifferent.exists_intTrace_eq_ramificationIdx
