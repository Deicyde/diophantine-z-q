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

end TDifferent

#print axioms TDifferent.exists_root_of_residue
