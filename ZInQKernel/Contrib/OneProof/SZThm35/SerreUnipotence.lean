import ZInQKernel.Contrib.CloudR2CM.SerreTate.SerreLemmaTateProof
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.BigOperators.Intervals

noncomputable section

namespace SZRaynaud

open HDec.CMSerreTate.SerreLemmaTateAux

section SerreUnipotence

variable {ℓ : ℕ} [Fact ℓ.Prime] {M : Type} [AddCommGroup M]

private theorem inPow_sum {ι : Type*} (s : Finset ι) (f : ι → PkgI3.Tate.T ℓ M) {r : ℕ}
    (h : ∀ i ∈ s, InPow r (f i)) : InPow r (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (inPow_zero (M := M) (ℓ := ℓ) r)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact inPow_add (h _ (Finset.mem_insert_self _ _))
      (ih fun j hj => h _ (Finset.mem_insert_of_mem hj))

private theorem injective_of_kernel_inPow_one (f : Module.End ℤ_[ℓ] (PkgI3.Tate.T ℓ M))
    (h : ∀ x, f x = 0 → InPow 1 x) : Function.Injective f := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  apply eq_zero_of_forall
  intro r
  induction r generalizing x with
  | zero => exact ⟨x, by simp⟩
  | succ r ih =>
    obtain ⟨y, hy⟩ := h x hx
    have hy0 : f y = 0 := by
      apply eq_zero_of_ell_smul
      rw [← pow_one (ℓ : ℤ_[ℓ]), ← map_smul, ← hy, hx]
    rw [hy, pow_one]
    exact inPow_ell_smul (ih y hy0)

variable {g : Module.End ℤ_[ℓ] (PkgI3.Tate.T ℓ M)}

/-- The geometric sum is injective if the automorphism is sufficiently close to the identity. -/
private theorem geomSum_injective {s : ℕ} (hs : 1 ≤ s) (hs₂ : 2 ≤ s ∨ 3 ≤ ℓ)
    (hg : ∀ y, InPow s (g y - y)) {q : ℕ} (hq : q.Prime) :
    Function.Injective (∑ j ∈ Finset.range q, g ^ j : Module.End ℤ_[ℓ] (PkgI3.Tate.T ℓ M)) := by
  let S := ∑ j ∈ Finset.range q, g ^ j
  apply injective_of_kernel_inPow_one S
  intro x hx
  have h₀ : InPow s (S x - (q : ℤ_[ℓ]) • x) := by
    rw [show S x - (q : ℤ_[ℓ]) • x = ∑ j ∈ Finset.range q, ((g ^ j) x - x) by
      simp only [S, LinearMap.sum_apply, Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_range, Nat.cast_smul_eq_nsmul]]
    exact inPow_sum _ _ fun j _ => order0 hg j x
  by_cases hqℓ : q = ℓ
  · obtain rfl := hqℓ
    have h₂ : InPow 2 (S x - (q : ℤ_[q]) • x) := by
      rcases hs₂ with h | h
      · exact inPow_mono h h₀
      · have hlin : InPow (s + s) (S x - (q : ℤ_[q]) • x -
            ((q.choose 2 : ℕ) : ℤ_[q]) • (g x - x)) := by
          rw [show S x - (q : ℤ_[q]) • x - ((q.choose 2 : ℕ) : ℤ_[q]) • (g x - x) =
              ∑ j ∈ Finset.range q, ((g ^ j) x - x - (j : ℤ_[q]) • (g x - x)) by
            simp only [S, LinearMap.sum_apply, Finset.sum_sub_distrib, Finset.sum_const,
              Finset.card_range, Nat.cast_smul_eq_nsmul, ← Finset.sum_smul,
              Finset.sum_range_id, Nat.choose_two_right]]
          exact inPow_sum _ _ fun j _ => order1 hg j x
        obtain ⟨b, hb⟩ := hq.dvd_choose_self (by decide : 2 ≠ 0) h
        have hC : InPow (s + 1) (((q.choose 2 : ℕ) : ℤ_[q]) • (g x - x)) := by
          rw [hb, Nat.cast_mul, mul_comm, mul_smul]
          exact inPow_smul _ (inPow_ell_smul (hg x))
        have ht := inPow_add (inPow_mono (show 2 ≤ s + s by omega) hlin)
          (inPow_mono (show 2 ≤ s + 1 by omega) hC)
        rwa [sub_add_cancel] at ht
    rw [hx, zero_sub] at h₂
    have hsmul := inPow_neg h₂
    rw [neg_neg] at hsmul
    exact inPow_of_ell_smul hsmul
  · rw [hx, zero_sub] at h₀
    have hsmul := inPow_neg (inPow_mono hs h₀)
    rw [neg_neg] at hsmul
    obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.mpr
      ((Nat.coprime_primes hq (Fact.out : ℓ.Prime)).mpr hqℓ)
    have hab' : (a : ℤ_[ℓ]) * (q : ℤ_[ℓ]) + (b : ℤ_[ℓ]) * (ℓ : ℤ_[ℓ]) = 1 := by
      exact_mod_cast hab
    have hcomb : x = (a : ℤ_[ℓ]) • ((q : ℤ_[ℓ]) • x) +
        (b : ℤ_[ℓ]) • ((ℓ : ℤ_[ℓ]) • x) := by
      rw [smul_smul, smul_smul, ← add_smul, hab', one_smul]
    rw [hcomb]
    exact inPow_add (inPow_smul _ hsmul) (inPow_smul _ ⟨x, by rw [pow_one]⟩)

private theorem sub_sq_eq_zero_of_prime_pow {s : ℕ} (hs : 1 ≤ s)
    (hs₂ : 2 ≤ s ∨ 3 ≤ ℓ) (hg : ∀ y, InPow s (g y - y))
    {q : ℕ} (hq : q.Prime) (hpow : (g ^ q - 1) ^ 2 = 0) :
    (g - 1) ^ 2 = 0 := by
  let S := ∑ j ∈ Finset.range q, g ^ j
  have hS : Function.Injective S := geomSum_injective hs hs₂ hg hq
  have hSD : S * (g - 1) = g ^ q - 1 := geom_sum_mul g q
  have hDS : (g - 1) * S = g ^ q - 1 := mul_geom_sum g q
  have hc : Commute S (g - 1) := hSD.trans hDS.symm
  rw [← hSD, hc.mul_pow] at hpow
  apply LinearMap.ext
  intro x
  apply hS
  apply hS
  simpa only [pow_two, Module.End.mul_apply, LinearMap.zero_apply, map_zero] using
    DFunLike.congr_fun hpow x

/-- A Tate automorphism congruent to the identity at level ℓ^k, for ℓ^k ≥ 3,
has square-zero displacement whenever a positive power does. -/
theorem sub_sq_eq_zero_of_quasiUnipotent {k : ℕ} (hk : 3 ≤ ℓ ^ k)
    (hg : ∀ y, InPow k (g y - y)) {n : ℕ} (hn : 0 < n) (hpow : (g ^ n - 1) ^ 2 = 0) :
    (g - 1) ^ 2 = 0 := by
  have hk₁ : 1 ≤ k := by
    by_contra! h
    have : k = 0 := by omega
    simp [this] at hk
  have hk₂ : 2 ≤ k ∨ 3 ≤ ℓ := by
    by_cases h : 2 ≤ k
    · exact Or.inl h
    · have : k = 1 := by omega
      exact Or.inr (by simpa only [this, pow_one] using hk)
  induction n using Nat.strong_induction_on generalizing g with
  | _ n ih =>
    by_cases h₁ : n = 1
    · simpa only [h₁, pow_one] using hpow
    · obtain ⟨q, hq, m, rfl⟩ := Nat.exists_prime_and_dvd h₁
      have hm : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
      have hmq : ((g ^ m) ^ q - 1) ^ 2 = 0 := by rw [← pow_mul, mul_comm m q]; exact hpow
      have hgm : ((g ^ m) - 1) ^ 2 = 0 :=
        sub_sq_eq_zero_of_prime_pow hk₁ hk₂ (order0 hg m) hq hmq
      exact ih m (lt_of_lt_of_le (by omega : m < 2 * m)
        (Nat.mul_le_mul hq.two_le le_rfl)) hg hm hgm

end SerreUnipotence
end SZRaynaud

#print axioms SZRaynaud.sub_sq_eq_zero_of_quasiUnipotent
