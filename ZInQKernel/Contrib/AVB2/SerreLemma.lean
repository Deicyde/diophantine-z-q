import Mathlib

/-!
# Serre's lemma at level 3, ring and lattice forms (task av-b2)

Copyright: this file is part of the fork Deicyde/diophantine-z-q (task av-b2, 2026-11-13).

* `eq_one_of_pow_eq_one`: in a ring `R` without `3`-torsion that is `3`-adically separated, an element
  `x ≡ 1 (mod 3)` of finite multiplicative order is `1` (Minkowski / Serre; the elementary proof:
  reduce to prime order `p`, then `x = 1 + 3^k c` forces `3 ∣ c`).
* `eq_zero_of_smul_mem`: in a discrete subgroup `Λ ⊆ ℂ^g`, if `3^{-k} w ∈ Λ` for all `k` then `w = 0`.
* `lattice_serre`: a `ℂ`-linear `M : ℂ^g → ℂ^g` preserving a full discrete lattice `Λ`, congruent to `1`
  modulo `3Λ`, with `M^m − 1` mapping `ℂ^g` into `Λ`, is the identity.

These are the algebraic half of Serre's lemma (J.-P. Serre, *Rigidité du foncteur de Jacobi d'échelon
n ≥ 3*, Sém. Cartan 13 (1960/61), exp. 17, appendix; locator UNVERIFIED). Only Mathlib is used.
-/

namespace ZInQ.Contrib.AVB2

open Finset

/-- `3`-torsion-freeness iterated. -/
theorem eq_zero_of_three_pow_mul {A : Type*} [Ring A] (htf : ∀ r : A, 3 * r = 0 → r = 0) :
    ∀ (k : ℕ) (r : A), 3 ^ k * r = 0 → r = 0 := by
  intro k
  induction k with
  | zero => intro r h; simpa using h
  | succ k ih =>
    intro r h
    exact htf r (ih (3 * r) (by rw [← mul_assoc, ← pow_succ]; exact h))

/-- **Key step (commutative).** If `(1 + 3^{j+1} c)^p = 1` with `p` prime in a commutative ring
without `3`-torsion, then `3 ∣ c`. -/
theorem key_comm {A : Type*} [CommRing A] (htf : ∀ r : A, 3 * r = 0 → r = 0)
    {p : ℕ} (hp : p.Prime) (j : ℕ) {c : A} (hx : (1 + 3 ^ (j + 1) * c) ^ p = 1) :
    ∃ d, c = 3 * d := by
  set x := 1 + 3 ^ (j + 1) * c with hxdef
  have hS : (∑ i ∈ range p, x ^ i) * (3 ^ (j + 1) * c) = 0 := by
    have h := geom_sum_mul x p
    rw [hx, sub_self] at h
    rw [← h, hxdef]
    ring
  have hSc : (∑ i ∈ range p, x ^ i) * c = 0 :=
    eq_zero_of_three_pow_mul htf (j + 1) _ (by rw [← hS]; ring)
  by_cases hp3 : p = 3
  · subst hp3
    have h3 : 3 * (c + 3 ^ (j + 1) * c ^ 2 + 3 ^ (2 * j + 1) * c ^ 3) = 0 := by
      have e := hSc
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, hxdef] at e
      linear_combination e
    refine ⟨-(3 ^ j * c ^ 2 + 3 ^ (2 * j) * c ^ 3), ?_⟩
    have := htf _ h3
    linear_combination this
  · let I : Ideal A := Ideal.span {3}
    have hx1 : x - 1 ∈ I := Ideal.mem_span_singleton'.2 ⟨3 ^ j * c, by rw [hxdef]; ring⟩
    have hmk : Ideal.Quotient.mk I x = 1 := by
      rw [← sub_eq_zero, ← map_one (Ideal.Quotient.mk I), ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      exact hx1
    have hpc : (p : A) * c ∈ I := by
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_mul, map_natCast]
      have := congrArg (Ideal.Quotient.mk I) hSc
      rw [map_mul, map_sum, map_zero] at this
      simpa [map_pow, hmk] using this
    have hcop : IsCoprime (p : ℤ) ((3 : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact (Nat.coprime_primes hp Nat.prime_three).2 hp3
    obtain ⟨a, b, hab⟩ := hcop
    have hcI : c ∈ I := by
      have hc : c = (a : A) * ((p : A) * c) + ((b : A) * c) * 3 := by
        have := congrArg (fun t : ℤ => (t : A) * c) hab
        push_cast at this
        linear_combination -this
      rw [hc]
      exact I.add_mem (I.mul_mem_left _ hpc) (Ideal.mem_span_singleton'.2 ⟨_, rfl⟩)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hcI
    exact ⟨d, by rw [← hd, mul_comm]⟩

/-- **Serre's lemma, ring form.** `R` a ring without `3`-torsion and `3`-adically separated;
`x = 1 + 3y` with `x^m = 1`, `m > 0`. Then `x = 1`. -/
theorem eq_one_of_pow_eq_one {R : Type*} [Ring R] (htf : ∀ r : R, 3 * r = 0 → r = 0)
    (hsep : ∀ r : R, (∀ k : ℕ, ∃ s, r = 3 ^ k * s) → r = 0)
    {x y : R} (hxy : x = 1 + 3 * y) {m : ℕ} (hm : 0 < m) (hxm : x ^ m = 1) : x = 1 := by
  -- powers of `x` stay `≡ 1 (mod 3)`
  have hcl : ∀ i : ℕ, ∃ t : R, x ^ i = 1 + 3 * t := by
    intro i
    induction i with
    | zero => exact ⟨0, by simp⟩
    | succ i ih =>
      obtain ⟨t, ht⟩ := ih
      refine ⟨t + y + 3 * t * y, ?_⟩
      rw [pow_succ, ht, hxy]
      have h3 : t * 3 = 3 * t := ((Commute.ofNat_left 3 t).eq).symm
      calc (1 + 3 * t) * (1 + 3 * y) = 1 + 3 * t + 3 * y + 3 * (t * 3) * y := by noncomm_ring
        _ = 1 + 3 * (t + y + 3 * t * y) := by rw [h3]; noncomm_ring
  by_contra hne
  have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.2 ⟨m, hm, hxm⟩
  set o := orderOf x with ho
  have ho0 : o ≠ 0 := hfin.orderOf_pos.ne'
  have ho1 : o ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
  set p := o.minFac with hpdef
  have hp : p.Prime := Nat.minFac_prime ho1
  have hpo : p ∣ o := Nat.minFac_dvd o
  set x' := x ^ (o / p) with hx'
  have hord : orderOf x' = p := orderOf_pow_orderOf_div ho0 hpo
  have hx'p : x' ^ p = 1 := by rw [← hord]; exact pow_orderOf_eq_one x'
  have hx'1 : x' ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hord
    exact hp.one_lt.ne hord
  -- `x' ≡ 1 (mod 3^k)` for every `k`
  have hall : ∀ j : ℕ, ∃ c : R, x' = 1 + 3 ^ (j + 1) * c := by
    intro j
    induction j with
    | zero =>
      obtain ⟨t, ht⟩ := hcl (o / p)
      exact ⟨t, by rw [hx', ht, zero_add, pow_one]⟩
    | succ j ih =>
      obtain ⟨c, hc⟩ := ih
      let B := Algebra.adjoin ℤ ({c} : Set R)
      let c' : B := ⟨c, Algebra.self_mem_adjoin_singleton ℤ c⟩
      have hval : ∀ b : B, (B.val b : R) = b := fun _ => rfl
      have hB : (1 + 3 ^ (j + 1) * c' : B) ^ p = 1 := by
        apply Subtype.val_injective
        have := hx'p
        rw [hc] at this
        change B.val ((1 + 3 ^ (j + 1) * c') ^ p) = B.val 1
        rw [map_pow, map_add, map_mul, map_pow, map_one, map_ofNat]
        exact this
      have htfB : ∀ r : B, 3 * r = 0 → r = 0 := by
        intro r hr
        apply Subtype.val_injective
        have := congrArg B.val hr
        rw [map_mul, map_ofNat, map_zero] at this
        exact htf _ this
      obtain ⟨d, hd⟩ := key_comm htfB hp j hB
      refine ⟨(d : R), ?_⟩
      have hcd : c = 3 * (d : R) := by
        have := congrArg B.val hd
        rw [map_mul, map_ofNat] at this
        exact this
      rw [hc, hcd, ← mul_assoc, ← pow_succ]
  have h0 : x' - 1 = 0 := hsep _ (fun k => by
    cases k with
    | zero => exact ⟨x' - 1, by simp⟩
    | succ j =>
      obtain ⟨c, hc⟩ := hall j
      exact ⟨c, by rw [hc]; noncomm_ring⟩)
  exact hx'1 (sub_eq_zero.1 h0)

/-- In a discrete subgroup `Λ` of `ℂ^g`, if `3^{-k} w ∈ Λ` for every `k` then `w = 0`. -/
theorem eq_zero_of_smul_mem {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (w : Fin g → ℂ) (hw : ∀ k : ℕ, ((3⁻¹ : ℂ) ^ k) • w ∈ Λ) : w = 0 := by
  have h0 : IsOpen ({0} : Set Λ) := isOpen_discrete _
  obtain ⟨U, hU, hpre⟩ := isOpen_induced_iff.1 h0
  have h0U : (0 : Fin g → ℂ) ∈ U := by
    have : (0 : Λ) ∈ Subtype.val ⁻¹' U := by rw [hpre]; rfl
    exact this
  have ht : Filter.Tendsto (fun k : ℕ => ((3⁻¹ : ℂ) ^ k) • w) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun k : ℕ => (3⁻¹ : ℂ) ^ k) Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_norm_lt_one (by rw [norm_inv]; norm_num)
    simpa using h1.smul_const w
  obtain ⟨k, hk⟩ := (ht.eventually (hU.mem_nhds h0U)).exists
  have hmem : (⟨_, hw k⟩ : Λ) ∈ Subtype.val ⁻¹' U := hk
  rw [hpre] at hmem
  have h1 : ((3⁻¹ : ℂ) ^ k) • w = 0 := congrArg Subtype.val hmem
  rcases smul_eq_zero.1 h1 with h | h
  · exact absurd h (pow_ne_zero _ (by norm_num))
  · exact h

/-- **Serre's lemma, lattice form.** -/
theorem lattice_serre {g : ℕ} (Λ : Submodule ℤ (Fin g → ℂ)) [DiscreteTopology Λ]
    (hΛ : IsZLattice ℝ Λ) (M : (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ)) (hMΛ : ∀ z ∈ Λ, M z ∈ Λ)
    (h3 : ∀ z ∈ Λ, (3⁻¹ : ℂ) • (M z - z) ∈ Λ) {m : ℕ} (hm : 0 < m)
    (hfin : ∀ z, (M ^ m) z - z ∈ Λ) : M = 1 := by
  have hMm : ∀ z, (M ^ m) z = z := by
    intro z
    refine sub_eq_zero.1 (eq_zero_of_smul_mem Λ ((M ^ m) z - z) (fun k => ?_))
    have h := hfin (((3⁻¹ : ℂ) ^ k) • z)
    rwa [map_smul, ← smul_sub] at h
  let x : Module.End ℤ Λ := (M.restrictScalars ℤ).restrict hMΛ
  have hy : ∀ z ∈ Λ, (((3⁻¹ : ℂ) • (M - 1)).restrictScalars ℤ) z ∈ Λ := by
    intro z hz
    simpa using h3 z hz
  let y : Module.End ℤ Λ := (((3⁻¹ : ℂ) • (M - 1)).restrictScalars ℤ).restrict hy
  have hxv : ∀ z : Λ, ((x z : Λ) : Fin g → ℂ) = M z := fun _ => rfl
  have hyv : ∀ z : Λ, ((y z : Λ) : Fin g → ℂ) = (3⁻¹ : ℂ) • (M z - z) := fun _ => by
    simp [y]
  have hxy : x = 1 + 3 * y := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    rw [LinearMap.add_apply, Module.End.one_apply, Module.End.mul_apply, Module.End.ofNat_apply,
      Submodule.coe_add, Submodule.coe_smul_of_tower, hxv, hyv, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    norm_num
  have hpow : ∀ n : ℕ, ∀ z : Λ, (((x ^ n) z : Λ) : Fin g → ℂ) = (M ^ n) z := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply, hxv]
  have hxm : x ^ m = 1 := by
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    rw [hpow, hMm, Module.End.one_apply]
  have htf : ∀ r : Module.End ℤ Λ, 3 * r = 0 → r = 0 := by
    intro r hr
    apply LinearMap.ext
    intro z
    have h := congrArg (fun f : Module.End ℤ Λ => ((f z : Λ) : Fin g → ℂ)) hr
    simp only [Module.End.mul_apply, Module.End.ofNat_apply, Submodule.coe_smul,
      LinearMap.zero_apply, Submodule.coe_zero] at h
    apply Subtype.ext
    rcases smul_eq_zero.1 h with h' | h'
    · norm_num at h'
    · simpa using h'
  have hsep : ∀ r : Module.End ℤ Λ, (∀ k : ℕ, ∃ s, r = 3 ^ k * s) → r = 0 := by
    intro r hr
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    refine eq_zero_of_smul_mem Λ _ (fun k => ?_)
    obtain ⟨s, hs⟩ := hr k
    have : ((r z : Λ) : Fin g → ℂ) = ((3 : ℂ) ^ k) • ((s z : Λ) : Fin g → ℂ) := by
      rw [hs, Module.End.mul_apply]
      have key : ∀ (j : ℕ) (v : Λ),
          (((3 ^ j : Module.End ℤ Λ) v : Λ) : Fin g → ℂ) = ((3 : ℂ) ^ j) • (v : Fin g → ℂ) := by
        intro j
        induction j with
        | zero => intro v; simp
        | succ j ih =>
          intro v
          rw [pow_succ, Module.End.mul_apply, ih, Module.End.ofNat_apply,
            Submodule.coe_smul_of_tower, ← Nat.cast_smul_eq_nsmul ℂ, pow_succ, mul_smul]
          norm_num
      exact key k _
    rw [this, smul_smul, ← mul_pow, inv_mul_cancel₀ (by norm_num), one_pow, one_smul]
    exact (s z).2
  have hx1 := eq_one_of_pow_eq_one htf hsep hxy hm hxm
  apply LinearMap.restrictScalars_injective ℝ
  apply LinearMap.ext_on hΛ.span_top
  intro z hz
  have := congrArg (fun f : Module.End ℤ Λ => ((f ⟨z, hz⟩ : Λ) : Fin g → ℂ)) hx1
  simpa [hxv] using this

end ZInQ.Contrib.AVB2
