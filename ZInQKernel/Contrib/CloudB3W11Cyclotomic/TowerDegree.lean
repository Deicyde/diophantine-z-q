import ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDefinition
import ZInQKernel.Contrib.TauCeti.NumberTheory.Cyclotomic.Irreducible

/-!
# Degrees in the `p`-power cyclotomic tower, and the degree-`p` step

Task cloud-b3/w11 (author D, 2026-11-16). Continues
`ZInQKernel.Contrib.CloudB3W11Cyclotomic.TowerDefinition`.

* `PadicAlgCl.finrank_cyclotomicTower`: `[ℚ_p(μ_{p^n}) : ℚ_p] = (p − 1) p^{n−1}` for `n > 0`.
  The degree grows without bound; this is what makes the image of the cyclotomic character on
  `Gal(ℚ̄_p/K)` infinite for every finite `K/ℚ_p`.
* `PadicAlgCl.pow_mem_and_not_mem_fixingSubgroup`: an automorphism fixing `ℚ_p(μ_{p^{m+2}})`
  but not `ℚ_p(μ_{p^{m+3}})` has `σ^p` fixing `ℚ_p(μ_{p^{m+3}})` but not `ℚ_p(μ_{p^{m+4}})`.
  This is the `hcyc` hypothesis of the normalised-trace construction.
* `PadicAlgCl.finrank_cyclotomicTower_and_pow_mem_fixingSubgroup`: the two packaged as one
  conjunction.

The irreducibility of `Φ_{p^n}` over `ℚ_p` is this repository's already vendored Tau Ceti
theorem `TauCeti.irreducible_cyclotomic_prime_pow_ratPadic`
(`ZInQKernel/Contrib/TauCeti/NumberTheory/Cyclotomic/Irreducible.lean`, Apache-2.0, Tau Ceti
commit `5a01f5fe3621`; Eisenstein at `p` after `X ↦ X + 1`, Serre, *Local Fields*, IV §4), so
the Eisenstein derivation of the public source is not repeated.

## Provenance

The statements and the structure of the proofs are ported from
[anthropics/fermats-last-theorem](https://github.com/anthropics/fermats-last-theorem), commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`, files
`Theorems/Thm_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup.lean` and
`P2M/Sol/S_PadicAlgCl_finrank_cyclotomicTower_and_pow_mem_fixingSubgroup.lean` (Copyright 2026
Anthropic, PBC; Apache License, Version 2.0 — the licence text as already carried by this
repository is at `ZInQKernel/Contrib/CloudB2X0Transitive/Vendor/AnthropicFLT/LICENSE`). The
upstream theorem names are kept. Changes: as recorded in `TowerDefinition.lean`, plus the
replacement of the upstream private lemmas `isEisensteinAt_padicInt` and
`irreducible_cyclotomic` by the Tau Ceti theorem named above.
-/

set_option linter.style.longLine false
set_option linter.style.haveILetI false

namespace PadicAlgCl

open Polynomial IntermediateField

noncomputable section

variable (p : ℕ) [Fact p.Prime]

/-- The arithmetic step behind the degree-`p` step of the tower: raising to the `p`-th power
moves the exact `p`-adic valuation of `a − 1` up by exactly one, once that valuation is `≥ 2`. -/
theorem pow_p_sub_one_of_dvd {a k : ℕ} (hk : 2 ≤ k) (ha : 1 ≤ a) (h1 : p ^ k ∣ a - 1)
    (h2 : ¬ p ^ (k + 1) ∣ a - 1) : p ^ (k + 1) ∣ a ^ p - 1 ∧ ¬ p ^ (k + 2) ∣ a ^ p - 1 := by
  have hp : p.Prime := Fact.out
  obtain ⟨u, hu⟩ := h1
  have hpu : ¬ p ∣ u := by
    rintro ⟨v, rfl⟩
    exact h2 ⟨v, by rw [hu]; ring⟩
  have ha' : a = p ^ k * u + 1 := by omega
  have hexp : a ^ p = ∑ i ∈ Finset.range (p + 1), (p ^ k * u) ^ i * p.choose i := by
    rw [ha', add_pow]
    simp
  have hp1 : p + 1 = (p - 1) + 1 + 1 := by have := hp.one_lt; omega
  have hsplit : ∑ i ∈ Finset.range (p + 1), (p ^ k * u) ^ i * p.choose i =
      1 + p ^ k * u * p +
        ∑ i ∈ Finset.range (p - 1), (p ^ k * u) ^ (i + 2) * p.choose (i + 2) := by
    rw [hp1, Finset.sum_range_succ', Finset.sum_range_succ']
    simp only [pow_zero, Nat.choose_zero_right, mul_one, zero_add, pow_one, Nat.choose_one_right]
    ring
  have htail : p ^ (k + 2) ∣
      ∑ i ∈ Finset.range (p - 1), (p ^ k * u) ^ (i + 2) * p.choose (i + 2) := by
    refine Finset.dvd_sum fun i _ => Dvd.dvd.mul_right ?_ _
    rw [mul_pow, ← pow_mul]
    exact Dvd.dvd.mul_right (pow_dvd_pow p (by nlinarith)) _
  obtain ⟨M, hM⟩ := htail
  have hkey : a ^ p - 1 = p ^ (k + 1) * u + p ^ (k + 2) * M := by
    rw [hexp, hsplit, hM]
    have hre : p ^ k * u * p = p ^ (k + 1) * u := by ring
    rw [hre]
    omega
  refine ⟨?_, ?_⟩
  · rw [hkey]
    exact dvd_add (dvd_mul_right _ _) (Dvd.dvd.mul_right (pow_dvd_pow p (by omega)) _)
  · rw [hkey]
    intro hdvd
    have h3 : p ^ (k + 2) ∣ p ^ (k + 1) * u :=
      (Nat.dvd_add_left (dvd_mul_right (p ^ (k + 2)) M)).mp hdvd
    rw [pow_succ] at h3
    exact hpu (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos _) h3)

/-- **The step of the cyclotomic tower is of degree exactly `p`**, in the form the normalised
trace estimate consumes: an automorphism fixing `ℚ_p(μ_{p^{m+2}})` but not `ℚ_p(μ_{p^{m+3}})`
has `σ^p` fixing `ℚ_p(μ_{p^{m+3}})` but not `ℚ_p(μ_{p^{m+4}})`. -/
theorem pow_mem_and_not_mem_fixingSubgroup (m : ℕ)
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p)
    (hσ : σ ∈ (cyclotomicTower p (m + 2)).fixingSubgroup)
    (hσ' : σ ∉ (cyclotomicTower p (m + 3)).fixingSubgroup) :
    σ ^ p ∈ (cyclotomicTower p (m + 3)).fixingSubgroup ∧
      σ ^ p ∉ (cyclotomicTower p (m + 4)).fixingSubgroup := by
  have hp : p.Prime := Fact.out
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_pow p (m + 4)
  haveI : NeZero (p ^ (m + 4)) := ⟨pow_ne_zero (m + 4) hp.ne_zero⟩
  obtain ⟨a, -, ha⟩ :=
    hζ.eq_pow_of_pow_eq_one (ξ := σ ζ) (by rw [← map_pow, hζ.pow_eq_one, map_one])
  have ha' : σ ζ = ζ ^ a := ha.symm
  have ha1 : 1 ≤ a := by
    by_contra h0
    have ha0 : a = 0 := by omega
    subst ha0
    rw [pow_zero] at ha'
    have h1 : ζ = 1 := by
      have hcong := congrArg σ.symm ha'
      simpa using hcong
    have hone : (p ^ (m + 4) : ℕ) = 1 := by
      have heq := hζ.eq_orderOf
      rw [h1, orderOf_one] at heq
      exact heq
    have : 1 < p ^ (m + 4) := Nat.one_lt_pow (by omega) hp.one_lt
    omega
  have hσp : (σ ^ p) ζ = ζ ^ a ^ p := pow_apply_eq_pow_pow p σ ha' p
  have hap1 : 1 ≤ a ^ p := Nat.one_le_pow _ _ ha1
  rw [mem_fixingSubgroup_cyclotomicTower_iff_dvd p (by omega) hζ σ ha1 ha'] at hσ hσ'
  rw [mem_fixingSubgroup_cyclotomicTower_iff_dvd p (by omega) hζ (σ ^ p) hap1 hσp,
    mem_fixingSubgroup_cyclotomicTower_iff_dvd p (le_refl (m + 4)) hζ (σ ^ p) hap1 hσp]
  exact pow_p_sub_one_of_dvd p (by omega) ha1 hσ hσ'

/-- **`[ℚ_p(μ_{p^n}) : ℚ_p] = (p − 1) p^{n−1}`** for `n > 0`. -/
theorem finrank_cyclotomicTower (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ_[p] (cyclotomicTower p n) = (p - 1) * p ^ (n - 1) := by
  have hp : p.Prime := Fact.out
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_pow p (k + 1)
  haveI : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.ne_zero⟩
  haveI := hζ.intermediateField_adjoin_isCyclotomicExtension (K := ℚ_[p])
  rw [cyclotomicTower_eq_adjoin p (k + 1) hζ,
    IsCyclotomicExtension.finrank (IntermediateField.adjoin ℚ_[p] {ζ})
      (TauCeti.irreducible_cyclotomic_prime_pow_ratPadic p (k + 1)),
    Nat.totient_prime_pow hp (Nat.succ_pos k), mul_comm]

/-- **The degree of the tower and its degree-`p` step**, in the conjunction shape the
normalised-trace argument consumes. -/
theorem finrank_cyclotomicTower_and_pow_mem_fixingSubgroup :
    (∀ n : ℕ, 0 < n → Module.finrank ℚ_[p] (cyclotomicTower p n) = (p - 1) * p ^ (n - 1)) ∧
    (∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      σ ∈ (cyclotomicTower p (m + 2)).fixingSubgroup →
      σ ∉ (cyclotomicTower p (m + 3)).fixingSubgroup →
        σ ^ p ∈ (cyclotomicTower p (m + 3)).fixingSubgroup ∧
          σ ^ p ∉ (cyclotomicTower p (m + 4)).fixingSubgroup) :=
  ⟨finrank_cyclotomicTower p, pow_mem_and_not_mem_fixingSubgroup p⟩

/-- The degree of the tower, as the explicit `φ(p^n)`. Convenient when the tower is compared
with an arbitrary finite subextension of `ℚ̄_p/ℚ_p`. -/
theorem finrank_cyclotomicTower_eq_totient (n : ℕ) :
    Module.finrank ℚ_[p] (cyclotomicTower p n) = (p ^ n).totient := by
  have hp : p.Prime := Fact.out
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h1 : cyclotomicTower p 0 = ⊥ := by
      have hζ : IsPrimitiveRoot (1 : PadicAlgCl p) (p ^ 0) := by
        simp
      rw [cyclotomicTower_eq_adjoin p 0 hζ]
      simp
    rw [h1]
    simp
  · rw [finrank_cyclotomicTower p n hn, Nat.totient_prime_pow hp hn, mul_comm]

/-- **Each step of the tower multiplies the degree by `p`** (for `n > 0`). This is the `hdeg`
hypothesis of the normalised-trace construction, where the tower is indexed from level `2`. -/
theorem finrank_cyclotomicTower_succ (n : ℕ) (hn : 0 < n) :
    Module.finrank ℚ_[p] (cyclotomicTower p (n + 1)) =
      p * Module.finrank ℚ_[p] (cyclotomicTower p n) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [finrank_cyclotomicTower p (k + 2) (by omega), finrank_cyclotomicTower p (k + 1) (by omega)]
  have h21 : k + 2 - 1 = k + 1 := by omega
  have h11 : k + 1 - 1 = k := by omega
  rw [h21, h11, pow_succ]
  ring

/-- The `hdeg` hypothesis in the exact shift the normalised-trace construction uses
(`Km m = ℚ_p(μ_{p^{m+2}})`). -/
theorem finrank_cyclotomicTower_shift_succ (m : ℕ) :
    Module.finrank ℚ_[p] (cyclotomicTower p (m + 3)) =
      p * Module.finrank ℚ_[p] (cyclotomicTower p (m + 2)) :=
  finrank_cyclotomicTower_succ p (m + 2) (by omega)

/-- **The tower hypotheses of the normalised-trace construction**, for the tower
`Km m = ℚ_p(μ_{p^{m+2}})`: monotone, each level finite over `ℚ_p`, stable under the Galois
action, each step of degree `p`, and the degree-`p` step read on fixing subgroups.

These are exactly the `hmono`, `hfin`, `hstab`, `hdeg` and `hcyc` hypotheses of Tate's
normalised-trace construction. The one remaining hypothesis of that construction, the norm
estimate on `∑_{i < p} σ^i y`, is **not** proved here. -/
theorem cyclotomicTower_shift_hypotheses :
    Monotone (fun m : ℕ => cyclotomicTower p (m + 2)) ∧
    (∀ m : ℕ, FiniteDimensional ℚ_[p] ↥(cyclotomicTower p (m + 2))) ∧
    (∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      σ ∈ (cyclotomicTower p (0 + 2)).fixingSubgroup →
        ∀ y ∈ cyclotomicTower p (m + 2), σ y ∈ cyclotomicTower p (m + 2)) ∧
    (∀ m n : ℕ, n = m + 1 →
      Module.finrank ℚ_[p] ↥(cyclotomicTower p (n + 2)) =
        p * Module.finrank ℚ_[p] ↥(cyclotomicTower p (m + 2))) ∧
    (∀ (m : ℕ) (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p),
      σ ∈ (cyclotomicTower p (m + 2)).fixingSubgroup →
      σ ∉ (cyclotomicTower p (m + 3)).fixingSubgroup →
        σ ^ p ∈ (cyclotomicTower p (m + 3)).fixingSubgroup ∧
          σ ^ p ∉ (cyclotomicTower p (m + 4)).fixingSubgroup) := by
  refine ⟨fun a b hab => cyclotomicTower_mono p (by omega), fun m => inferInstance,
    fun m σ _ y hy => map_mem_cyclotomicTower p (m + 2) σ hy, ?_,
    pow_mem_and_not_mem_fixingSubgroup p⟩
  rintro m n rfl
  exact finrank_cyclotomicTower_shift_succ p m

end

end PadicAlgCl
