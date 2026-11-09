import ZInQKernel.Assembly.Local.FormalMultiplication
import ZInQKernel.Size.FormalMultiple.ReductionOrders

/-!
# Deep multiples of the generator

Blueprint: `assembly/local-tests/deep-multiples.md`.

For every prime element `π` of `ℤ[s]` and every integer `N ≥ 1` there is `m ≥ 1` with
`[jm]P₀ ∈ E_N(π)` for every `j ∈ ℤ` (`exists_smul_mem_Ek`); for a finite set `Ps` of prime
elements there is one `κ ≥ 1` that works at every `π ∈ Ps` (`exists_common_smul_mem_Ek`).

First `[m₁]P₀ ∈ E₁(π)`: at `π ∼ s` with `m₁ = 1` (`genP0_mem_formalFilt_three`), above an odd
prime by the reduction orders of `P₀` (`ZInQ.Size.exists_reduction_multiple`). Multiplying by
the rational prime `p` below `π` raises the level by one (`zsmul_mem_formalFilt_succ`).

`E_k(π)` depends only on the associate class of `π` (`Ek_congr`).
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Mult

/-- Associated primes give the same additive valuation. -/
theorem vP_congr {π π' : Zs} (hπ : Prime π) (hπ' : Prime π') (h : Associated π π') (x : K0) :
    vP π hπ x = vP π' hπ' x := by
  by_cases hx : x = 0
  · rw [hx, AddValuation.map_zero, AddValuation.map_zero]
  rw [vP_apply hπ hx, vP_apply hπ' hx, vp_eq_of_associated h]

/-- `E_k(π)` depends only on the ideal `(π)`. -/
theorem Ek_congr {π π' : Zs} (hπ : Prime π) (hπ' : Prime π') (h : Associated π π') (k : ℤ)
    (P : genCurve.toAffine.Point) : P ∈ Ek π hπ k ↔ P ∈ Ek π' hπ' k := by
  rcases P with _ | ⟨x, y, hP⟩
  · exact ⟨fun _ => (Ek π' hπ' k).zero_mem, fun _ => (Ek π hπ k).zero_mem⟩
  change (vP π hπ x < 0 ∧ (k : WithTop ℤ) ≤ vP π hπ (-x / y)) ↔
    (vP π' hπ' x < 0 ∧ (k : WithTop ℤ) ≤ vP π' hπ' (-x / y))
  rw [vP_congr hπ hπ' h, vP_congr hπ hπ' h]

/-- Every prime of `ℤ[s]` lies above a rational prime. -/
theorem exists_prime_below {π : Zs} (hπ : Prime π) : ∃ p : ℕ, p.Prime ∧ π ∣ (p : Zs) := by
  set N := (QuadraticAlgebra.norm π).natAbs with hN
  have hN0 : N ≠ 0 := by
    rw [hN, Int.natAbs_ne_zero]; exact fun h => hπ.ne_zero (Zs.norm_eq_zero_iff.mp h)
  have hdvd : π ∣ (N : Zs) := by
    have h1 : π ∣ ((QuadraticAlgebra.norm π : ℤ) : Zs) :=
      ⟨star π, by rw [← eq_intCast (algebraMap ℤ Zs), QuadraticAlgebra.algebraMap_norm_eq_mul_star]⟩
    rcases Int.natAbs_eq (QuadraticAlgebra.norm π) with h | h
    · rw [h, ← hN] at h1; simpa using h1
    · rw [h, ← hN] at h1; simpa using h1
  rw [← Nat.prod_primeFactorsList hN0, Nat.cast_list_prod] at hdvd
  obtain ⟨a, ha, hπa⟩ := (Prime.dvd_prod_iff hπ).mp hdvd
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp ha
  exact ⟨p, Nat.prime_of_mem_primeFactorsList hp, hπa⟩

/-- `v_π(p) ≥ 1` for the rational prime `p` below `π`. -/
theorem vge_natCast_of_dvd {π : Zs} (hπ : Prime π) {p : ℕ} (hπp : π ∣ (p : Zs)) :
    Vge (vP π hπ) 1 ((p : ℤ) : K0) := by
  rw [Vge, le_vP_iff, Int.cast_natCast]
  by_cases hp0 : (p : K0) = 0
  · exact Or.inl hp0
  right
  have hpZ : (p : Zs) ≠ 0 := by
    intro h; apply hp0; rw [← toK0_natCast, h, map_zero]
  rw [← toK0_natCast]
  exact_mod_cast (le_vp_iff_pow_dvd hπ hpZ 1).mpr (by simpa using hπp)

/-- The first step: some positive multiple of `P₀` lies in `E₁(π)`. -/
theorem exists_smul_mem_Ek_one {π : Zs} (hπ : Prime π) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : ℤ) • genP0 ∈ Ek π hπ 1 := by
  obtain ⟨p, hp, hπp⟩ := exists_prime_below hπ
  by_cases hp2 : p = 2
  · -- `π` is associated to `s`, and `P₀ ∈ E₃(s)`
    subst hp2
    have hs : π ∣ sqrt2Z := by
      rw [show ((2 : ℕ) : Zs) = sqrt2Z ^ 2 by rw [Nat.cast_ofNat, two_eq_sqrt2Z_sq]] at hπp
      exact hπ.dvd_of_dvd_pow hπp
    refine ⟨1, le_rfl, ?_⟩
    rw [Nat.cast_one, one_zsmul, Ek_congr hπ prime_sqrt2Z (hπ.associated_of_dvd prime_sqrt2Z hs)]
    exact formalFilt_antitone _ (by norm_num) genP0_mem_formalFilt_three
  · have := Fact.mk hp
    obtain ⟨m₀, hm₀, -, hmem⟩ := ZInQ.Size.exists_reduction_multiple p hp.one_lt.le
    refine ⟨m₀, hm₀, ?_⟩
    have h1 := hmem p (Nat.mem_primeFactors.mpr ⟨hp, dvd_rfl, hp.ne_zero⟩) hp2 π hπ hπp
    exact (mem_formalNbhd_iff (vP_genA_nonneg π hπ) _).mpr
      ((ZInQ.Size.inE1_iff_mem_W1 hπ _).mp h1)

/-- **Deep multiples at one prime.** For every prime `π` and `N ≥ 1` there is `m ≥ 1` with
`[jm]P₀ ∈ E_N(π)` for all `j ∈ ℤ`. -/
theorem exists_smul_mem_Ek {π : Zs} (hπ : Prime π) (N : ℤ) (hN : 1 ≤ N) :
    ∃ m : ℕ, 1 ≤ m ∧ ∀ j : ℤ, (j * m) • genP0 ∈ Ek π hπ N := by
  obtain ⟨m₁, hm₁, h1⟩ := exists_smul_mem_Ek_one hπ
  obtain ⟨p, hp, hπp⟩ := exists_prime_below hπ
  have hpv := vge_natCast_of_dvd hπ hπp
  have step : ∀ i : ℕ, ((p ^ i * m₁ : ℕ) : ℤ) • genP0 ∈ Ek π hπ (1 + i) := by
    intro i
    induction i with
    | zero => simpa using h1
    | succ i ih =>
      have := zsmul_mem_formalFilt_succ (vP_genA_nonneg π hπ) hpv (by omega) ih
      have key : ((p ^ (i + 1) * m₁ : ℕ) : ℤ) • genP0 =
          (p : ℤ) • (((p ^ i * m₁ : ℕ) : ℤ) • genP0) := by
        rw [smul_smul]; congr 1; push_cast; ring
      rw [key, show (1 : ℤ) + ((i + 1 : ℕ) : ℤ) = 1 + i + 1 by push_cast; ring]
      exact this
  refine ⟨p ^ (N - 1).toNat * m₁, Nat.one_le_iff_ne_zero.mpr
    (mul_ne_zero (pow_ne_zero _ hp.ne_zero) (by omega)), fun j => ?_⟩
  have h := step (N - 1).toNat
  rw [show (1 : ℤ) + ((N - 1).toNat : ℤ) = N by omega] at h
  rw [mul_smul]
  exact zsmul_mem h j

/-- **Deep multiples at finitely many primes.** For a finite set `Ps` of primes and `N ≥ 1`
there is `κ ≥ 1` with `[jκ]P₀ ∈ E_N(π)` for all `π ∈ Ps` and `j ∈ ℤ`. -/
theorem exists_common_smul_mem_Ek (Ps : Finset Zs) (N : ℤ) (hN : 1 ≤ N) :
    ∃ κ : ℕ, 1 ≤ κ ∧ ∀ π ∈ Ps, ∀ hπ : Prime π, ∀ j : ℤ, (j * κ) • genP0 ∈ Ek π hπ N := by
  classical
  have h : ∀ π : Zs, ∃ m : ℕ, 1 ≤ m ∧ ∀ hπ : Prime π, ∀ j : ℤ, (j * m) • genP0 ∈ Ek π hπ N := by
    intro π
    by_cases hπ : Prime π
    · obtain ⟨m, hm, hmem⟩ := exists_smul_mem_Ek hπ N hN
      exact ⟨m, hm, fun _ => hmem⟩
    · exact ⟨1, le_rfl, fun h => absurd h hπ⟩
  choose m hm hmem using h
  refine ⟨∏ π ∈ Ps, m π, Finset.one_le_prod fun π _ => hm π, fun π hπP hπ j => ?_⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem m hπP
  rw [hc, Nat.cast_mul, mul_comm (m π : ℤ), ← mul_assoc]
  exact hmem π hπ (j * c)

end ZInQ.Assembly
