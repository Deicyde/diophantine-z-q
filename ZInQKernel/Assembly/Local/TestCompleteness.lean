import ZInQKernel.Assembly.Local.PoleInputLocal
import ZInQKernel.Assembly.Local.PoleInputReal

/-!
# One suitable shift

Blueprint: `assembly/local-tests/test-completeness.md` (Lemma 11.2).

Assume pole completeness. For every `n ∈ ℤ \ 𝒞` there is `κ ≠ 0` with `Test(n, κ, n)`
(`test_complete`).

Let `η` be the sign of `F(n)`, `R₀ = η · 2730⁶ F(n) = |2730⁶ F(n)| > 1`, `Ps` the prime factors of
`R₀` in `ℤ[s]` and `N = 1 + Σ_{π ∈ Ps} v_π(F(n))`. Deep multiples give `κ ≥ 1` with
`[κ]P₀ ∈ E_N(π)` for all `π ∈ Ps`, hence (up to associates) at every prime dividing `R₀`. Take
`h = 2κ`, `s₀ = 2κn`; the real conditions give `q`, the local conditions the hypotheses of PC,
and PC gives `Φ(R/Θ²)`.
-/

namespace ZInQ.Assembly

open WeierstrassCurve WeierstrassCurve.Affine ZInQ.Mult ZInQ.Compiler.Precision

/-- A rational whose reduced denominator is prime to `R₀` is `p`-integral at every `p ∣ R₀`. -/
theorem padicValRat_nonneg_of_coprime {q : ℚ} {R₀ : ℕ} (hcop : Nat.Coprime q.den R₀) {p : ℕ}
    (hp : p.Prime) (hpR : p ∣ R₀) : 0 ≤ padicValRat p q := by
  have := Fact.mk hp
  have hd : ¬ p ∣ q.den := fun hd =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hd hcop) hpR)
  have hv := den_val q p
  rw [padicValNat.eq_zero_of_not_dvd hd] at hv
  omega

/-- **One suitable shift** (Lemma 11.2). Under pole completeness, every `n ∉ 𝒞` has a nonzero
shift `κ` with `Test(n, κ, n)`. -/
theorem test_complete (hPC : PoleCompleteness) (n : ℤ) (hn : (n : ℚ) ∉ contactSet) :
    ∃ κ : ℤ, κ ≠ 0 ∧ Test n κ n := by
  classical
  set F := sixF n with hFdef
  have hF0 : F ≠ 0 := by
    have := contactPoly_ne_zero_iff.mpr hn
    rw [contactPoly_intCast] at this; exact_mod_cast this
  set Z : ℤ := 2730 ^ 6 * F with hZdef
  have hZ0 : Z ≠ 0 := mul_ne_zero (by norm_num) hF0
  -- the sign `η` and `R₀ = |Z|`
  set η : ℚ := if 0 < F then 1 else -1 with hηdef
  have hη : η ^ 2 = 1 := by rw [hηdef]; split_ifs <;> norm_num
  set R₀ : ℕ := Z.natAbs with hR₀def
  have hR₀ : (R₀ : ℚ) = testR₀ η n := by
    rw [hR₀def, Nat.cast_natAbs, Int.cast_abs, testR₀, contactPoly_intCast, hZdef, hηdef]
    push_cast
    split_ifs with h
    · rw [abs_of_pos (by positivity)]; ring
    · have : (F : ℚ) < 0 := by
        have : F < 0 := lt_of_le_of_ne (not_lt.mp h) hF0
        exact_mod_cast this
      rw [abs_of_neg (by nlinarith)]; ring
  have hR₀1 : 1 < R₀ := by
    rw [hR₀def, hZdef, Int.natAbs_mul]
    have : 1 ≤ F.natAbs := Int.natAbs_pos.mpr hF0
    have h6 : (2730 ^ 6 : ℤ).natAbs = 2730 ^ 6 := by norm_num
    rw [h6]; nlinarith
  have hR₀Zs : (R₀ : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; omega
  -- deep multiples at the prime factors of `R₀`
  set Ps : Finset Zs := (UniqueFactorizationMonoid.factors (R₀ : Zs)).toFinset with hPs
  set N : ℤ := 1 + ∑ π ∈ Ps, vp π (F : K0) with hN
  have hvF : ∀ π ∈ Ps, vp π (F : K0) ≤ N := by
    intro π hπ
    have hπp : Prime π := UniqueFactorizationMonoid.prime_of_factor π (Multiset.mem_toFinset.mp hπ)
    have := Finset.single_le_sum (s := Ps) (f := fun π => vp π (F : K0))
      (fun π' hπ' => vp_nonneg_intCast
        (UniqueFactorizationMonoid.prime_of_factor π' (Multiset.mem_toFinset.mp hπ')) F) hπ
    omega
  have hN1 : 1 ≤ N := by
    have := Finset.sum_nonneg (s := Ps) (f := fun π => vp π (F : K0)) (fun π' hπ' =>
      vp_nonneg_intCast
        (UniqueFactorizationMonoid.prime_of_factor π' (Multiset.mem_toFinset.mp hπ')) F)
    omega
  obtain ⟨κn, hκn, hdeepPs⟩ := exists_common_smul_mem_Ek Ps N hN1
  set κ : ℤ := (κn : ℤ) with hκdef
  have hκ : 1 ≤ κ := by rw [hκdef]; exact_mod_cast hκn
  have hdeep : ∀ (π : Zs) (hπ : Prime π), π ∣ ((2730 ^ 6 * sixF n : ℤ) : Zs) →
      ∃ N' : ℤ, 1 ≤ N' ∧ vp π (sixF n : K0) ≤ N' ∧ κ • genP0 ∈ Ek π hπ N' := by
    intro π hπ hπZ
    have hπR : π ∣ (R₀ : Zs) := dvd_intCast_iff_natAbs.mp hπZ
    obtain ⟨π₁, hπ₁, hassoc⟩ :=
      UniqueFactorizationMonoid.exists_mem_factors_of_dvd hR₀Zs hπ.irreducible hπR
    have hπ₁p := UniqueFactorizationMonoid.prime_of_factor π₁ hπ₁
    have hπ₁Ps : π₁ ∈ Ps := Multiset.mem_toFinset.mpr hπ₁
    refine ⟨N, hN1, ?_, ?_⟩
    · rw [vp_eq_of_associated hassoc]; exact hvF π₁ hπ₁Ps
    · have := hdeepPs π₁ hπ₁Ps hπ₁p 1
      rw [one_mul] at this
      exact (Ek_congr hπ hπ₁p hassoc N _).mpr this
  -- the real conditions choose `q`
  set C := testC n κ n (2 * κ) (2 * κ * n) with hC
  obtain ⟨q, hcop, ha0, hW, hΘ, hpos, hhalf⟩ := poleInput_real R₀ hR₀1 C
  rw [hR₀] at ha0 hW hΘ hpos hhalf
  have hq : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ 2730 ^ 6 * sixF n → 0 ≤ padicValRat p q :=
    fun p hp hpZ => padicValRat_nonneg_of_coprime hcop hp (Int.natCast_dvd.mp hpZ)
  -- the local conditions and pole completeness
  obtain ⟨h2, h3, hsq⟩ := poleInput_local hn hη hκ hdeep hq ha0 hW hΘ
  have hΦ : PoleSoluble (testB n κ n η q (2 * κ) (2 * κ * n)) := by
    refine hPC _ hsq hpos hhalf fun p hp => ?_
    simp only [poleS0, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact h2
    · have := h3 3 (by simp); omega
    · have := h3 5 (by simp); omega
    · have := h3 7 (by simp); omega
    · have := h3 13 (by simp); omega
  refine ⟨κ, by omega, by omega, hn, 2 * κ, 2 * κ * n, η, q, by omega, by omega, hη, ha0, hW,
    hΘ, hΦ⟩

end ZInQ.Assembly
