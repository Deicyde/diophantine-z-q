import ZInQKernel.Multiplication.Local.LogCoefficients
import ZInQKernel.Multiplication.Local.PrimesAbove
import ZInQKernel.Multiplication.Local.Valuations

/-!
# The truncated logarithm is `16575 z` times a unit

Blueprint: `multiplication/local/truncation-unit.md`.

At every nonzero prime `π` of `ℤ[s]` (including `(s)`), if `v_π(z) ≥ 1` then
`L(z) = 16575 z (1 + η)` with `v_π(η) ≥ 2`; in particular `L(z) ≠ 0` for `z ≠ 0`. The same holds
in the completion `K_π`. The generic statement (`truncLog_eq_mul_unit`) needs only
`v(δ) ≥ 0` and `v(16575) ≤ 2`; at the primes of `ℤ[s]`, `v_π(16575) ≤ 2` because
`16575 = 3 · 5² · 13 · 17` and the odd primes are unramified (`vp_16575_le_two`).
-/

namespace ZInQ.Mult

open IsDedekindDomain

section Generic

variable {F : Type*} [Field F] {v : AddValuation F (WithTop ℤ)}

theorem Vge.div_val {m e : ℤ} {x y : F} (hx : Vge v m x) (hy : v y = e) : Vge v (m - e) (x / y) := by
  by_cases h : x = 0
  · subst h; rw [zero_div]; exact Vge.zero _
  obtain ⟨n, hn⟩ := val_eq_coe h
  rw [vge_iff_of_eq (val_div_coe hn hy)]
  have := (vge_iff_of_eq hn).mp hx
  omega

/-- **The truncated logarithm is `16575 z` times a unit** (generic form): if `v(δ) ≥ 0`,
`v(16575) ≤ 2` and `v(z) ≥ 1`, then `L(z) = 16575 z (1 + η)` with `v(η) ≥ 2`. -/
theorem truncLog_eq_mul_unit {δ : F} (hδ : 0 ≤ v δ) (hc : v (16575 : F) ≤ 2) {z : F}
    (hz : 1 ≤ v z) : ∃ η : F, 2 ≤ v η ∧ truncLog δ z = 16575 * z * (1 + η) := by
  have hc0 : (16575 : F) ≠ 0 := by
    intro h; rw [h, v.map_zero] at hc; exact absurd hc (by simp)
  obtain ⟨e, he⟩ := val_eq_coe hc0
  have he2 : e ≤ 2 := by
    have h' : ((e : ℤ) : WithTop ℤ) ≤ ((2 : ℤ) : WithTop ℤ) := by rw [← he]; exact hc
    exact WithTop.coe_le_coe.mp h'
  have hδ' : Vge v 0 δ := hδ
  have hz' : Vge v 1 z := hz
  set N : F := -6630 * δ * z ^ 4 + 11050 * δ ^ 2 * z ^ 8 - 25500 * δ ^ 3 * z ^ 12 +
    68250 * δ ^ 4 * z ^ 16 - 198900 * δ ^ 5 * z ^ 20 + 612612 * δ ^ 6 * z ^ 24 with hN
  have term : ∀ (c : ℤ) (j : ℕ), 1 ≤ j → Vge v 4 ((c : F) * δ ^ j * z ^ (4 * j)) := by
    intro c j hj
    have := ((vge_intCast (v := v) c).mul (hδ'.pow j)).mul (hz'.pow (4 * j))
    exact this.mono (by push_cast; nlinarith)
  have hNv : Vge v 4 N := by
    have t1 := term (-6630) 1 le_rfl
    have t2 := term 11050 2 (by norm_num)
    have t3 := term 25500 3 (by norm_num)
    have t4 := term 68250 4 (by norm_num)
    have t5 := term 198900 5 (by norm_num)
    have t6 := term 612612 6 (by norm_num)
    push_cast at t1 t2 t3 t4 t5 t6
    simp only [pow_one] at t1
    rw [hN]
    exact ((((t1.add t2).sub t3).add t4).sub t5).add t6
  refine ⟨N / 16575, ?_, ?_⟩
  · have := (hNv.div_val he).mono (show (2 : ℤ) ≤ 4 - e by omega)
    exact this
  · rw [truncLog_eq, hN]
    field_simp
    ring

/-- In particular `L(z) ≠ 0` for `z ≠ 0` with `v(z) ≥ 1`. -/
theorem truncLog_ne_zero {δ : F} (hδ : 0 ≤ v δ) (hc : v (16575 : F) ≤ 2) {z : F}
    (hz : 1 ≤ v z) (hz0 : z ≠ 0) : truncLog δ z ≠ 0 := by
  obtain ⟨η, hη, h⟩ := truncLog_eq_mul_unit hδ hc hz
  have hc0 : (16575 : F) ≠ 0 := by
    intro h; rw [h, v.map_zero] at hc; exact absurd hc (by simp)
  rw [h]
  refine mul_ne_zero (mul_ne_zero hc0 hz0) (one_add_ne_zero (v := v) ?_)
  exact le_trans (show ((1 : ℤ) : WithTop ℤ) ≤ ((2 : ℤ) : WithTop ℤ) from
    WithTop.coe_le_coe.mpr (by norm_num)) hη

end Generic

/-! ### At the primes of `ℤ[s]` -/

theorem vp_natPrime_le_one {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {π : Zs} (hπ : Prime π) :
    0 ≤ vp π (q : K0) ∧ vp π (q : K0) ≤ 1 := by
  have hq0 : (q : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this
    exact (Fact.out : q.Prime).ne_zero this
  have h0 := vp_nonneg hπ (q : Zs)
  rw [toK0_natCast] at h0
  by_cases hd : π ∣ (q : Zs)
  · rw [vp_natCast_self hq2 hπ hd]; omega
  · rw [← toK0_natCast, (vp_eq_zero_iff hπ hq0).mpr hd]; omega

theorem vp_natCast_coprime {q q' : ℕ} (hqq : Nat.Coprime q q') {π : Zs} (hπ : Prime π) :
    vp π (q : K0) = 0 ∨ vp π (q' : K0) = 0 := by
  by_cases hq : q = 0
  · subst hq; simp at hqq; subst hqq; right; simp [vp_one hπ]
  by_cases hq' : q' = 0
  · subst hq'; simp at hqq; subst hqq; left; simp [vp_one hπ]
  have hq0 : (q : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; exact hq this
  have hq0' : (q' : Zs) ≠ 0 := by
    intro h; have := congrArg QuadraticAlgebra.re h; simp at this; exact hq' this
  by_contra hcon
  push Not at hcon
  rw [← toK0_natCast, ← toK0_natCast, ne_eq, vp_eq_zero_iff hπ hq0, ne_eq,
    vp_eq_zero_iff hπ hq0', not_not, not_not] at hcon
  have hcop : IsCoprime (q : Zs) (q' : Zs) := by
    have := (Nat.isCoprime_iff_coprime.mpr hqq).map (Int.castRingHom Zs); simpa using this
  exact hπ.not_isUnit (hcop.isUnit_of_dvd' hcon.1 hcon.2)

/-- `v_π(16575) ≤ 2` at every prime `π` of `ℤ[s]`. -/
theorem vp_16575_le_two {π : Zs} (hπ : Prime π) : vp π (16575 : K0) ≤ 2 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have h3 := vp_natPrime_le_one (q := 3) (by norm_num) hπ
  have h5 := vp_natPrime_le_one (q := 5) (by norm_num) hπ
  have h13 := vp_natPrime_le_one (q := 13) (by norm_num) hπ
  have h17 := vp_natPrime_le_one (q := 17) (by norm_num) hπ
  have c35 := vp_natCast_coprime (q := 3) (q' := 5) (by norm_num) hπ
  have c313 := vp_natCast_coprime (q := 3) (q' := 13) (by norm_num) hπ
  have c317 := vp_natCast_coprime (q := 3) (q' := 17) (by norm_num) hπ
  have c513 := vp_natCast_coprime (q := 5) (q' := 13) (by norm_num) hπ
  have c517 := vp_natCast_coprime (q := 5) (q' := 17) (by norm_num) hπ
  have c1317 := vp_natCast_coprime (q := 13) (q' := 17) (by norm_num) hπ
  have hfac : (16575 : K0) = (3 : ℕ) * ((5 : ℕ) ^ 2 * ((13 : ℕ) * (17 : ℕ))) := by norm_num
  have n3 : ((3 : ℕ) : K0) ≠ 0 := by norm_num
  have n5 : ((5 : ℕ) : K0) ≠ 0 := by norm_num
  have n13 : ((13 : ℕ) : K0) ≠ 0 := by norm_num
  have n17 : ((17 : ℕ) : K0) ≠ 0 := by norm_num
  rw [hfac, vp_mul hπ n3 (by positivity), vp_mul hπ (by positivity) (by positivity),
    vp_pow hπ, vp_mul hπ n13 n17]
  push_cast at h3 h5 h13 h17 c35 c313 c317 c513 c517 c1317 ⊢
  omega

theorem vP_16575_le_two {π : Zs} (hπ : Prime π) : vP π hπ (16575 : K0) ≤ 2 := by
  rw [vP_apply hπ (by norm_num)]
  exact WithTop.coe_le_coe.mpr (vp_16575_le_two hπ)

theorem vP_genD_sq_nonneg {π : Zs} (hπ : Prime π) : 0 ≤ vP π hπ (genD ^ 2) := by
  rw [show genD ^ 2 = Zs.toK0 (genDZ ^ 2) by simp]
  exact vP_toK0_nonneg _ _

/-- **The truncated logarithm is `16575 z` times a unit** at every prime `π` of `ℤ[s]`:
if `v_π(z) ≥ 1` then `L(z) = 16575 z (1 + η)` with `v_π(η) ≥ 2`. -/
theorem log25_eq_mul_unit {π : Zs} (hπ : Prime π) {z : K0} (hz : 1 ≤ vP π hπ z) :
    ∃ η : K0, 2 ≤ vP π hπ η ∧ truncLog (genD ^ 2) z = 16575 * z * (1 + η) :=
  truncLog_eq_mul_unit (vP_genD_sq_nonneg hπ) (vP_16575_le_two hπ) hz

/-- `L(z) ≠ 0` whenever `z ≠ 0` and `v_π(z) ≥ 1` for some prime `π`. -/
theorem log25_ne_zero {π : Zs} (hπ : Prime π) {z : K0} (hz0 : z ≠ 0) (hz : 1 ≤ vP π hπ z) :
    truncLog (genD ^ 2) z ≠ 0 :=
  truncLog_ne_zero (vP_genD_sq_nonneg hπ) (vP_16575_le_two hπ) hz hz0

/-! ### In the completion -/

/-- The additive valuation of the completion `K_π` of `K₀` at `π`. -/
noncomputable abbrev vComp (π : Zs) (hπ : Prime π) :
    AddValuation ((primeSpec π hπ).adicCompletion K0) (WithTop ℤ) :=
  ordOf Valued.v

theorem vComp_algebraMap {π : Zs} (hπ : Prime π) (x : K0) :
    vComp π hπ (algebraMap K0 ((primeSpec π hπ).adicCompletion K0) x) = vP π hπ x := by
  by_cases hx : x = 0
  · subst hx; simp
  have hx' : algebraMap K0 ((primeSpec π hπ).adicCompletion K0) x ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K0 _).injective).mpr hx
  rw [vComp, ordOf_apply _ hx', vP, ordOf_apply _ hx]
  congr 3
  exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (primeSpec π hπ) x

/-- The truncated logarithm in the completion `K_π`, at the same prime. -/
theorem log25_eq_mul_unit_completion {π : Zs} (hπ : Prime π)
    {z : (primeSpec π hπ).adicCompletion K0} (hz : 1 ≤ vComp π hπ z) :
    ∃ η, 2 ≤ vComp π hπ η ∧
      truncLog (algebraMap K0 _ (genD ^ 2)) z = 16575 * z * (1 + η) := by
  refine truncLog_eq_mul_unit ?_ ?_ hz
  · rw [vComp_algebraMap]; exact vP_genD_sq_nonneg hπ
  · rw [show (16575 : (primeSpec π hπ).adicCompletion K0) = algebraMap K0 _ 16575 from
      (map_ofNat _ 16575).symm,
      vComp_algebraMap]
    exact vP_16575_le_two hπ

end ZInQ.Mult
