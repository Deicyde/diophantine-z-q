import ZInQKernel.Multiplication.Local.FormalLog
import ZInQKernel.Multiplication.Local.FormalGroup
import ZInQKernel.Multiplication.Local.TruncationUnit

/-!
# The truncation error at a large prime

Blueprint: `multiplication/local/truncation-error.md`.

Let `p > 324` be prime, `π ∣ p` a prime of `ℤ[s]`, `K_π` the completion and `λ = log ∘ z` the
formal logarithm of `E` over `K_π`. For `P ∈ E₁(K_π)`, `P ≠ O`:

1. `v(λ(P)) = v(z(P)) ≥ 1`;
2. `L(z(P)) = 16575 λ(P) (1 + ε)` with `v(ε) ≥ 28`.

The generic form (`partialLog_truncation_error`) is over any complete `ℤᵐ⁰`-valued field of
residue characteristic `p > 324` with `v(p) = 1`: the omitted terms `r = 4j + 1 ≥ 29` have
relative valuation `≥ (r - 1) v(t) - v_p(r) ≥ 28 v(t)`.
-/

namespace ZInQ.Mult

open Finset WithZero WeierstrassCurve WeierstrassCurve.Affine

/-- `L(t) = 16575 Σ_{r < 26} b_{r-1} t^r / r` for `A = -d²`: `L` is `16575` times the
degree-`25` partial sum of the formal logarithm. -/
theorem truncLog_eq_partialLog {F : Type*} [Field F] [CharZero F] (d t : F) :
    truncLog (d ^ 2) t = 16575 * ∑ r ∈ range 26, logCoeffA (-d ^ 2) r * t ^ r := by
  rw [truncLog_eq_trunc]
  congr 1
  simp only [sum_range_succ, sum_range_zero, logCoeffA, invDiffCoeff, logCoeff]
  norm_num [Nat.centralBinom, Nat.choose]
  ring

/-- The partial sum `Σ_{r < 26} b_{r-1} t^r / r`. -/
def partialLog {F : Type*} [Field F] (A t : F) : F := ∑ r ∈ range 26, logCoeffA A r * t ^ r

variable {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K]

/-- The relative bound for an omitted term: `(n - 29) m ≥ v_p(n)` for `n ≥ 29`, `m ≥ 1`,
`p > 324`. -/
theorem omitted_term_bound {p : ℕ} [Fact p.Prime] (hp324 : 324 < p) {n : ℕ} (hn : 29 ≤ n)
    {m : ℤ} (hm : 1 ≤ m) : ((padicValNat p n : ℕ) : ℤ) ≤ ((n : ℤ) - 29) * m := by
  have hb := padicValNat_bernoulli (p := p) (r := n) (by omega)
  generalize padicValNat p n = k at hb ⊢
  have hp' : (324 : ℤ) ≤ (p : ℤ) - 1 := by omega
  have hn' : (29 : ℤ) ≤ n := by exact_mod_cast hn
  have hk0 : (0 : ℤ) ≤ k := by positivity
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; push_cast; nlinarith
  · have hk1 : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith

/-- **The truncation error** (generic form): if `p > 324`, `v(p) = 1`, `v(A) ≥ 0` and
`v(t) ≥ 1`, `t ≠ 0`, then `v(log t) = v(t)` and `Σ_{r<26} b_{r-1} t^r / r = log(t) (1 + ε)` with
`v(ε) ≥ 28`. -/
theorem partialLog_truncation_error {p : ℕ} [Fact p.Prime] (hp324 : 324 < p)
    (h : ResidueChar K p 1) {A t : K} (hA : 0 ≤ vK K A) (ht : 1 ≤ vK K t) (ht0 : t ≠ 0) :
    vK K (evalLog A t) = vK K t ∧
      ∃ ε : K, 28 ≤ vK K ε ∧ partialLog A t = evalLog A t * (1 + ε) := by
  obtain ⟨m, hmt⟩ := val_eq_coe ht0
  have hm1 : 1 ≤ m := by rw [hmt] at ht; exact_mod_cast ht
  have hiso := (evalLog_isometry h hA hmt (by push_cast; have := hp324; nlinarith)).2
  refine ⟨hiso, ?_⟩
  set f : ℕ → K := fun r => logCoeffA A r * t ^ r with hf
  have hs : Summable f := summable_log h hA ht
  -- the tail `Σ_{r ≥ 26}` has valuation `≥ 29 m`
  have hT : vK K (t ^ 29) ≤ vK K (∑' r, f (r + 26)) := by
    refine le_vK_tsum ((summable_nat_add_iff (f := f) 26).mpr hs) fun r => ?_
    rw [val_pow_coe hmt]
    by_cases hr : (r + 26 - 1) % 4 = 0
    · have hterm := vge_logTerm h hA (Vge.of_eq hmt) (r + 26)
      refine (hterm.mono ?_)
      have := omitted_term_bound hp324 (n := r + 26) (by omega) hm1
      push_cast at this ⊢
      nlinarith
    · have hr' : (r + 25) % 4 ≠ 0 := by omega
      have : logCoeffA A (r + 26) = 0 := by simp [logCoeffA, invDiffCoeff, hr']
      simp only [hf, this, zero_mul, (vK K).map_zero, le_top]
  have hsplit : partialLog A t = evalLog A t - ∑' r, f (r + 26) := by
    rw [evalLog, ← hs.sum_add_tsum_nat_add 26, partialLog]; ring
  have hD0 : evalLog A t ≠ 0 := by
    intro h0; rw [h0, (vK K).map_zero, hmt] at hiso; exact WithTop.top_ne_coe hiso
  refine ⟨-(∑' r, f (r + 26)) / evalLog A t, ?_, ?_⟩
  · have hv : Vge (vK K) (29 * m) (∑' r, f (r + 26)) := by
      have := hT; rw [val_pow_coe hmt] at this; exact_mod_cast this
    have := hv.neg.div_val' (show vK K (evalLog A t) = m by rw [hiso, hmt])
    exact (this.mono (by omega) : Vge (vK K) 28 _)
  · rw [hsplit]; field_simp; ring

/-! ### At a prime above `p > 324` -/

instance charZero_completion (π : Zs) (hπ : Prime π) :
    CharZero ((primeSpec π hπ).adicCompletion K0) :=
  charZero_of_injective_algebraMap (algebraMap K0 _).injective

/-- The completion `K_π` has residue characteristic `p` and `v(p) = 1` for `π ∣ p`, `p` odd. -/
theorem residueChar_completion {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {π : Zs} (hπ : Prime π)
    (hπp : π ∣ (p : Zs)) : ResidueChar ((primeSpec π hπ).adicCompletion K0) p 1 where
  val_p := by
    rw [show ((p : ℕ) : (primeSpec π hπ).adicCompletion K0) = algebraMap K0 _ (p : K0) by simp]
    erw [vComp_algebraMap hπ]
    rw [vP_apply hπ (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero), vp_natCast_self hp2 hπ hπp]
    rfl
  val_coprime n hn := by
    have hn0 : n ≠ 0 := by rintro rfl; exact hn (dvd_zero p)
    rw [show ((n : ℕ) : (primeSpec π hπ).adicCompletion K0) = algebraMap K0 _ (n : K0) by simp]
    erw [vComp_algebraMap hπ]
    rw [vP_apply hπ (Nat.cast_ne_zero.mpr hn0), vp_natCast_of_not_dvd hπ hπp hn]
    rfl

/-- `d` in the completion `K_π`. -/
noncomputable abbrev genDAt (π : Zs) (hπ : Prime π) : (primeSpec π hπ).adicCompletion K0 :=
  algebraMap K0 _ genD

theorem vComp_neg_genDAt_sq_nonneg {π : Zs} (hπ : Prime π) :
    0 ≤ vComp π hπ (-genDAt π hπ ^ 2) := by
  rw [show -genDAt π hπ ^ 2 = algebraMap K0 _ (-genD ^ 2) by simp, vComp_algebraMap]
  rw [show -genD ^ 2 = Zs.toK0 (-genDZ ^ 2) by simp]
  exact vP_toK0_nonneg _ _

/-- The formal logarithm `λ(P) = log(z(P))` of a point of `y² = x³ + A x`. -/
noncomputable def ellLog {K : Type*} [Field K] [Valued K ℤᵐ⁰] {A : K}
    (P : (shortCurve A).toAffine.Point) : K :=
  evalLog A (zCoord P)

/-- **The truncation error at a large prime.** Let `p > 324` be prime and `π ∣ p`. For
`P ∈ E₁(K_π)`, `P ≠ O`: `v(λ(P)) = v(z(P)) ≥ 1`, and `L(z(P)) = 16575 λ(P) (1 + ε)` with
`v(ε) ≥ 28`. -/
theorem log25_truncation_error {p : ℕ} [Fact p.Prime] (hp324 : 324 < p) {π : Zs} (hπ : Prime π)
    (hπp : π ∣ (p : Zs)) (P : (shortCurve (-genDAt π hπ ^ 2)).toAffine.Point)
    (hP : P ∈ W1 (vComp π hπ) (-genDAt π hπ ^ 2)) (hP0 : P ≠ 0) :
    vComp π hπ (ellLog P) = vComp π hπ (zCoord P) ∧ 1 ≤ vComp π hπ (zCoord P) ∧
      ∃ ε, 28 ≤ vComp π hπ ε ∧
        truncLog (genDAt π hπ ^ 2) (zCoord P) = 16575 * ellLog P * (1 + ε) := by
  have hres := residueChar_completion (p := p) (by omega) hπ hπp
  have hA := vComp_neg_genDAt_sq_nonneg hπ
  rcases P with _ | ⟨x, y, hxy⟩
  · exact absurd rfl hP0
  obtain ⟨N, hN, -, -, hy0, hz, -⟩ := formal_val_x_y hA hxy hP
  have hz1 : 1 ≤ vComp π hπ (zCoord (Point.some x y hxy)) := by rw [hz]; exact_mod_cast hN
  have hz0 : zCoord (Point.some x y hxy) ≠ 0 := by
    intro h0; rw [h0, (vComp π hπ).map_zero] at hz; exact WithTop.top_ne_coe hz
  obtain ⟨h1, ε, hε, h2⟩ := partialLog_truncation_error hp324 hres hA hz1 hz0
  refine ⟨h1, hz1, ε, hε, ?_⟩
  rw [truncLog_eq_partialLog, ← partialLog, h2, ellLog]; ring

/-- For `P = O` both sides of the truncation identity vanish. -/
theorem log25_truncation_zero {π : Zs} (hπ : Prime π) :
    truncLog (genDAt π hπ ^ 2) (zCoord (0 : (shortCurve (-genDAt π hπ ^ 2)).toAffine.Point)) = 0 ∧
      ellLog (0 : (shortCurve (-genDAt π hπ ^ 2)).toAffine.Point) = 0 := by
  refine ⟨by simp [truncLog], ?_⟩
  have : (fun r : ℕ => logCoeffA (-genDAt π hπ ^ 2) r * (0 : (primeSpec π hπ).adicCompletion K0) ^ r) =
      fun _ => 0 := by
    funext r; rcases r with _ | r <;> simp [logCoeffA]
  simp only [ellLog, evalLog, zCoord_zero, this, tsum_zero]

end ZInQ.Mult
