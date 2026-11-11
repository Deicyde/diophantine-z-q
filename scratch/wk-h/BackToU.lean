import ZInQKernel.Hypotheses.Height

/-!
# wk-h, Tier 1: the return to `u` (N5 F4 and the final numerics) in Lean

Draft for the reduction plan `docs/research/wk-h.md` §4.1. It replaces `SixContactMin` by its
`j`-form `JHeightBound`: a bound on the height of the Hauptmodul value `J(u) = −57600F(u)²/G(u)⁶`
(N5 L949-964; `scratch/h-b1/b1_checks.py`). The step from `J(u)` back to `u` (N5's rational-root
argument, F4 of `h-trust.md`) and the final arithmetic become Lean proofs.

`JHeightBound` is *not* a published theorem: it is the composite of h-trust steps A1-F3. This tier
only removes F4 and the final numerics from the trust base and fixes the interface for Tier 2
(`scratch/wk-h/Arakelov.lean`), whose conclusion is `JHeightBound`.

The constant `40·10⁴·2²⁴ + 22` is N5's: `h(j) ≤ 40 h([z_m]) + 22` (F2) with
`h([z_m]) ≤ 10⁴·2²⁴·max(1, h_F(A))` (F3), and `max(1, h_F(A)) ≤ max(1, C_cm, Q¹⁷) M²⁴` (E4).
-/

namespace ZInQ.WkH

open ZInQ

/-- The binary sextic `F_h(a,b) = a(a+15b)(a+20b)(a+24b)(a+30b)(a+60b)`. -/
def Fh (a b : ℤ) : ℤ := a * (a + 15 * b) * (a + 20 * b) * (a + 24 * b) * (a + 30 * b) * (a + 60 * b)

/-- The binary quadratic `G_h(a,b) = 7a² + 300ab + 3600b²` (discriminant `−10800 < 0`). -/
def Gh (a b : ℤ) : ℤ := 7 * a ^ 2 + 300 * a * b + 3600 * b ^ 2

/-- The Hauptmodul value `J(u) = −57600 F(u)² / G(u)⁶` (h-b1 M7). -/
def Jmap (u : ℚ) : ℚ :=
  -57600 * (u * (u + 15) * (u + 20) * (u + 24) * (u + 30) * (u + 60)) ^ 2 /
    (7 * u ^ 2 + 300 * u + 3600) ^ 6

/-- Nullstellensatz certificate for `x⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_x (a b : ℤ) :
    3 * a ^ 7 = (-200 * a - 4800 * b) * Fh a b +
      (29 * a ^ 5 + 3700 * a ^ 4 * b + 164400 * a ^ 3 * b ^ 2 + 2880000 * a ^ 2 * b ^ 3 +
        17280000 * a * b ^ 4) * Gh a b := by
  unfold Fh Gh; ring

/-- Nullstellensatz certificate for `y⁷` (`scratch/wk-h/f4_cert.py`). -/
theorem cert_y (a b : ℤ) :
    104976000000 * b ^ 7 = (-1001 * a - 37650 * b) * Fh a b +
      (143 * a ^ 5 + 20557 * a ^ 4 * b + 1026600 * a ^ 3 * b ^ 2 + 20691900 * a ^ 2 * b ^ 3 +
        133110000 * a * b ^ 4 + 29160000 * b ^ 5) * Gh a b := by
  unfold Fh Gh; ring

/-- `G` has no rational zero (negative discriminant). -/
theorem G_ne_zero (u : ℚ) : 7 * u ^ 2 + 300 * u + 3600 ≠ 0 := by
  nlinarith [sq_nonneg (7 * u + 150)]

/-- **F4, strengthened.** `12 h(u) ≤ h(J(u)) + 300` for `u ∉ 𝒞`. N5 proves `h(u) < h(J(u)) + 74`
by the rational-root theorem; the certificates give the degree-12 form. Proof plan (not yet
written): for `u = a/b` in lowest terms, `gcd(F_h, G_h) ∣ 3·104976000000` by `cert_x`, `cert_y`
and `gcd(a, b) = 1`; hence `gcd(57600F_h², G_h⁶) ∣ 57600·(3·104976000000)⁶`; and
`max(|a|,b)⁷ ≤ C·(max(|a|,b)·|F_h| + max(|a|,b)⁵·|G_h|)` with `C ≤ 2·10⁸` gives
`max(|a|,b)¹² ≤ (4·10⁸)⁶·max(57600F_h², G_h⁶)`. -/
theorem twelve_mul_ratHeight_le (u : ℚ) (hu : u ∉ contactSet) :
    12 * ratHeight u ≤ ratHeight (Jmap u) + 300 := by
  sorry

/-- `SixContactMin` for a general prime set `S` (`ZInQ.SixContactMin` is `SixContactMinAt
Mult.S_mul` by `rfl`; this scratch file imports only `Hypotheses/Height.lean`, because the
upstream package `lean/` is not built in this worktree). -/
def SixContactMinAt (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ratHeight u ≤ heightH6 (heightD : ℝ) * (contactSupport S u : ℝ) ^ 24

theorem contactSupport_pos' (S : Finset ℕ) (u : ℚ) : 0 < contactSupport S u := by
  unfold contactSupport
  exact Finset.prod_pos fun p hp =>
    (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1).pos

/-- The constant `X(R) = max(1, C_cm, Q_R¹⁷)` of N5's final display. -/
noncomputable def heightX (R : ℝ) : ℝ := max 1 (max (heightCcm : ℝ) (heightQ R ^ 17))

/-- **The `j`-form of H** (residual hypothesis of Tier 1): for every `u ∈ ℚ \ 𝒞`,
`h(J(u)) ≤ (40·10⁴·2²⁴ + 22)·max(1, C_cm, Q_D¹⁷)·M_S(u)²⁴`, at `S = Mult.S_mul`. -/
def JHeightBound (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet →
    ratHeight (Jmap u) ≤
      (40 * 10000 * 2 ^ 24 + 22 : ℝ) * heightX heightD * (contactSupport S u : ℝ) ^ 24

theorem heightH6_eq (R : ℝ) : heightH6 R = 2 * 10 ^ 13 * heightX R := rfl

/-- **Tier-1 reduction.** `JHeightBound → SixContactMin` (F4 and the final numerics). -/
theorem sixContactMin_of_jHeightBound {S : Finset ℕ} (hJ : JHeightBound S) :
    SixContactMinAt S := by
  intro u hu
  have h12 := twelve_mul_ratHeight_le u hu
  have hj := hJ u hu
  have hX : 1 ≤ heightX heightD := le_max_left _ _
  have hM : (1 : ℝ) ≤ (contactSupport S u : ℝ) ^ 24 :=
    one_le_pow₀ (by exact_mod_cast contactSupport_pos' _ _)
  have hXM : 1 ≤ heightX heightD * (contactSupport S u : ℝ) ^ 24 :=
    one_le_mul_of_one_le_of_one_le hX hM
  rw [heightH6_eq]
  nlinarith

end ZInQ.WkH
