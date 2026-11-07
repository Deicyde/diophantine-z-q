import ZInQKernel.Compiler.Precision.Decision
import ZInQKernel.Compiler.Precision.Threshold
import ZInQKernel.Compiler.Precision.NormZero

/-!
# Correctness of the decision program

Blueprint: `compiler/natural/precision/decision-program-correct.md`.

For every `c ∈ ℕ⁵`, `decide5 c = true ↔ accepts c` (`decide5_iff`). The steps: the early tests
are item 1 of the relation; the Jacobian test is admissibility (`admissible_iff_jmul`); for
admissible `k`, `z_k = ν_k / N_k` with `N_k ≠ 0` (`zIdx_eq_nu`), so `ε_l = U/V`
(`epsIdx_eq`) and `r(a, j) = θ/δ` (`rRatio_eq`); the closeness test becomes the integer
inequality `|θ - nδ| V < U |δ|`; and the precision test is `4^𝓑 ≤ L` by the threshold statement,
false for `L = 0` and computed by the capped precision test for `L ≥ 1`.
-/

namespace ZInQ.Compiler.Precision

open JTriple

theorem K0.intCast_re (m : ℤ) : (m : K0).re = m := by
  rw [← map_intCast Zs.toK0, Zs.toK0_re]; simp

theorem K0.intCast_im (m : ℤ) : (m : K0).im = 0 := by
  rw [← map_intCast Zs.toK0, Zs.toK0_im]; simp

/-- Division by an integer acts componentwise. -/
theorem K0.div_intCast (w : K0) (m : ℤ) : w / (m : K0) = ⟨w.re / m, w.im / m⟩ := by
  rcases eq_or_ne m 0 with rfl | hm
  · ext <;> simp
  · have hm' : (m : K0) ≠ 0 := Int.cast_ne_zero.mpr hm
    have hmq : (m : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hm
    rw [div_eq_iff hm']
    ext <;> simp <;> field_simp

/-- `N(ν) ∈ ℤ` maps to `ν ν̄` in `K₀`. -/
theorem toK0_norm (z : Zs) :
    ((QuadraticAlgebra.norm z : ℤ) : K0) = Zs.toK0 z * star (Zs.toK0 z) := by
  rw [← toK0_star, ← map_mul, Zs.mul_star_eq_norm, map_intCast]

/-- For admissible `k`, `z_k = ν_k / N_k` with `N_k ≠ 0`. -/
theorem zIdx_eq_nu {k : ℤ} (hk : Admissible k) :
    normJ (jmul k) ≠ 0 ∧ zIdx k = Zs.toK0 (nuJ (jmul k)) / (normJ (jmul k) : K0) := by
  obtain ⟨hZ, hY⟩ := (admissible_iff_jmul k).mp hk
  obtain ⟨h, e⟩ := jmul_eq_some hZ
  refine ⟨Zs.norm_ne_zero hY, ?_⟩
  rw [zIdx, e, zPt_some, normJ, toK0_norm, nuJ, map_neg, map_mul, map_mul, toK0_star]
  have hY' : Zs.toK0 (jmul k).Y ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr hY
  have hZ' : Zs.toK0 (jmul k).Z ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr hZ
  have hs : star (Zs.toK0 (jmul k).Y) ≠ 0 := star_ne_zero.mpr hY'
  field_simp

theorem nuJ_ne_zero {k : ℤ} (hk : Admissible k) : nuJ (jmul k) ≠ 0 := by
  intro h
  apply zIdx_ne_zero hk
  rw [(zIdx_eq_nu hk).2, h, map_zero, zero_div]

/-- `ε_l = U / V` with `U, V > 0`. -/
theorem epsIdx_eq {l : ℤ} (hl : Admissible l) :
    0 < epsU (jmul l) ∧ 0 < epsV (jmul l) ∧
      epsIdx l = (epsU (jmul l) : ℚ) / (epsV (jmul l) : ℚ) := by
  obtain ⟨hN, hz⟩ := zIdx_eq_nu hl
  have hν := nuJ_ne_zero hl
  refine ⟨?_, Int.natAbs_pos.mpr hN, ?_⟩
  · unfold epsU
    by_contra h0
    apply hν
    ext <;> simp <;> omega
  · rw [epsIdx, hz, K0.div_intCast, K0.mk_re, K0.mk_im, Zs.toK0_re, Zs.toK0_im, abs_div, abs_div,
      ← add_div, epsU, epsV]
    simp only [Nat.cast_add, Nat.cast_natAbs, Int.cast_abs]

/-- `r(a, j) = θ / δ` with `δ ≠ 0`. -/
theorem rRatio_eq {a j : ℤ} (ha : Admissible a) (hj : Admissible j) :
    ratioDen (jmul a) (jmul j) ≠ 0 ∧
      rRatio a j = (ratioNum (jmul a) (jmul j) : ℚ) / (ratioDen (jmul a) (jmul j) : ℚ) := by
  obtain ⟨hNa, hza⟩ := zIdx_eq_nu ha
  obtain ⟨hNj, hzj⟩ := zIdx_eq_nu hj
  have hνa := nuJ_ne_zero ha
  have hnorm := Zs.norm_ne_zero hνa
  refine ⟨mul_ne_zero hNj hnorm, ?_⟩
  have key : zIdx j / zIdx a =
      Zs.toK0 (nuJ (jmul j) * star (nuJ (jmul a)) * (normJ (jmul a) : Zs)) /
        (ratioDen (jmul a) (jmul j) : K0) := by
    rw [hza, hzj, ratioDen, Int.cast_mul, toK0_norm, map_mul, map_mul, map_intCast, toK0_star]
    have h1 : (normJ (jmul a) : K0) ≠ 0 := Int.cast_ne_zero.mpr hNa
    have h2 : (normJ (jmul j) : K0) ≠ 0 := Int.cast_ne_zero.mpr hNj
    have h3 : Zs.toK0 (nuJ (jmul a)) ≠ 0 := (map_ne_zero_iff _ Zs.toK0_injective).mpr hνa
    have h4 : star (Zs.toK0 (nuJ (jmul a))) ≠ 0 := star_ne_zero.mpr h3
    field_simp
  rw [rRatio, key, K0.div_intCast, K0.mk_re, Zs.toK0_re, ratioNum]

/-- The closeness test as an integer inequality. -/
theorem closeTest_iff {n a l j : ℤ} (hl : Admissible l) (ha : Admissible a) (hj : Admissible j) :
    CloseTestInt n a l j ↔
      |ratioNum (jmul a) (jmul j) - n * ratioDen (jmul a) (jmul j)| * (epsV (jmul l) : ℤ) <
        (epsU (jmul l) : ℤ) * |ratioDen (jmul a) (jmul j)| := by
  obtain ⟨-, hV, he⟩ := epsIdx_eq hl
  obtain ⟨hδ, hr⟩ := rRatio_eq ha hj
  set δ := ratioDen (jmul a) (jmul j)
  set θ := ratioNum (jmul a) (jmul j)
  have hδq : (δ : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hδ
  have hVq : (0 : ℚ) < epsV (jmul l) := by exact_mod_cast hV
  rw [CloseTestInt, hr, he, show (θ : ℚ) / δ - n = (θ - n * δ) / δ by field_simp, abs_div,
    div_lt_div_iff₀ (abs_pos.mpr hδq) hVq]
  constructor <;> intro h
  · exact_mod_cast h
  · exact_mod_cast h

/-- The precision test is computed by the capped test at `L = ⌊(V - 1)/(4U)⌋`. -/
theorem precisionTest_iff {n κ l : ℤ} (hl : Admissible l) :
    PrecisionTestInt n κ l ↔
      capL (jmul l) ≠ 0 ∧
        1 ≤ divFourLoop (capL (jmul l)) (cappedBound (capL (jmul l)) (κ * sixF n).natAbs) := by
  obtain ⟨hU, hV, he⟩ := epsIdx_eq hl
  rw [PrecisionTestInt, he, four_eps_mul_pow_lt_one_iff _ _ _ hU hV, bound]
  change 4 ^ (A0 * (κ * sixF n).natAbs ^ 24) ≤ capL (jmul l) ↔ _
  by_cases hL : capL (jmul l) = 0
  · rw [hL]
    simp only [ne_eq, not_true_eq_false, false_and, iff_false, not_le]
    positivity
  · rw [precision_test_iff _ _ (Nat.one_le_iff_ne_zero.mpr hL)]
    exact ⟨fun h => ⟨hL, h⟩, fun h => h.2⟩

/-- `decideInt` computes the precision relation on decoded inputs. -/
theorem decideInt_iff (n κ a l j : ℤ) : decideInt n κ a l j = true ↔ acceptsInt n κ a l j := by
  unfold decideInt acceptsInt
  by_cases hE : EarlyTestsInt n κ a l j
  swap
  · simp [hE]
  rw [ite_eq_left hE]
  simp only
  by_cases hJ : (jmul l).Z = 0 ∨ (jmul a).Z = 0 ∨ (jmul j).Z = 0 ∨ (jmul l).Y = 0 ∨
      (jmul a).Y = 0 ∨ (jmul j).Y = 0
  · rw [ite_eq_left hJ]
    simp only [Bool.false_eq_true, false_iff, not_and]
    intro _ hadm
    obtain ⟨hl, ha, hj⟩ := hadm
    rw [admissible_iff_jmul] at hl ha hj
    tauto
  rw [ite_eq_right hJ]
  have hl : Admissible l := (admissible_iff_jmul l).mpr (by tauto)
  have ha : Admissible a := (admissible_iff_jmul a).mpr (by tauto)
  have hj : Admissible j := (admissible_iff_jmul j).mpr (by tauto)
  rw [closeTest_iff hl ha hj, precisionTest_iff hl]
  simp only [hE, hl, ha, hj, true_and, and_self]
  split_ifs with hC hL
  · simp [hL]
  · simp [hL, hC]
  · simp [hC]

/-- **Correctness of the decision program**: `decide(c) = true ↔ accepts(c)` for every
`c ∈ ℕ⁵`. -/
theorem decide5_iff (c : Fin 5 → ℕ) : decide5 c = true ↔ accepts c :=
  decideInt_iff _ _ _ _ _

end ZInQ.Compiler.Precision
