import ZInQKernel.Compiler.Precision.HeightConstant

/-!
# E2-E4 and F3 arithmetic of N5 (h-trust steps E2, E3, E4, F3), and the CM-branch arithmetic

Real-number lemmas. Their hypotheses are the numerical outputs of the literature theorems
(Javanpeykar, Gaudron–Rémond Thm 1.4, Faltings' Lemma 5 with additivity, Bost, Pazuki); their
conclusions are N5's displayed bounds.
-/

namespace GlueAssembly

open Real ZInQ

/-! ### E3-E4: the non-CM transfer (N5 L868-905) -/

/-- **E3-E4 arithmetic, wk-h's form** (`scratch/wk-h/Arakelov.lean`, re-proved here). -/
theorem transfer_numerics {Q M hFJ g d L hA hZ : ℝ} (hQ : 10 ^ 12 ≤ Q) (hM : 1 ≤ M)
    (hg2 : 2 ≤ g) (hg : g ≤ Q ^ 3 * M ^ 4) (hd1 : 1 ≤ d) (hd : d ≤ Q * M)
    (hJ : hFJ ≤ Q ^ 13 * M ^ 24)
    (hL : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))))
    (hvar : hA + hZ ≤ hFJ + L / 2) (hZ : -(2 * g) ≤ hZ) :
    hA ≤ Q ^ 17 * M ^ 24 := by
  set P := Q * M ^ 4 with hPdef
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (by norm_num) hQ
  have hM4 : (1 : ℝ) ≤ M ^ 4 := one_le_pow₀ hM
  have hP : (10 : ℝ) ^ 12 ≤ P := by
    calc (10 : ℝ) ^ 12 = 10 ^ 12 * 1 := by ring
      _ ≤ Q * M ^ 4 := by gcongr
  have hP0 : 0 < P := lt_of_lt_of_le (by norm_num) hP
  have hlogP : log P ≤ P := le_trans (log_le_sub_one_of_pos hP0) (by linarith)
  have hl1 : log (14 * g) ≤ 4 * P := by
    have h14 : 14 * g ≤ P ^ 4 := by
      have hM12 : (1 : ℝ) ≤ M ^ 12 := one_le_pow₀ hM
      calc 14 * g ≤ 14 * (Q ^ 3 * M ^ 4) := by linarith
        _ ≤ Q * (Q ^ 3 * M ^ 4) * M ^ 12 := by
            have : (14 : ℝ) ≤ Q := le_trans (by norm_num) hQ
            have h0 : 0 ≤ Q ^ 3 * M ^ 4 := by positivity
            nlinarith [mul_le_mul_of_nonneg_left hM12 (mul_nonneg (by positivity : (0:ℝ) ≤ Q) h0)]
        _ = P ^ 4 := by rw [hPdef]; ring
    calc log (14 * g) ≤ log (P ^ 4) := log_le_log (by linarith) h14
      _ = 4 * log P := by rw [log_pow]; norm_num
      _ ≤ 4 * P := by linarith
  have hl2 : log d ≤ P := by
    have : d ≤ P := by
      calc d ≤ Q * M := hd
        _ ≤ Q * M ^ 4 := by
            gcongr
            calc M = M ^ 1 := (pow_one M).symm
              _ ≤ M ^ 4 := pow_le_pow_right₀ hM (by norm_num)
    linarith [log_le_log (by linarith) this]
  have hl3 : log (max hFJ (max (log d) 1)) ≤ 13 * P := by
    have hY : max hFJ (max (log d) 1) ≤ P ^ 13 := by
      have hP13 : P ≤ P ^ 13 := le_self_pow₀ (by linarith) (by norm_num)
      have hQM : Q ^ 13 * M ^ 24 ≤ P ^ 13 := by
        rw [hPdef, mul_pow, ← pow_mul]
        gcongr
        · norm_num
      refine max_le (hJ.trans hQM) (max_le ?_ ?_)
      · linarith [log_le_sub_one_of_pos (by linarith : (0:ℝ) < d)]
      · linarith
    calc log (max hFJ (max (log d) 1)) ≤ log (P ^ 13) :=
          log_le_log (lt_of_lt_of_le one_pos (le_max_of_le_right (le_max_right _ _))) hY
      _ = 13 * log P := by rw [log_pow]; norm_num
      _ ≤ 13 * P := by linarith
  have hg0 : 0 ≤ g := by linarith
  have hlog14 : 0 ≤ log (14 * g) := log_nonneg (by linarith)
  have hL' : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P)) := by
    refine hL.trans ?_
    gcongr
  have hg3 : g ^ 3 ≤ (Q ^ 3 * M ^ 4) ^ 3 := by gcongr
  have hg2' : g ^ 2 ≤ (Q ^ 3 * M ^ 4) ^ 2 := by gcongr
  have hL'' : L ≤ 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P) := by
    refine hL'.trans ?_
    have : 64 * g ^ 2 * (4 * P) + P + 2 * (13 * P) ≤
        64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P := by nlinarith
    have h0 : 0 ≤ 64 * g ^ 2 * (4 * P) + P + 2 * (13 * P) := by positivity
    calc 1024 * g ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P))
        ≤ 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * g ^ 2 * (4 * P) + P + 2 * (13 * P)) := by gcongr
      _ ≤ _ := by gcongr
  have hT : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * P) + 27 * P) ≤
      262144 * Q ^ 16 * M ^ 24 + 27648 * Q ^ 16 * M ^ 24 := by
    rw [hPdef]
    have hM8 : (1 : ℝ) ≤ M ^ 8 := one_le_pow₀ hM
    have hQ6 : (1 : ℝ) ≤ Q ^ 6 := one_le_pow₀ hQ1
    have e1 : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (64 * (Q ^ 3 * M ^ 4) ^ 2 * (4 * (Q * M ^ 4))) =
        262144 * Q ^ 16 * M ^ 24 := by ring
    have e2 : 1024 * (Q ^ 3 * M ^ 4) ^ 3 * (27 * (Q * M ^ 4)) = 27648 * (Q ^ 10 * M ^ 16) := by ring
    have e3 : Q ^ 10 * M ^ 16 ≤ Q ^ 16 * M ^ 24 := by
      have : Q ^ 16 * M ^ 24 = (Q ^ 10 * M ^ 16) * (Q ^ 6 * M ^ 8) := by ring
      rw [this]
      have h0 : 0 ≤ Q ^ 10 * M ^ 16 := by positivity
      nlinarith [one_le_mul_of_one_le_of_one_le hQ6 hM8]
    nlinarith [e1, e2, e3]
  have hlow : Q ^ 3 * M ^ 4 ≤ Q ^ 16 * M ^ 24 := by
    have h1 : (1 : ℝ) ≤ Q ^ 13 := one_le_pow₀ hQ1
    have h2 : (1 : ℝ) ≤ M ^ 20 := one_le_pow₀ hM
    have : Q ^ 16 * M ^ 24 = (Q ^ 3 * M ^ 4) * (Q ^ 13 * M ^ 20) := by ring
    rw [this]
    have h0 : 0 ≤ Q ^ 3 * M ^ 4 := by positivity
    nlinarith [one_le_mul_of_one_le_of_one_le h1 h2]
  have hJ' : Q ^ 13 * M ^ 24 ≤ Q ^ 16 * M ^ 24 := by
    have : Q ^ 13 ≤ Q ^ 16 := pow_le_pow_right₀ hQ1 (by norm_num)
    gcongr
  have hfin : Q ^ 16 * M ^ 24 * 10 ^ 12 ≤ Q ^ 17 * M ^ 24 := by
    have : Q ^ 17 * M ^ 24 = Q ^ 16 * M ^ 24 * Q := by ring
    rw [this]; gcongr
  have hT0 : 0 ≤ Q ^ 16 * M ^ 24 := by positivity
  nlinarith

/-- **E2-E4 arithmetic from the level** (N5 L868-905): from the conductor bound `N ≤ QM²` (D5),
Javanpeykar's bound at `X₁(N)` (`h_F(J) ≤ 1.3·10⁷ N¹²`, `2 ≤ g ≤ N²`), `[L':ℚ] ≤ QM`, the
Gaudron–Rémond degree bound, Faltings' height variation with additivity, and Bost's lower bound
`h_F(Z) ≥ −(3/2)·dim Z` with `dim Z ≤ g`, conclude `h_F(A) ≤ Q¹⁷M²⁴`. -/
theorem transfer_of_level {Q M N g d hFJ L hA hZ : ℝ} (hQ : 10 ^ 12 ≤ Q) (hM : 1 ≤ M)
    (hN1 : 1 ≤ N) (hN : N ≤ Q * M ^ 2) (hJav : hFJ ≤ 13000000 * N ^ 12)
    (hg2 : 2 ≤ g) (hg : g ≤ N ^ 2) (hd1 : 1 ≤ d) (hd : d ≤ Q * M)
    (hL : L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))))
    (hvar : hA + hZ ≤ hFJ + L / 2) (hBost : -(3 / 2) * g ≤ hZ) :
    hA ≤ Q ^ 17 * M ^ 24 := by
  have hQ1 : (1 : ℝ) ≤ Q := le_trans (by norm_num) hQ
  have hN0 : 0 ≤ N := by linarith
  have hN12 : N ^ 12 ≤ Q ^ 12 * M ^ 24 := by
    calc N ^ 12 ≤ (Q * M ^ 2) ^ 12 := by gcongr
      _ = Q ^ 12 * M ^ 24 := by ring
  have hJ : hFJ ≤ Q ^ 13 * M ^ 24 := by
    have h0 : 0 ≤ Q ^ 12 * M ^ 24 := by positivity
    calc hFJ ≤ 13000000 * N ^ 12 := hJav
      _ ≤ 13000000 * (Q ^ 12 * M ^ 24) := by gcongr
      _ ≤ Q * (Q ^ 12 * M ^ 24) := by gcongr; linarith
      _ = Q ^ 13 * M ^ 24 := by ring
  have hg' : g ≤ Q ^ 3 * M ^ 4 := by
    calc g ≤ N ^ 2 := hg
      _ ≤ (Q * M ^ 2) ^ 2 := by gcongr
      _ = Q ^ 2 * M ^ 4 := by ring
      _ ≤ Q ^ 3 * M ^ 4 := by
          have : Q ^ 2 ≤ Q ^ 3 := pow_le_pow_right₀ hQ1 (by norm_num)
          gcongr
  exact transfer_numerics hQ hM hg2 hg' hd1 hd hJ hL hvar (by linarith)

/-! ### CM branch (N5 L581-631): `h_F(A) ≤ C_cm` -/

theorem log_two_mul_bcm_le {D : ℝ} (hD : 1 ≤ D) (n : ℕ) (hn : (n : ℝ) = 21000 * D ^ 2) :
    log (2 * (D ^ 2 * 3 ^ n + 1)) ≤ 2 + 2 * D + 42000 * D ^ 2 := by
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hD2 : (1 : ℝ) ≤ D ^ 2 := one_le_pow₀ hD
  have hle : 2 * (D ^ 2 * 3 ^ n + 1) ≤ 4 * (D ^ 2 * 3 ^ n) := by nlinarith
  have hpos : 0 < 2 * (D ^ 2 * 3 ^ n + 1) := by positivity
  have hlog4 : log 4 ≤ 2 := by
    have : (4 : ℝ) ≤ exp 2 := by
      have := add_one_le_exp (2 : ℝ)
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      nlinarith
    calc log 4 ≤ log (exp 2) := log_le_log (by norm_num) this
      _ = 2 := log_exp 2
  have hlog3 : log 3 ≤ 2 := by
    have : (3 : ℝ) ≤ exp 2 := by
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      nlinarith
    calc log 3 ≤ log (exp 2) := log_le_log (by norm_num) this
      _ = 2 := log_exp 2
  have hlogD : log D ≤ D := le_trans (log_le_sub_one_of_pos (by linarith)) (by linarith)
  calc log (2 * (D ^ 2 * 3 ^ n + 1)) ≤ log (4 * (D ^ 2 * 3 ^ n)) := log_le_log hpos hle
    _ = log 4 + 2 * log D + n * log 3 := by
        rw [log_mul (by norm_num) (by positivity), log_mul (by positivity) (by positivity),
          log_pow, log_pow]
        push_cast; ring
    _ ≤ 2 + 2 * D + 42000 * D ^ 2 := by
        rw [hn]
        have : 21000 * D ^ 2 * log 3 ≤ 21000 * D ^ 2 * 2 := by gcongr
        linarith

/-- **CM-branch arithmetic** (N5 L606-628): `h_F(E) ≤ B_cm`, `[L:ℚ] ≤ D`, Gaudron–Rémond with
source `E²` (`g = 2`: exponent `1024·2³ = 8192`, `(14·2)^{64·2²} = 28^{256}`), height variation
and additivity give `h_F(A) ≤ C_cm = 2B_cm + 4096(1028 + 5D + 84000D²)`. -/
theorem cm_numerics {D d hE L hA : ℝ} (n : ℕ) (hn : (n : ℝ) = 21000 * D ^ 2) (hD : 1 ≤ D)
    (hd1 : 1 ≤ d) (hd : d ≤ D) (hEB : hE ≤ D ^ 2 * 3 ^ n + 1)
    (hL : L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))))
    (hvar : hA ≤ 2 * hE + L / 2) :
    hA ≤ 2 * (D ^ 2 * 3 ^ n + 1) + 4096 * (1028 + 5 * D + 84000 * D ^ 2) := by
  set B := D ^ 2 * 3 ^ n + 1 with hB
  have h3 : (1 : ℝ) ≤ 3 ^ n := one_le_pow₀ (by norm_num)
  have hD2 : D ≤ D ^ 2 := by nlinarith
  have hBD : D ≤ B := by rw [hB]; nlinarith
  have hlogd : log d ≤ D := le_trans (log_le_sub_one_of_pos (by linarith)) (by linarith)
  have hmax : max (2 * hE) (max (log d) 1) ≤ 2 * B :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  have hlogmax : log (max (2 * hE) (max (log d) 1)) ≤ 2 + 2 * D + 42000 * D ^ 2 :=
    (log_le_log (lt_of_lt_of_le one_pos (le_max_of_le_right (le_max_right _ _))) hmax).trans
      (log_two_mul_bcm_le hD n hn)
  have hlog28 : log 28 ≤ 4 := by
    have : (28 : ℝ) ≤ exp 4 := by
      have h4 : exp 4 = (exp 1) ^ 4 := by rw [← exp_nat_mul]; norm_num
      have he := exp_one_gt_d9
      rw [h4]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 4]
    calc log 28 ≤ log (exp 4) := log_le_log (by norm_num) this
      _ = 4 := log_exp 4
  have : L ≤ 8192 * (1028 + 5 * D + 84000 * D ^ 2) := by
    refine hL.trans ?_
    nlinarith
  linarith

/-! ### F3: Pazuki's bound in N5's normalization (N5 L934-947) -/

theorem log_sixteen_le : log (2 ^ 4 : ℝ) ≤ 3 := by
  have : (2 ^ 4 : ℝ) ≤ exp 3 := by
    have h3 : exp 3 = (exp 1) ^ 3 := by rw [← exp_nat_mul]; norm_num
    have he := exp_one_gt_d9
    rw [h3]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 3]
  calc log (2 ^ 4 : ℝ) ≤ log (exp 3) := log_le_log (by norm_num) this
    _ = 3 := log_exp 3

/-- **F3 arithmetic.** From Pazuki's Cor. 1.3(2) for `g = 2`, `r = 2` in the Deligne metric,
`h_Θ ≤ X_D/2 + C₂ log(X_D + 2)` with `X_D = max(1, h_F(A) + log π)` and
`C₂ = 1000·2⁴·(log 2⁴)⁵`, conclude `h ≤ 10⁴·2²⁴·max(1, h_F(A))`. -/
theorem pazuki_numerics {hz hA : ℝ}
    (hP : hz ≤ max 1 (hA + log π) / 2 +
      1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (hA + log π) + 2)) :
    hz ≤ 10000 * 2 ^ 24 * max 1 hA := by
  set X := max 1 hA with hX
  set XD := max 1 (hA + log π) with hXD
  have hX1 : 1 ≤ X := le_max_left _ _
  have hlogpi : log π ≤ 2 := by
    have : π ≤ exp 2 := by
      have h2 : exp 2 = exp 1 * exp 1 := by rw [← exp_add]; norm_num
      have he := exp_one_gt_d9
      have hpi := pi_lt_d2
      nlinarith
    calc log π ≤ log (exp 2) := log_le_log pi_pos this
      _ = 2 := log_exp 2
  have hXD1 : 1 ≤ XD := le_max_left _ _
  have hXD3 : XD ≤ 3 * X := by
    refine max_le (by linarith) ?_
    have : hA ≤ X := le_max_right _ _
    linarith
  have hlogXD : log (XD + 2) ≤ 2 * XD := by
    have := log_le_sub_one_of_pos (by linarith : (0 : ℝ) < XD + 2)
    linarith
  have hC0 : 0 ≤ log (2 ^ 4 : ℝ) := log_nonneg (by norm_num)
  have hC : (log (2 ^ 4 : ℝ)) ^ 5 ≤ 243 := by
    calc (log (2 ^ 4 : ℝ)) ^ 5 ≤ 3 ^ 5 := pow_le_pow_left₀ hC0 log_sixteen_le 5
      _ = 243 := by norm_num
  have hlog0 : 0 ≤ log (XD + 2) := log_nonneg (by linarith)
  have h1 : 1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (XD + 2) ≤ 1000 * 2 ^ 4 * 243 * (6 * X) := by
    have : log (XD + 2) ≤ 6 * X := by linarith
    gcongr
  have h2 : XD / 2 ≤ 3 * X / 2 := by linarith
  have h3 := hP.trans (add_le_add h2 h1)
  have h4 : 3 * X / 2 + 1000 * 2 ^ 4 * 243 * (6 * X) ≤ 10000 * 2 ^ 24 * X := by nlinarith
  exact h3.trans h4

end GlueAssembly
