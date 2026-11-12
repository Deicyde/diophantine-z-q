/-!
# The assembly: from the numerical outputs of E2-E4, F1, F3 to `SixContactMinAt S`

`GlueOutputs S` is a conjunction, for every `u ∉ 𝒞`, of the numerical outputs that steps
A1-E1 (modularity half), E2-E4 (Javanpeykar, Gaudron–Rémond, Faltings, Bost), F1 (the theta
expression of `j`) and F3 (Pazuki) give. Lean checks the assembly: F2 (`logHeight_Phi_le`, over
Mathlib's Weil height), the invariance of the height of a rational number in a number field
(`logHeight₁_algebraMap_rat`), the E-arithmetic (`transfer_of_level`, `cm_numerics`), the
F3-arithmetic (`pazuki_numerics`), F4 (`twelve_mul_ratHeight_le`) and the final constant.

`GlueOutputs S` is NOT a faithful statement of the literature theorems: the abelian varieties and
their Faltings heights do not exist in Mathlib, so they appear only as real numbers with the
inequalities the theorems give. As a Lean Prop it is a height bound in disguise (wk-h §4.3).
What is faithful is the theta point: a genuine point of `K¹⁰` with its genuine Weil height.
-/

namespace GlueAssembly

open Real ZInQ Height

/-- A bundled number field. -/
structure NF where
  K : Type
  [fld : Field K]
  [nf : NumberField K]

attribute [instance] NF.fld NF.nf

/-- **Outputs of the non-CM transfer (A1-E1, E2, E3, E4)**, for `Q = Q_D`, `M = M_S(u)`, and
`hA` the stable Faltings height of `A`: a level `N` with `1 ≤ N ≤ QM²` (D5); `g = dim J₁(N)`
with `2 ≤ g ≤ N²` and `h_F(J₁(N)) ≤ 1.3·10⁷ N¹²` (Javanpeykar, `g, deg_B ≤ N²`); `d = [L':ℚ]`
with `1 ≤ d ≤ QM` (B3); `L = log deg φ` for the Gaudron–Rémond isogeny `J₁(N) → A × Z` (E1,
E3); `h_F(A) + h_F(Z) ≤ h_F(J₁(N)) + L/2` (Faltings' Lemma 5 and additivity) and
`h_F(Z) ≥ −(3/2)g` (Bost, `dim Z ≤ g`). -/
def NonCMOutput (Q M hA : ℝ) : Prop :=
  ∃ N g d hFJ L hZ : ℝ, 1 ≤ N ∧ N ≤ Q * M ^ 2 ∧ hFJ ≤ 13000000 * N ^ 12 ∧
    2 ≤ g ∧ g ≤ N ^ 2 ∧ 1 ≤ d ∧ d ≤ Q * M ∧
    L ≤ 1024 * g ^ 3 * (64 * g ^ 2 * log (14 * g) + log d +
      2 * log (max hFJ (max (log d) 1))) ∧
    hA + hZ ≤ hFJ + L / 2 ∧ -(3 / 2) * g ≤ hZ

/-- **Outputs of the CM branch (N5 L581-628)**: `d = [L:ℚ] ≤ D`, `h_F(E) ≤ B_cm`, `L = log deg`
of the Gaudron–Rémond isogeny `E² → A`, and `h_F(A) ≤ 2h_F(E) + L/2`. -/
def CMOutput (hA : ℝ) : Prop :=
  ∃ d hE L : ℝ, 1 ≤ d ∧ d ≤ heightD ∧ hE ≤ heightBcm ∧
    L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))) ∧
    hA ≤ 2 * hE + L / 2

/-- **Output of F3 (Pazuki, Cor. 1.3(2), `g = r = 2`, Deligne metric)** for the absolute
sup-norm height `hz` of the even theta nulls. -/
def PazukiOutput (hz hA : ℝ) : Prop :=
  hz ≤ max 1 (hA + log π) / 2 +
    1000 * 2 ^ 4 * (log (2 ^ 4)) ^ 5 * log (max 1 (hA + log π) + 2)

/-- **The glue interface.** For every `u ∉ 𝒞`: a number field `K`, the ten even theta nulls
`z ∈ K¹⁰` of the QM surface `A` over `J(u)` (F1: `Φ(z) = J(u)`), the Faltings height `hA` of
`A`, Pazuki's bound for the absolute Weil height `h(z) = h_K(z)/[K:ℚ]` (F3), and the outputs of
either the non-CM transfer (at `Q = Q_D`, `M = M_S(u)`) or the CM branch. -/
def GlueOutputs (S : Finset ℕ) : Prop :=
  ∀ u : ℚ, u ∉ contactSet → ∃ (K : NF) (z : Fin 10 → K.K) (hA : ℝ),
    3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K.K (Jmap u) ∧
    PazukiOutput (logHeight z / Module.finrank ℚ K.K) hA ∧
    (NonCMOutput (heightQ heightD) (contactSupport S u) hA ∨ CMOutput hA)

/-- `Q_D ≥ D ≥ 10¹²`. -/
theorem heightQ_heightD_ge : (10 : ℝ) ^ 12 ≤ heightQ heightD := by
  have hD : (10 : ℝ) ^ 12 ≤ heightD := by
    exact_mod_cast ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hD1 : (1 : ℝ) ≤ heightD := le_trans (by norm_num) hD
  have hDpos : 0 < heightD := by
    have := ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
    omega
  have hE : (1 : ℝ) ≤ heightE0 := by
    have : 1 ≤ heightE0 := by
      rw [ZInQ.Compiler.Precision.heightE0_eq]
      have hG : 0 < heightG0 := by unfold heightG0; norm_num
      have := Nat.mul_pos hDpos hG
      have := pow_pos this 2
      omega
    exact_mod_cast this
  have h1 : (1 : ℝ) ≤ (heightD : ℝ) * heightE0 := one_le_mul_of_one_le_of_one_le hD1 hE
  calc (10 : ℝ) ^ 12 ≤ heightD := hD
    _ = (heightD : ℝ) ^ (1 : ℝ) := (rpow_one _).symm
    _ ≤ (heightD : ℝ) ^ ((heightD : ℝ) * heightE0) := rpow_le_rpow_of_exponent_le hD1 h1
    _ = heightQ heightD := rfl

/-- Casting `C_cm`'s defining equation, over variables (the kernel cannot unfold the constants;
see `ZInQKernel/Compiler/Precision/HeightConstant.lean`). -/
theorem cast_ccm {C B D : ℕ} (h : C = 2 * B + 4096 * (1028 + 5 * D + 84000 * D ^ 2)) :
    (C : ℝ) = 2 * (B : ℝ) + 4096 * (1028 + 5 * (D : ℝ) + 84000 * (D : ℝ) ^ 2) := by
  rw [h]; push_cast; ring

/-- The CM branch over variables: `h_F(A) ≤ C_cm` (applied to the constants through their
defining equations only). -/
theorem cm_branch_nat {D B C : ℕ} (hBe : B = D ^ 2 * 3 ^ (21000 * D ^ 2) + 1)
    (hCe : C = 2 * B + 4096 * (1028 + 5 * D + 84000 * D ^ 2)) (hD : 1 ≤ D) {d hE L hA : ℝ}
    (hd1 : 1 ≤ d) (hd : d ≤ D) (hEB : hE ≤ B)
    (hL : L ≤ 8192 * (256 * log 28 + log d + 2 * log (max (2 * hE) (max (log d) 1))))
    (hvar : hA ≤ 2 * hE + L / 2) : hA ≤ C := by
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hB : (B : ℝ) = (D : ℝ) ^ 2 * 3 ^ (21000 * D ^ 2) + 1 := by rw [hBe]; push_cast; ring
  have hnR : ((21000 * D ^ 2 : ℕ) : ℝ) = 21000 * (D : ℝ) ^ 2 := by push_cast; ring
  have hcm := cm_numerics (21000 * D ^ 2) hnR hD1 hd1 hd (hEB.trans (le_of_eq hB)) hL hvar
  rw [cast_ccm hCe, hB]
  exact hcm

theorem one_le_heightD_real : (1 : ℝ) ≤ heightD := by
  have : (10 : ℝ) ^ 12 ≤ heightD := by
    exact_mod_cast ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  linarith

/-- Non-CM half of the E-part: `max(1, h_F(A)) ≤ X(D)·M²⁴`. -/
theorem max_one_hA_le_noncm {M hA : ℝ} (hM : 1 ≤ M) (h : NonCMOutput (heightQ heightD) M hA) :
    hA ≤ heightX heightD * M ^ 24 := by
  obtain ⟨N, g, d, hFJ, L, hZ, hN1, hN, hJav, hg2, hg, hd1, hd, hL, hvar, hBost⟩ := h
  have h1 := transfer_of_level heightQ_heightD_ge hM hN1 hN hJav hg2 hg hd1 hd hL hvar hBost
  have hQX : heightQ heightD ^ 17 ≤ heightX heightD :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hM24 : 0 ≤ M ^ 24 := by positivity
  exact h1.trans (mul_le_mul_of_nonneg_right hQX hM24)

/-- CM half of the E-part. -/
theorem max_one_hA_le_cm {M hA : ℝ} (hM : 1 ≤ M) (h : CMOutput hA) :
    hA ≤ heightX heightD * M ^ 24 := by
  obtain ⟨d, hE, L, hd1, hd, hEB, hL, hvar⟩ := h
  have hDn : 1 ≤ heightD := le_trans (by norm_num) ZInQ.Compiler.Precision.ten_pow_twelve_le_heightD
  have hcm := cm_branch_nat ZInQ.Compiler.Precision.heightBcm_eq
    ZInQ.Compiler.Precision.heightCcm_eq hDn hd1 hd hEB hL hvar
  have hCX : (heightCcm : ℝ) ≤ heightX heightD :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hX1 : 0 ≤ heightX heightD := le_trans zero_le_one (le_max_left _ _)
  have hM24 : 1 ≤ M ^ 24 := one_le_pow₀ hM
  calc hA ≤ heightCcm := hcm
    _ ≤ heightX heightD := hCX
    _ ≤ heightX heightD * M ^ 24 := le_mul_of_one_le_right hX1 hM24

/-- The E-part of the assembly: `max(1, h_F(A)) ≤ X(D)·M²⁴` in both branches (N5 L903-905). -/
theorem max_one_hA_le {M hA : ℝ} (hM : 1 ≤ M)
    (h : NonCMOutput (heightQ heightD) M hA ∨ CMOutput hA) :
    max 1 hA ≤ heightX heightD * M ^ 24 := by
  have hM24 : 1 ≤ M ^ 24 := one_le_pow₀ hM
  have hX1 : 1 ≤ heightX heightD := le_max_left _ _
  refine max_le (le_trans hX1 (le_mul_of_one_le_right (by linarith) hM24)) ?_
  rcases h with h | h
  · exact max_one_hA_le_noncm hM h
  · exact max_one_hA_le_cm hM h

theorem log_3779136_le : log 3779136 ≤ 16 := by
  have : (3779136 : ℝ) ≤ exp 16 := by
    have h : exp 16 = (exp 1) ^ 16 := by rw [← exp_nat_mul]; norm_num
    have he := exp_one_gt_d9
    rw [h]; nlinarith [pow_le_pow_left₀ (by norm_num) he.le 16]
  calc log 3779136 ≤ log (exp 16) := log_le_log (by norm_num) this
    _ = 16 := log_exp 16

/-- **F1 + F2 + invariance**: if `Φ(z) = j` for `j ∈ ℚ`, then
`h(j) ≤ 40·h_K(z)/[K:ℚ] + log 3779136`. -/
theorem ratHeight_le_of_theta {K : Type} [Field K] [NumberField K] (z : Fin 10 → K) (j : ℚ)
    (hF1 : 3779136 * (∏ i, z i) ^ 4 / (∑ i, z i ^ 8) ^ 5 = algebraMap ℚ K j) :
    ratHeight j ≤ 40 * (logHeight z / Module.finrank ℚ K) + log 3779136 := by
  have h2 := logHeight₁_Phi_le z
  rw [hF1, logHeight₁_algebraMap_rat, NumberField.totalWeight_eq_finrank] at h2
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  unfold ratHeight
  set n : ℝ := (Module.finrank ℚ K : ℝ)
  set L := log (max |(j.num : ℝ)| (j.den : ℝ))
  calc L = (n * L) / n := by field_simp
    _ ≤ (40 * logHeight z + n * log 3779136) / n := div_le_div_of_nonneg_right h2 hn.le
    _ = 40 * (logHeight z / n) + log 3779136 := by field_simp

/-- **The assembly.** `GlueOutputs S → JHeightBound S`. -/
theorem jHeightBound_of_glueOutputs {S : Finset ℕ} (h : GlueOutputs S) : JHeightBound S := by
  intro u hu
  obtain ⟨K, z, hA, hF1, hPaz, hE⟩ := h u hu
  have hM : (1 : ℝ) ≤ contactSupport S u := by exact_mod_cast contactSupport_pos S u
  set Y := heightX heightD * (contactSupport S u : ℝ) ^ 24 with hY
  have hXM : max 1 hA ≤ Y := max_one_hA_le hM hE
  have hz := pazuki_numerics hPaz
  have hj := ratHeight_le_of_theta z (Jmap u) hF1
  have hY1 : 1 ≤ Y := (le_max_left 1 hA).trans hXM
  have hlog := log_3779136_le
  have : ratHeight (Jmap u) ≤ (40 * 10000 * 2 ^ 24 + 22 : ℝ) * Y := by nlinarith
  rw [hY] at this
  linarith

/-- **H from the glue interface.** `GlueOutputs S → SixContactMinAt S`; at `S = Mult.S_mul`
the conclusion is `ZInQ.SixContactMin`. -/
theorem sixContactMinAt_of_glueOutputs {S : Finset ℕ} (h : GlueOutputs S) :
    SixContactMinAt S :=
  sixContactMinAt_of_jHeightBound (jHeightBound_of_glueOutputs h)

end GlueAssembly
