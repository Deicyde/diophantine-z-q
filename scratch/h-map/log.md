# h-map log

## Step 1. Lean consumers of SixContactMin (VERIFIED by reading source, commit d549dabb)
- SixContactMin (Hypotheses/HeightMin.lean): ∀ u ∈ ℚ \ 𝒞, h(u) ≤ H₆(D)·M_{S_mul}(u)^24, 𝒞={0,-15,-20,-24,-30,-60}.
  H₆(D)=A0=2·10^13·max(1,C_cm,(D^(D E0))^17), D=324!·3^(256·324!^4).
- Consumer 1 (precision / main branch): Assembly/Top/MainBranch.lean ratHeight_le_bound_of_test:
  t with Test(n,κ,t) has M_{S_ht}(t) | κF(n) (test_dvd); H at S_ht (via M_{S_mul}≤M_{S_ht}) gives
  h(t) ≤ A0|κF(n)|^24 = 𝓑(n,κ); then |t-n|<e^{-𝓑} forces t=n (eq_int_of_real_abs_sub_lt_exp_neg_of_height_le).
- Consumer 2 (multiplication soundness): Multiplication/Soundness/ContactSupport.lean slope_height_le:
  slope t with SlopePred has M_{S_mul}(t)^25 | f = n1n2-n3 (local congruence), so h(t) ≤ A_ht|f|^{24/25};
  FiniteBox.finite_box_of_heights: N^2 < 24 A N^{48/25}+10 ⇒ |n_i| < (48A)^13 = T.
  A_ht = H₆(R), R=max(D,H_max,c_*,10^12) ≥ D (monotone).
- Frozen target: ∃ P in 292890231905 vars, totdeg < 2↑↑7, |coeff| < 2↑↑8, defining ℤ in ℚ.
