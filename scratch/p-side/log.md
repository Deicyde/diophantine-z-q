# p-side results log

## P1 — ZInQKernel/Contrib/PSide/APZero.lean (compiles, no sorry; VERIFIED)
- `card_solutions_eq` : over a finite field of odd char, #{(x,y): y²=g x} = #F + Σ_x χ(g x).
- `charSum_odd_eq_zero` : χ(−1) = −1 and g odd ⇒ Σ χ(g x) = 0.
- `LFunction_cd_apply_prime_eq_neg_charSum` : a_p(C_d) = −Σ_x χ(x³ − d²x)  (d odd sqfree, p ∤ 2d).
- `LFunction_cd_apply_prime_of_mod_four_eq_three` : p ≡ 3 (4), p ∤ 2d ⇒ a_p(C_d) = 0.  [P1]
- `natCard_point_cd_of_mod_four_eq_three` : #C_d(F_p) = p + 1.  [P1, point-count form]
- `LFunction_cd_apply_prime_of_mod_four_eq_three'` : same with hypothesis p ∤ d.

## P2 — ZInQKernel/Contrib/PSide/Coeff.lean (compiles, no sorry; VERIFIED)
For every d (no hypothesis) unless noted:
- `cdCoeff_zero`, `cdCoeff_one`; `cdArith d : ArithmeticFunction ℤ`, `isMultiplicative_cdArith`.
- `cdCoeff_mul` : Coprime m n → c(mn) = c(m) c(n).
- `cdCoeff_prime_pow` : c(p^k) = [T^k] 1/cdEulerPoly d p.
- `cdCoeff_prime` : c(p) = if p ∣ 2d then 0 else p + 1 − #C_d(F_p).
- `cdEulerPoly_of_not_dvd` : cdEulerPoly d p = 1 − c(p) T + p T² for p ∤ 2d.
- `cdCoeff_prime_pow_succ_succ` : p ∤ 2d ⇒ c(p^{k+2}) = c(p) c(p^{k+1}) − p c(p^k).
- `cdCoeff_prime_pow_of_dvd` : p ∣ 2d, k ≠ 0 ⇒ c(p^k) = 0; `cdCoeff_eq_zero_of_dvd` (p ∣ 2d, p ∣ n ⇒ c(n) = 0); `cdCoeff_eq_zero_of_even`.
- d odd sqfree: `LFunction_cd_eq_cdCoeff` (Mathlib LFunction n = cdCoeff d n, all n), `LFunction_cd_prime_pow_succ_succ` (recursion on Mathlib's coefficients).

## P3 — ZInQKernel/Contrib/PSide/BadPrimes.lean (compiles, no sorry; VERIFIED)
- `cuspEquiv F : F ≃ {(x,y) : y² = x³}` (t ↦ (t², t³)); `natCard_cusp`.
- `natCard_cd_of_dvd` : p ∣ d ⇒ #{y² = x³ − d²x over F_p} = p.
- `natCard_cd_two` : d odd ⇒ #{y² = x³ − d²x over F_2} = 2 (decide).
- `LFunction_cd_apply_prime_eq_sub_card_of_dvd` : d odd sqfree, p ∣ 2d ⇒ a_p = p − N_p (= 0).  [P3]
- `LFunction_cd_apply_prime_eq_sub_card_all` : d odd sqfree, every prime p ⇒ a_p = p − N_p.

## P5 — ZInQKernel/Contrib/PSide/TYZInputsIff.lean (compiles, no sorry; VERIFIED)
- `ReadingAAt n` := (∃F, IsLContinuation (C_n) F ∧ analyticOrderAt F 1 ≤ 1) ∨ (T5aCl n = 0 ∧ T5bCl n = 0).
- `parity_sums_eq` : L ≡ Λ mod 2 on classes 1,3 ⇒ finalStep's parity sums = T5aCl n, T5bCl n.
- `tyzInputs_iff` : TYZInputs ↔ ∀ n ≡ 5 (8) sqfree, ReadingAAt n.   [P5]
  backward choice: L = Λ.val on classes 1,3; 1/0 on class 5 by existence of a cont. of order ≤ 1; 0 else.
- `tyzInputs_iff_readingA` : TYZInputs ↔ TYZThm35ReadingA ∧ ∀ n, (∃ cont) ∨ (T5a = T5b = 0)  (no hypothesis).
- `tyzInputs_iff_readingA_of_hecke` : HeckeContinuation → (TYZInputs ↔ TYZThm35ReadingA).
- `tyzInputs_of_readingA` : TYZThm35ReadingA → HeckeContinuation → TYZInputs.
- Axioms (scratch/p-side/Axioms.lean, `lake env lean`): all P1/P2/P3/P5 headline theorems depend on
  [propext, Classical.choice, Quot.sound] only. VERIFIED.

## P4a — ZInQKernel/Contrib/PSide/Hasse.lean (compiles, no sorry; VERIFIED)
Over any finite field F, ringChar F ≠ 2, χ = quadraticChar F, jac a := Σ_x χ(x(x²+a)):
- `jac_mul_sq` : t ≠ 0 ⇒ jac(a t²) = χ(t) jac(a);  `jac_sq_mul_sq`.
- `sum_char_mul_add` : Σ_a χ((a+u)(a+v)) = if u = v then q−1 else −1 (via Mathlib `jacobiSum_nontrivial_inv`).
- `sum_jac_sq` : Σ_a jac(a)² = q(q−1)(1+χ(−1)).
- `sum_sq_le_two_mul` : G ≥ 0 ⇒ Σ_t G(t²) ≤ 2 Σ_c G(c).
- `jac_sq_le_four_mul` : a ≠ 0 ⇒ jac(a)² ≤ 4q.
For C_d:
- `cdCoeff_prime_eq_neg_jac` : p ∤ 2d ⇒ c_p = −jac(−d²) (any d).
- `cdCoeff_prime_sq_le` : every prime p, every d: c_p² ≤ 4p.   [Hasse for C_d]
- `LFunction_cd_prime_sq_le` : d odd sqfree: (Mathlib a_p)² ≤ 4p.

## P4b — ZInQKernel/Contrib/PSide/Convergence.lean (compiles, no sorry; VERIFIED)
- `recurrence_bound` : u₀ = 1, u₁ = a, u_{k+2} = a u_{k+1} − r² u_k, a² ≤ 4r², r ≥ 0 ⇒ |u_k| ≤ (k+1) r^k
  (u_k = Σ α^i β^{k−i}, α,β = (a ± i√(4r²−a²))/2, |α| = |β| = r).
- `cdCoeff_prime_pow_sq_le` : every prime p, every d: c(p^k)² ≤ (k+1)² p^k.
- `cdCoeff_sq_le` : every n, d: c(n)² ≤ σ₀(n)² n.
- `convolution_one_one` : (1 ⍟ 1) n = σ₀(n).
- `LSeriesSummable_cdCoeff` : every d, 3/2 < Re s ⇒ LSeriesSummable (cdCoeff d) s.
- d odd sqfree: `LSeriesSummable_cd` (Mathlib's L(C_d,s) absolutely convergent on Re s > 3/2),
  `abscissaOfAbsConv_cd_le` (≤ 3/2), `differentiableOn_LSeries_cd` (holomorphic on Re s > 3/2).
- Axioms of all P4 headline theorems: [propext, Classical.choice, Quot.sound]. VERIFIED.

## Ground-truth sample (scratch/p-side/check_pari.py; PARI ellan, 30 inputs, d = 5, n = 1..30) — VERIFIED
- a_n(C_5) = [1,0,0,0,0,0,0,0,-3,0,0,0,-6,0,0,0,-2,0,0,0,0,0,0,0,0,0,0,0,-10,0];
  a_p = −Σχ(x³−25x) at p ∤ 10, a_p = 0 at p ≡ 3 (4) and p | 10, a_n² ≤ σ₀(n)² n: all pass.

## Supplement — ZInQKernel/Contrib/PSide/Supersingular.lean (compiles, no sorry; VERIFIED)
- `cdCoeff_prime_of_mod_four_eq_three` : p ≡ 3 (4), p ∤ 2d ⇒ c_p = 0 (every d).
- `cdCoeff_prime_pow_of_mod_four_eq_three` : c(p^{2k}) = (−p)^k, c(p^{2k+1}) = 0.
- `LFunction_cd_prime_pow_of_mod_four_eq_three` : same on Mathlib's coefficients (d odd sqfree).

## Final check
- `lake build` of the 7 Contrib/PSide modules: Build completed successfully, 0 errors; 0 `sorry`.
- scratch/p-side/Axioms.lean → scratch/p-side/axioms-output.txt: 22 headline theorems, all
  [propext, Classical.choice, Quot.sound]. VERIFIED.
- Imports: only baseline files (RouteK/Rank/LFunctionCd, RouteK/PropN), Mathlib, own files. Nothing imports them.
