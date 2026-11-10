# pd-lean-2 report: Proposition D, files 3–6 and 9 (Abel, Residues, PrimeTail, Lattice, PropD)

Every leaf is proved. `lake build ZInQKernel` succeeds. There is no `sorry`, `axiom`,
`native_decide`, `implemented_by` or `extern` in the new files. `#print axioms` on
`goodPrimeDensity_of_uniformBadBound`, `goodPrimeDensity`, `goodPrimeAP_of_greenTaoDense'` and
`goodPrimeAP_of_greenTaoDense_uniformBadBound` reports `[propext, Classical.choice, Quot.sound]`.

Everything is in namespace `ZInQ.Density`, in `ZInQKernel/Density/{Abel,PrimeTail,Lattice,Residues,
PropD,PropDFinal}.lean` (about 1430 lines). The root module is `ZInQKernel/DensityMain.lean`, and
`ZInQKernel.lean` gains `import ZInQKernel.DensityMain`. The branch merges `origin/wip/pd-paper`,
`origin/wip/pd-lean-1` (for `InClass`, `cp`, `cp_odd`, `exists_sq_add_sq`, `goodSlopePrime_of_gcd`,
`mod_four_of_dvd_cp`) and `origin/wip/pd-sieve` (for `uniformBadBound`). The referee report
(rv-pd-paper) asked for no repair to files 3–6 or 9. I followed its remark F5 in Lemma 3.1.

**Result.** With pd-sieve's `uniformBadBound`, `ZInQ.GoodPrimeDensity` is now a theorem
(`ZInQ.Density.goodPrimeDensity`). So `GoodPrimeAP` follows from `GreenTaoDense` alone
(`goodPrimeAP_of_greenTaoDense'`).

## Leaves

Article paths refer to `docs/research/pd-paper.md` (this task has no blueprint leaf list).

| article (pd-paper.md) | Lean name | status |
| --- | --- | --- |
| §5 notation `θ_S`, `Φ_S` | `thetaS`, `phiTerm`, `PhiS` (defs) | defined |
| Lemma 5.2(1) (Abel summation) | `abel_summation`, `abel_partial_sum_le`, `abel_bound` | proved |
| Lemma 5.2, auxiliary | `sum_one_div_rpow_le` (`Σ_{n≤M} n^{−x} ≤ x/(x − 1)`), `thetaS_le_log_mul_card`, `thetaS_le_of_eventually`, `thetaS_le_log4`, `summable_phiTerm` | proved |
| Proposition 5.3 | `primesRelUpperDensityPos_of_dirichlet` | proved |
| §2.1 `Q_L`, `M_L`, `A_L`, `C_L` | `QL`, `modSet`, `ML`, `crt`, `cond`, `AL`, `CL` (defs); `ML_eq` | defined |
| §2.1 remark 3 (CRT count) | `card_AL` (`#A_L = 3∏(ℓ − 2)`), `totient_ML` (`φ(M_L) = 24∏(ℓ − 1)`), `deltaL_eq` | proved |
| §2.1 remark 3 (main term) | `deltaL_ge` (`δ_L ≥ 3/(8(L − 1))`, `L ≥ 4`) | proved |
| §3.2 units, class | `isUnit_of_mem_AL`, `mem_CL` | proved |
| Lemma 3.1 | `phi_CL_lower` | proved |
| Lemma 5.1 (prime tail) | `prime_tail` (note's form), `sum_inv_sq_le_of_primes_gt` (stronger, used) | proved |
| §2.1 `Bad_ℓ` | `BadSetOf c ℓ` (generic in `c`), `BadSet ℓ` (§6.1 form), `badSet_eq` | defined |
| Proposition 4.1 (per prime) | `card_latticePts_le`, `card_badSet_le_latticePts`, `card_badSet_le` | proved |
| Proposition 4.1 (sum over `ℓ⁴ > N`) | `sum_card_latticePts_le`, `sum_card_badSet_large_le` (`≤ 20 N^{3/4}`) | proved |
| §6.1 `UniformBadBound` | `UniformBadBound` (def, the §6.1 statement verbatim) | defined |
| Lemma 2.1 (`G*_L ⊆ G`) | `goodSlopePrime_of_mem_CL` | proved |
| Theorem D, `T_L` count | `TL` (def), `card_TL_le` | proved |
| Theorem D + Prop. 5.3 (milestone 2) | `goodPrimeDensity_of_uniformBadBound` | proved |
| §6.1 `goodPrimeDensity` (milestone 4) | `uniformBadBound_holds`, `goodPrimeDensity` (`PropDFinal.lean`) | proved |
| §6.2 final link | `goodPrimeAP_of_greenTaoDense_uniformBadBound`, `goodPrimeAP_of_greenTaoDense'` | proved |

## Statement corrections and changes

None of these changes the conclusion.

1. **Proposition 5.3** needs no hypothesis "`S` is a set of primes". The proof bounds `θ_S(N)` by
   `log N · #(S ∩ [0, N])` and uses Chebyshev only for `π(N)`. The Lean statement takes the lower
   Dirichlet density in explicit form: `η/(x − 1) − K ≤ Φ_S(x)` for all `x ∈ (1, 2]`, with `η > 0`.
   This is equivalent to `liminf_{x→1⁺}(x − 1)Φ_S(x) > 0`.
2. **Lemma 5.2(1)** is proved in the form "if `θ_S(N) ≤ κN + B` for every `N`, then
   `Φ_S(x) ≤ κx/(x − 1) + B`". The note's `κx² + (x − 1)C` is replaced by this sharper form. Errors
   `βN^{3/4} log N` are absorbed into `κ` beforehand (`thetaS_le_of_eventually`,
   `eventually_rpow_mul_log_le`), so no `n^{−5/4} log n` series is needed. The proof needs neither the
   mean-value bound `n^{−x} − (n + 1)^{−x} ≤ x n^{−x−1}` nor `a ≥ 0`. It applies Abel summation twice,
   comparing with the sequence whose partial sums are exactly `κ(m + 1) + B`. The zeta bound
   `Σ n^{−x} ≤ x/(x − 1)` comes from Bernoulli's inequality, `rpow_one_add_le_one_add_mul_self`.
3. **Lemma 5.1** is proved with `3 log 4` instead of `4 log 4`, by Abel summation against
   `θ(m) ≤ m log 4` instead of the dyadic split. It holds for every finite set of primes `> L`
   (`sum_inv_sq_le_of_primes_gt`). The note's form is `prime_tail`.
4. **Proposition 4.1.** The count needs only `p = c_p² + e²` (Prop. 1.6(1), pd-lean-1's
   `exists_sq_add_sq`). `c_p ≠ 0` holds because a prime is not a square, and `ℓ ∣ e² + 1` follows
   from `ℓ ∣ c_p` and `ℓ ∣ p + 1`. The roots `±b_ℓ` are not used: two solutions of `ℓ ∣ e² + 1` agree
   up to sign mod `ℓ`. The sum over `ℓ⁴ > N` bounds `Σ 4√N/ℓ` by `√N · 4√N/N^{1/4}` instead of
   `4√N(1 + log √N)`. This gives the same `20 N^{3/4}` for every `N ≥ 1`, not only `N ≥ 10³`.
5. **Theorem D, constants.** The Lean proof takes `L` with `log L ≥ 16 A log 4` (`exists_L`), so that
   `α_L ≤ δ_L/2`, and `η = δ_L − α_L − δ_L/4`. Only positivity matters (as in the note). It uses
   `x/(x − 1) = 1 + 1/(x − 1)` instead of `x² ≤ 4`.
6. **`UniformBadBound`** is the §6.1 statement verbatim, with `BadSet` as in §6.1 (`badSet_eq` shows it
   is `BadSetOf cp`). pd-sieve's `uniformBadBound` states the same body with `BadSet` written out. The
   two differ only in the decidability instance of the `filter`, so `uniformBadBound_holds` closes the
   gap with `convert … using 4; exact Iff.rfl`.
7. **`deltaL_ge`** holds for `L ≥ 4`; the note says `L ≥ 5`.

## Lemmas added beyond the leaves

- Abel: `abel_summation` (general discrete Abel summation), `rpow_neg_step` (Bernoulli step),
  `indicator_log_nonneg`, `phiTerm_nonneg`, `thetaS_nonneg`, `thetaS_mono`, `thetaS_mono_set`.
- PrimeTail: `mul_inv_sq_sub_le`, `sum_tel_gt` (telescoping `Σ_{L<m<M}(1/m − 1/(m + 1))`),
  `sum_log_div_sq_le` (`Σ_{L<p≤M} log p/p² ≤ 3 log 4/L`).
- Lattice: `latticePts`, `card_Icc_filter_modEq_le` (a residue class meets `[−s, s]` in
  `≤ 2s/ℓ + 1` points), `card_first_le`, `first_eq_empty`, `card_second_le`, `sum_inv_sq_le_of_gt`.
- Residues: `mem_QL`, `seven_notMem_QL`, `eight_notMem_insert`, `prod_QL_pos`, a `NeZero (ML L)`
  instance, `coprime_modSet`, `pairwise_coprime_modSet`, `crt_apply_natCast`, `card_cond_eight`,
  `card_cond_seven`, `card_cond_prime`, `totient_prod_primes`, `prod_tel`, `zmod7_ne_zero`,
  `isUnit_of_cond`, `CL_subset_primes`, `summable_vonMangoldt_div_rpow`.
- PropD: `cp_rep`, `TL_subset_primes`, `goodSlopePrimes_subset_primes`, `eventually_rpow_mul_log_le`,
  `exists_L`.

## Problems

None. No finite computation is heavier than `decide` on `ZMod 7`, `ZMod 8` and `Nat.totient 8`.
`card_AL` uses `Nat.card` on subtypes of `ZMod i`, together with `Equiv.subtypePiEquivPi` and
`Nat.card_pi`. This avoids needing a `Fintype (ZMod i)` instance for a variable modulus.

## Suggestions for the next agent

- Hook `goodPrimeAP_of_greenTaoDense'` (or `goodPrimeDensity`) into `ZInQKernel/Main.lean`. The variants
  `…_of_greenTaoDense` and `…_of_certifiedRankSel_greenTaoDense` can then drop `GoodPrimeDensity`,
  keeping only `GreenTaoDense` as the number-theoretic trust statement. The owner of `Main.lean` and
  of `Hypotheses/GreenTao.lean` should make this change, and also update the docstring of
  `GoodPrimeDensity`, which still says "not proved in Lean".
- The blueprint can record Proposition D as proved: `ZInQ.Density.goodPrimeDensity`, from files 1–9
  (pd-lean-1, pd-lean-2, pd-sieve).
