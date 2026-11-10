# pd-sieve report: the vendored Selberg sieve and GaussSieve (pd-paper.md §4.3–4.5, file 7–8)

Both leaves are done and fully proved. `lake build ZInQKernel` succeeds. The new files contain no
`sorry`, `axiom` or `native_decide`. `#print axioms` on `SelbergSieve.selberg_bound_simple`,
`ZInQ.Density.uniformGaussBadBound` and `ZInQ.Density.uniformBadBound` reports
`[propext, Classical.choice, Quot.sound]`.

Files:
- `ZInQKernel/Sieve/{AuxResults,Basic,Selberg,SelbergBounds}.lean` (vendored, Apache-2.0) and
  `ZInQKernel/Sieve/LICENSE`. Root module `ZInQKernel/SieveVendor.lean`.
- `ZInQKernel/Density/GaussSieve.lean` (namespace `ZInQ.Density`) and its helper modules
  `ZInQKernel/Density/GaussSieve/{Harmonic,SelbergSum,Local,Box,Instance}.lean` (namespace
  `ZInQ.Density.GaussSieve`). Root module `ZInQKernel/DensitySieve.lean`.
- `ZInQKernel.lean` gains `import ZInQKernel.SieveVendor` and `import ZInQKernel.DensitySieve`.
- `THIRD_PARTY_NOTICES.md` gains a NOTICE section (source repository, tag `v4.35.0`, commit
  `127b50e3`, license, the change made). It also records one adapted lemma (see below).
- The branch merges `origin/wip/pd-paper` and `origin/wip/pd-lean-1`. GaussSieve uses pd-lean-1's
  `InClass`, `cp` and `exists_sq_add_sq` (Proposition 1.6).

## Leaves

| article (pd-paper.md) | Lean name | status |
| --- | --- | --- |
| §6.1 file 7: vendored sieve | `ZInQKernel/Sieve/*`, `SelbergSieve.selberg_bound_simple` | proved (upstream) |
| §4.3 sieve set-up (box, `F`, `P`, `ν`, level) | `GaussSieve.gaussSieve`, `gsBox`, `gsF`, `gsProd`, `gsNu` | defined |
| §4.3 (4.1) prime points are sifted | `card_support_primes_le_siftedSum`, `mem_support_of_gaussBad` | proved |
| Lemma 4.3 (local densities, CRT) | `GaussSieve.card_zset_prime`, `card_zset_prod`, `card_zset_eq_of_dvd` | proved |
| Lemma 4.4 (remainders) | `GaussSieve.abs_card_box_dvd_sub_le` (general box), `abs_rem_le` | proved |
| §4.4 Selberg bound, error term | `GaussSieve.siftedSum_le`, `errSum_le` | proved |
| Lemma 4.5 (`S ≫ log w`) | `GaussSieve.selbergBoundingSum_ge_log` (`S ≥ (log w)/10`) | proved |
| Claim A | `GaussSieve.rSum_ge_log` (`(2/3) log w ≤ Σ_{n≤w} r(n)/n`) | proved |
| Claim B | `GaussSieve.rSum_le_hSum` (`V = 4`), `rDiv_eq_hDiv_mul_vDiv`, `vSum_le_four` | proved |
| test instance `ℓ = 5` | `ZInQ.Density.siftedSum_le_five` | proved |
| Proposition 4.2 (counting form) | `ZInQ.Density.card_gaussBad_le` | proved |
| Proposition 4.2 | `ZInQ.Density.uniformGaussBadBound` (`A = 14402`) | proved |
| §6.1 `uniformBadBound` | `ZInQ.Density.uniformBadBound` | proved |

## Statement of the main result, and how it matches `UniformBadBound`

pd-lean-2 has not yet pushed `UniformBadBound` or `BadSet`, so I did not define either name. To avoid
a clash with them, `uniformBadBound` states the body of §6.1's `UniformBadBound` verbatim, with
`BadSet ℓ` written out as `{p | p.Prime ∧ InClass p ∧ (ℓ : ℤ) ∣ cp p ∧ ℓ ∣ p + 1}`:

```lean
theorem uniformBadBound :
    ∃ A N₁ : ℝ, 0 < A ∧ ∀ N : ℕ, N₁ ≤ N → ∀ ℓ : ℕ, ℓ.Prime → ℓ % 4 = 1 → 5 ≤ ℓ →
      ((ℓ : ℝ) ^ 4 ≤ N) →
      (((Finset.range (N + 1)).filter
          (· ∈ {p : ℕ | p.Prime ∧ InClass p ∧ (ℓ : ℤ) ∣ cp p ∧ ℓ ∣ p + 1})).card : ℝ) ≤
        A * N / (ℓ ^ 2 * Real.log N)
```

If file 9 defines `BadSet` and `UniformBadBound` exactly as in §6.1, then
`theorem : UniformBadBound := uniformBadBound` should close by definitional unfolding (`p ∈ BadSet ℓ`
and `p ∈ {p | …}` are defeq). If the final `BadSet` differs, only the five-line proof of
`uniformBadBound` (from `uniformGaussBadBound` and `mem_gaussBad_of_bad`) needs to change.

The core bound is stated for a set that does not depend on CM theory:
`GaussBad ℓ = {p | p.Prime ∧ ∃ c e : ℤ, p = c² + e² ∧ ℓ ∣ c ∧ ℓ ∣ p + 1}`.
`uniformGaussBadBound` is Proposition 4.2 for `GaussBad`. `mem_gaussBad_of_bad` turns the note's bad
set into `GaussBad` through Proposition 1.6.

## Statement corrections and deviations from the note

None of these changes the conclusion. Each one simplifies the Lean proof.

1. **Lemma 4.5 / Claims A and B: a simpler proof.**
   - *Claim A* needs no Euler–Mascheroni bracket. In `R(w) = Σ_{d≤w} χ₄(d)·H(⌊w/d⌋)/d` the
     coefficients `a(d) = H(⌊w/d⌋)/d` are antitone. Grouping the terms in blocks of four gives
     `R(w) ≥ a(1) − a(3) ≥ (2/3)H(w) ≥ (2/3) log w` for every `w`, with no additive constant.
   - *Claim B* uses the exact factorisation `r = h ∗ v`. Here `h = τ·1_𝒮` (`𝒮`: every prime factor is
     `≡ 1 (mod 4)`) and `v = r·1_𝒯` (`𝒯`: no prime factor is `≡ 1 (mod 4)`). On `𝒯`, `v ≤ 1` and `v`
     is supported on `2^a s²`, so `Σ v(m)/m ≤ 2·2 = 4` (instead of `V ≤ 2ζ(2)⁴`).
   - The Selberg sum is compared directly with `τ`. At a sifting prime,
     `g(q) = (2q − 1)/(q − 1)² = Σ_{k≥1} (k + 1)/q^k` exactly. So
     `S ≥ Σ_{m ≤ w, rad m ∣ P} τ(m)/m` (`selbergBoundingSum_ge_tau`), which counts non-squarefree `m`
     too. The note instead uses squarefree `l` with `2^{ω(l)}`.
   - Result: `S ≥ (log w)/10` for every prime `ℓ ≥ 5` and every `w ≥ 1`. The note has
     `((2/3) log w − 2)/25`.
2. **The roots `b`.** The note fixes `b ∈ {b_ℓ, ℓ − b_ℓ}`. The Lean proof runs the sieve for every
   `b ∈ ZMod ℓ` with `b² = −1` (`b.val` as the integer shift). It shows that there are at most two such
   `b` (`card_sqrt_neg_one_le`), and that `e ≡ b` holds for some such `b`. The local count needs only
   `ℓ ≢ 0 (mod q)`, not `b² ≡ −1`.
3. **Box.** The box is `[−K, K] × [−K − 1, K]` with `K = ⌊⌊√N⌋/ℓ⌋`, so `M₁ = 2K + 1` and `M₂ = 2K + 2`.
   This avoids the `b`-dependent interval `I₂`. The remainder bound is the cruder
   `|R_d| ≤ ρ(d)(M₁ + M₂ + 1) ≤ d²(4K + 4)`, and the error sum is at most `w⁸(4K + 4)` (`3^{ω(d)} ≤ d`,
   at most `w²` divisors `d ≤ w²`).
4. **Constants.** `w = ⌊N^{1/40}⌋₊` and `A = 14402`. `N₁` is not explicit: it is `max(U₀, 4)^{40}`,
   where `400 log u ≤ u²` for `u ≥ U₀` (from `isLittleO_log_rpow_atTop`). The statement is
   existential in `N₁`, so this is enough. On paper `U₀ = 40` works (`u² − 400 log u` increases for
   `u ≥ 15` and is positive at `40`), which gives `N₁ = 40⁴⁰ ≈ e^{148}`, below the note's `e^{1920}`.
5. **Hypotheses not used.** `ℓ % 4 = 1` is not used: for `ℓ ≡ 3 (mod 4)` the set is empty anyway. It is
   kept to match `UniformBadBound`. The core lemmas need only `ℓ` prime with `ℓ ≥ 5`.

## Lemmas added beyond the leaves

- `GaussSieve.prod_factors_sum_pow_mult`: upstream's `Sieve.prod_factors_sum_pow_compMult`, with
  "completely multiplicative" weakened to "multiplicative". The upstream proof uses only that. It is
  copied with attribution in the file header and in `THIRD_PARTY_NOTICES.md`.
- `Harmonic.lean`: `chiDiv`, `invId`, `rDiv`, `mul_apply_prime_pow'` (Dirichlet convolution at a
  prime power), `alt_sum_ge` (alternating χ₄ sums), `AllOneMod4`/`NoOneMod4` and their indicators,
  `tauDiv`, `hDiv`, `vDiv`, `vDiv_props`, `hSum_coprime_ge` (removing the multiples of `ℓ` costs
  `1 − 2/ℓ`).
- `SelbergSum.lean`: `sum_succ_mul_pow_le` (`Σ_{k=1}^M (k + 1)x^k ≤ (1 − x)^{−2} − 1`),
  `selbergTerms_ge_sum_tau`.
- `Local.lean`: `ZSet`, `zsetEquivOfRingEquiv`, `zsetEquivProd`, `card_zset_mul` (CRT).
- `Box.lean`: `abs_card_Ico_cast_eq_sub_le` (an interval of `M` integers meets a residue class mod `d`
  in `M/d ± 1` points), `abs_mul_sub_mul_le`, `box`, `gaussFZ`, and Lemma 4.4 for an arbitrary box.
- `GaussSieve.lean`: `GaussBad`, `mem_gaussBad_of_bad`, `card_sqrt_neg_one_le`, `one_le_weights`,
  `gaussBad_final_ineq` (the real inequality, with `u = N^{1/40}`).

## Problems

None blocking. Every finite computation is symbolic; no `decide` is used on large data.

## Suggestions for the next agent

- File 9 (pd-lean-2): import `ZInQKernel.DensitySieve` and close `UniformBadBound` with
  `uniformBadBound`, or drop the hypothesis from `goodPrimeDensity_of_uniformBadBound` to get
  `goodPrimeDensity` unconditionally.
- `GaussSieve.abs_card_box_dvd_sub_le` and `card_zset_prod` are general: any box and any finite set of
  primes `q ≡ 1 (mod 4)` with `q ∤ ℓ`. The lattice count of Proposition 4.1 (file 6) can reuse
  `GaussBad` and `mem_gaussBad_of_bad`.
