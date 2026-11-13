# p-side: the positive-rank targets P1–P5 (coefficients and convergence of `L(C_d, s)`, `tyzInputs_iff`)

**Result.** All five targets are proved in Lean 4.35 / Mathlib v4.35. There are seven new modules
under `ZInQKernel/Contrib/PSide/` (1002 lines), with no `sorry`. Every headline theorem depends only
on `propext`, `Classical.choice` and `Quot.sound` (22 theorems checked; VERIFIED,
`scratch/p-side/axioms-output.txt`). The modules import only baseline files
(`RouteK/Rank/LFunctionCd.lean`, `RouteK/PropN.lean`), Mathlib, and each other. Nothing imports them.
No existing file was edited.

| target | file | main theorems |
|---|---|---|
| P1 | `APZero.lean` | `LFunction_cd_apply_prime_of_mod_four_eq_three`: `a_p(C_d) = 0` for `p ≡ 3 (mod 4)`, `p ∤ 2d`; `natCard_point_cd_of_mod_four_eq_three`: `#C_d(𝔽_p) = p + 1`; `LFunction_cd_apply_prime_eq_neg_charSum`: `a_p = −Σ_x χ(x³ − d²x)` |
| P2 | `Coeff.lean` | `cdCoeff_mul` (coprime multiplicativity), `isMultiplicative_cdArith`, `cdCoeff_prime_pow`, `cdCoeff_prime`, `cdCoeff_prime_pow_succ_succ` (`c_{p^{k+2}} = c_p c_{p^{k+1}} − p c_{p^k}`, `p ∤ 2d`), `cdCoeff_prime_pow_of_dvd` / `cdCoeff_eq_zero_of_dvd` (vanishing at `p ∣ 2d`), `LFunction_cd_eq_cdCoeff`, `LFunction_cd_prime_pow_succ_succ` |
| P3 | `BadPrimes.lean` | `LFunction_cd_apply_prime_eq_sub_card_of_dvd` (`p ∣ 2d`), `LFunction_cd_apply_prime_eq_sub_card_all`: `a_p = p − #{(x,y) ∈ 𝔽_p² : y² = x³ − d²x}` at **every** prime |
| P4 | `Hasse.lean`, `Convergence.lean` | `cdCoeff_prime_sq_le` (Hasse: `c_p² ≤ 4p`, every prime, every `d`), `LFunction_cd_prime_sq_le`; `cdCoeff_sq_le` (`c_n² ≤ σ₀(n)² n`); `LSeriesSummable_cd` (Mathlib's `L(C_d, s)` converges absolutely for `Re s > 3/2`), `abscissaOfAbsConv_cd_le` (`≤ 3/2`), `differentiableOn_LSeries_cd` (holomorphic on `Re s > 3/2`) |
| P5 | `TYZInputsIff.lean` | `tyzInputs_iff`, `tyzInputs_iff_readingA`, `tyzInputs_iff_readingA_of_hecke`, `tyzInputs_of_readingA` |
| extra | `Supersingular.lean` | `cdCoeff_prime_pow_of_mod_four_eq_three`: `c_{p^{2k}} = (−p)^k`, `c_{p^{2k+1}} = 0` for `p ≡ 3 (mod 4)` |

Hypotheses: P2, the Hasse bound and `LSeriesSummable_cdCoeff` hold for every `d`, because they are
about `cdCoeff d`. The statements about Mathlib's `WeierstrassCurve.LFunction` / `LSeries` assume
odd squarefree `d`, the hypothesis of `LFunctionCd.lean`'s `LFunction_cd_apply`. That covers the CR₃
case `d ≡ 5 (mod 8)`.

## Proofs

**P1.** `card_solutions_eq`: over a finite field `F` of odd characteristic,
`#{(x,y) : y² = g(x)} = #F + Σ_x χ(g x)`. This comes from Mathlib's `quadraticChar_card_sqrts`.
Combined with `LFunction_cd_apply_prime_eq_sub_card`, it gives `a_p = −Σ_x χ(x³ − d²x)`. The
polynomial is odd, so reindexing by `x ↦ −x` multiplies the sum by `χ(−1)`. That is `−1` for
`p ≡ 3 (mod 4)` (Mathlib's `quadraticChar_neg_one` and `ZMod.χ₄_nat_three_mod_four`), so the sum
vanishes.

**P2.** Multiplicativity comes from `Nat.factorization_mul_of_coprime` and
`Finsupp.prod_add_index_of_disjoint`. The recursion is the coefficient of `T^{k+2}` in
`(1 − c_p T + p T²) · (1/(1 − c_p T + p T²)) = 1`. Vanishing holds because the Euler polynomial at
`p ∣ 2d` is `1`.

**P3.** At `p ∣ d` the reduction is the cusp `y² = x³`. Its affine points are `(t², t³)`, and
`cuspEquiv : F ≃ {y² = x³}` has inverse `(x, y) ↦ y/x`, so the count is `p`. At `p = 2`, odd `d`,
the curve `y² = x³ − x` over `𝔽₂` has 2 points (by `decide`). In both cases `p − N_p = 0`, which is
Mathlib's coefficient there (additive reduction).

**P4, Hasse.** I used a direct character-sum argument (Jacobsthal sums) instead of general Hasse,
as the task suggested. Let `φ(a) = Σ_x χ(x(x² + a))`; then `c_p = −φ(−d²)`. Over any finite field
of odd characteristic with `q` elements:
1. `φ(a t²) = χ(t) φ(a)` for `t ≠ 0`.
2. `Σ_a χ((a+u)(a+v)) = −1` for `u ≠ v`. This is Mathlib's Jacobi sum `J(χ, χ) = −χ(−1)`
   (`jacobiSum_nontrivial_inv`).
3. Hence `Σ_a φ(a)² = q(q−1)(1 + χ(−1)) ≤ 2q(q−1)`.
4. For `a ≠ 0`, `(q−1) φ(a)² = Σ_{t≠0} φ(at²)² ≤ 2 Σ_c φ(c)²`, since each `c` has at most two
   square roots.

So `φ(a)² ≤ 4q`. This is STANDARD (the classical proof of Hasse's bound for `y² = x³ + ax`). For
references see Berndt–Evans–Williams, *Gauss and Jacobi Sums*, the chapter on Jacobsthal sums, and
Ireland–Rosen, Ch. 18, for `a_p = ±2a` with `p = a² + b²`. Both chapter numbers are UNVERIFIED (no
network).

**P4, convergence.** `recurrence_bound`: a real sequence with `u₀ = 1`, `u₁ = a`,
`u_{k+2} = a u_{k+1} − r² u_k` and `a² ≤ 4r²` satisfies `|u_k| ≤ (k+1) r^k`. The proof writes
`u_k = Σ_{i≤k} α^i β^{k−i}` with `α, β = (a ± i√(4r² − a²))/2`, both of modulus `r`. With
`r = √p` this gives `c_{p^k}² ≤ (k+1)² p^k`. Multiplicativity then gives `c_n² ≤ σ₀(n)² n`. The
comparison series `Σ σ₀(n) n^{−(s−1/2)}` is the L-series of `1 ⍟ 1`, which is summable for
`Re s > 3/2` (Mathlib's `LSeriesSummable_one_iff` and `LSeriesSummable.convolution`).
Holomorphy follows from Mathlib's `LSeries_differentiableOn`.

**P5.** This is the assembly described in `rv-pn-encoding` F1, item 5:

  `tyzInputs_iff : TYZInputs ↔ ∀ n, n % 8 = 5 → Squarefree n →
     (∃ F, IsLContinuation (C_n) F ∧ analyticOrderAt F 1 ≤ 1) ∨ (T5aCl n = 0 ∧ T5bCl n = 0)`.

The forward direction uses I7 when `L n ≠ 0` and `genusSums_eq_zero` when `L n = 0`. The backward
direction chooses `L` as follows:
- on classes 1 and 3, `L m = (Lam m).val`;
- on class 5, `L m = 1` if a continuation of order `≤ 1` exists, otherwise `0`;
- `L m = 0` everywhere else.

`L 1 = 1` and `LemmaTwoEight L` follow from `lemmaN1_core`. The genus data come from
`Witness.genusData_nonempty` when `L n ≠ 0`, and from `Witness.genusData_nonempty_of_parities`
(parities via `matching`, `parity_sums_eq`) when `L n = 0`.

Corollaries:
- `tyzInputs_iff_readingA`: `TYZInputs ↔ TYZThm35ReadingA ∧ ∀ n, (∃ continuation) ∨ (T5a = T5b = 0)`.
  This needs no hypothesis.
- `tyzInputs_iff_readingA_of_hecke`: `HeckeContinuation → (TYZInputs ↔ TYZThm35ReadingA)`.
- `tyzInputs_of_readingA` (item 6).

So, given Hecke's continuation, the encoding `TYZInputs` is exactly reading A of TYZ Theorem 3.5(2):
it is not vacuous, and it is not stronger. `lemmaN2` is used through `genusSums_eq_zero` and
`genusData_nonempty_of_parities`, and the axiom check confirms that it is `sorry`-free on this base.

## Checks

* Compile: `lake build` of the seven modules succeeds, with 0 errors and 0 `sorry` (VERIFIED). Each
  module was also checked with `lake env lean`.
* Axioms: `scratch/p-side/Axioms.lean`, output in `scratch/p-side/axioms-output.txt` (VERIFIED).
* PARI cross-check on 30 inputs (`scratch/p-side/check_pari.py`, `d = 5`, `n = 1..30`, `ellan`; VERIFIED):
  - `a_p = −Σ χ(x³ − 25x)` at `p ∤ 10`;
  - `a_p = 0` at `p ≡ 3 (mod 4)` and at `p ∣ 10`;
  - `a_n² ≤ σ₀(n)² n`.

## What remains / notes for integration

* None of these files closes a registered provider (`ZInQ.Contrib.*`). They are glue and API for
  the CR₃ side. P4 shows that the clause `F s = E.LSeries s` for `3/2 < Re s` in `IsLContinuation`
  (`CR3Literature.lean`) compares `F` with an absolutely convergent, holomorphic series. So the
  Props `HeckeContinuation`, `GrossZagier`, `FunctionalEquation5` and `TYZThm35ReadingA` are about
  the genuine `L(C_d, s)` on a nonempty open half-plane.
* Two pinned docstrings could now point here; per the rules I did not edit either:
  - `RouteK/PropN.lean` around L1522 says `tyzInputs_iff` "is not written in Lean";
  - `STATUS.md`.
* The Hasse bound is proved only for `C_d`, not for general elliptic curves. `recurrence_bound` and
  `cdCoeff_sq_le` are generic in the recursion and would carry over to any curve once its `a_p²` is
  bounded by `4p`.
* I did not have the upstream tracking issue's text. The statements follow the task description of
  P1–P5.
