# ap-finish report

The trust statement of `GoodPrimeAP` (22P_AP) is now split into two named statements, as the aud-ap audit suggested. Every existing statement is unchanged.

| item | Lean name | file | status |
|---|---|---|---|
| progressions of every length (lean-eval `green_tao` shape) | `ZInQ.ContainsArbitraryAPs` | ZInQKernel/Hypotheses/GreenTao.lean | definition |
| positive relative upper density in the primes | `ZInQ.PrimesRelUpperDensityPos` | ZInQKernel/Hypotheses/GreenTao.lean | definition |
| Green–Tao 2008 Thm 1.2, dense form (trust statement) | `ZInQ.GreenTaoDense` | ZInQKernel/Hypotheses/GreenTao.lean | hypothesis (definition) |
| Proposition D, density part (trust statement) | `ZInQ.GoodPrimeDensity` | ZInQKernel/Hypotheses/GreenTao.lean | hypothesis (definition) |
| 22P_AP from the two | `ZInQ.goodPrimeAP_of_greenTaoDense` | ZInQKernel/Hypotheses/GreenTao.lean | proved |
| main theorem variant | `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_greenTaoDense` | ZInQKernel/Main.lean | proved |

## Definitions
- `ContainsArbitraryAPs A := ∀ k, ∃ a b : ℕ, 1 ≤ b ∧ ∀ j < k, a + b * j ∈ A`.
- `PrimesRelUpperDensityPos A := ∃ c : ℝ, 0 < c ∧ ∃ᶠ N in atTop, c * π(N) ≤ #{n ∈ range (N+1) | n ∈ A}` (classical decidability). For a set of primes this is the same as `limsup |A ∩ [1,N]| / π(N) > 0`.
- `GreenTaoDense := ∀ A : Set ℕ, A ⊆ {p | p.Prime} → PrimesRelUpperDensityPos A → ContainsArbitraryAPs A`.
- `GoodPrimeDensity := PrimesRelUpperDensityPos {p | GoodSlopePrime p}`.

## Trust statements (in the docstrings)
- `GreenTaoDense`: Green–Tao, Ann. of Math. 167 (2008), Theorem 1.2, proved there only in outline (section 11 of arXiv math/0404188v6). A complete proof of the needed form is the main theorem of Tao–Ziegler, Acta Math. 201 (2008), with P_i = (i − 1)m. The published Lean proofs of Green–Tao known to the project prove the result only for the set of all primes (Theorem 1.1, the lean-eval statement), not this dense form.
- `GoodPrimeDensity`: Proposition D of docs/research/nt-22p.md (relative density about 0.106, from the CM description of good slope primes and a sieve). It exists on paper only as a sketch.

## Proof of goodPrimeAP_of_greenTaoDense
Adapted from `AudAP.goodPrimeAP_of_greenTao_propD` (scratch/aud-ap/Derive.lean on wip/aud-ap). Removing the primes up to M = max S_b costs at most M + 1 in each count. Since π(N) → ∞ (`Nat.tendsto_primeCounting`), the set {good slope primes > M} still has relative upper density at least δ/2. Green–Tao with k = K + 1 then gives the progression. The ℕ-valued shape with b ≥ 1 means the progression never has to be reversed. The first term a lies in A, so it is prime and therefore ≥ 1.

## Docstring fixes
- `GoodPrimeAP` (Hypotheses/PrimeAP.lean): now cites Tao–Ziegler and says section 11, not §10, and points to the split. The statement is unchanged.
- Main.lean module docstring: says that 22P_AP follows from Green–Tao (dense form) and Proposition D together, not from Green–Tao alone, and names the new variant.

## Checks
- `lake build ZInQKernel` succeeds; there is no sorry in ZInQKernel.
- `python3 scripts/check_target.py`: FrozenTarget matches.
- `#print axioms` on the new main-theorem variant and on `goodPrimeAP_of_greenTaoDense`: [propext, Classical.choice, Quot.sound].

## Statement corrections
None. The task statements were formalized as given.

## Extra lemmas
None. The new import of GreenTao.lean is in Main.lean, and GreenTao.lean imports PrimeAP.lean.

## Problems
- The worktree started without Lake build files, and fetching Mathlib failed. The build files were copied from a sibling worktree on the same base commit.

## Suggestions
- If a Lean proof of the dense Green–Tao form (or of Tao–Ziegler's linear case) becomes available, adapt its conclusion to `ContainsArbitraryAPs` and discharge `GreenTaoDense`.
- Proposition D needs a written proof. A Lean proof would need Chebotarev or CM-style density results that Mathlib does not have.
