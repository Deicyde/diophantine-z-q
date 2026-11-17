# bfh-kronecker results log

Task: restate bfh-leaf's `BFHClauseII` over the Kronecker symbol `(D/n)` (BFH's χ_D), prove the bridge to
fh-printed's `idelicChar`, rebuild the hFH discharge + fold check using only B = 4.

## 11-16 05:50 setup
- Build tree: copied (reflink) ~/dzq-wt/fh-printed/.lake/build and lean/.lake/build (fh-printed HEAD 8d0b9b64 differs
  from this base only in new files + OneProof/Main.lean).

## Kronecker symbol (Mathlib + FHPrinted/LocalNorm only) — VERIFIED (compiled, no warnings)
- `ZInQKernel/Contrib/OneProof/BFHPrinted/Kronecker.lean`:
  `kroneckerPrime D p := if p = 2 then χ₈ (D : ZMod 8) else jacobiSym D p`;
  `kroneckerSym D n := if n = 0 then (if |D| = 1 then 1 else 0) else ∏_{p^k ∥ n} kroneckerPrime D p ^ k`.
- Proved: kroneckerSym_one, kroneckerSym_mul (m,n ≠ 0), kroneckerSym_of_prime, kroneckerSym_prime (= legendreSym p D,
  p odd), kroneckerSym_two (= χ₈ D), kroneckerSym_two_of_one_mod_four; charAtPrime_odd (p odd, p² ∤ d: charAtPrime d p
  = legendreSym p d), charAtPrime_two_of_one_mod_four (= χ₈ d), charAtPrime_four_mul (square class), 
  charAtPrime_eq_kroneckerPrime (every fundamental d, every prime p), idelicChar_eq_kroneckerSym (every fundamental d,
  n ≠ 0), kroneckerSym_eq_jacobiSym (d ≡ 1 mod 4 squarefree, n ≠ 0).
- Pitfall: in this toolchain `if_pos`/`if_neg` are deprecated (use `ite_eq_left`/`ite_eq_right` with the condition);
  `simp only [key]` under `∀ u : ℤ_[p], … (u : ℚ_[p])` fails (subring coercion motive): rewrite with a funext'd
  equality of predicates instead.

## Restated leaf, bridge, B = 4 use, assembly — VERIFIED (compiled, no warnings, standard axioms)
- `ZInQKernel/Contrib/OneProof/BFHKronecker.lean` (copy BFHKronecker.lean.txt): `kroneckerTwistCoeff f D n =
  coeff f n * kroneckerSym D n`, `KroneckerCentralValueNeZero f D`, leaf `BFHClauseIIKronecker` (= bfh-leaf's
  BFHClauseII with χ_D the Kronecker symbol and S ⊇ primes dividing N, as printed, instead of 2N).
- Bridge: chiD_eq_kroneckerSym (D ≡ 1 mod 4 squarefree), kroneckerTwistCoeff_eq_printedTwistCoeff (all fundamental D),
  kroneckerTwistCoeff_eq_twistCoeff, kroneckerCentralValueNeZero_iff (all fundamental D).
- `bfhClauseIIKronecker_iff : BFHClauseIIKronecker ↔ BFHClauseII` (← via S ∪ {2} and SplitsInQuadratic.mono).
- B = 4 use: `exists_heegnerDisc_of_bfhClauseIIKronecker` (leaf applied once, S = (2N).primeFactors; D ≡ 1 mod 8 and
  D < 0 give D ≤ −7 < −4, no extra split primes). `grossZagierCd_of_bfhClauseIIKronecker` (copy of
  GZDecomp.grossZagierCd_of_leaves with hL2 … 4 replaced), `frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker`,
  `fhNonvanishing_of_bfhClauseIIKronecker` (every B, via the iff and bfh-leaf's glue).
- `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.BFHKronecker`: OK
  (13004 jobs, 1m25s on the copied tree).
- FoldCheck.lean: `frozenTarget_bfhKronecker` (Main's body, hFH ↦ hBFH : BFHClauseIIKronecker, the _gzLeaves call
  replaced by ..._bfhKronecker with the same first three args) and `frozenTarget_bfhKronecker_allB` (only the hFH
  argument replaced): both [propext, Classical.choice, Quot.sound] (FoldCheck-output.txt).
- Discharges.lean: `#discharges: 62 open hypotheses, 2301 theorems checked, 8 discharge one`; none from this task
  (expected: hFH's type FriedbergHoffsteinB_FE is not this file's conclusion); the hFH line is fh-printed's
  friedbergHoffsteinB_FE_of_printed. Axioms of all 14 new theorems standard (Discharges-output.txt).

## Differential check of the definition — VERIFIED (computed)
- kronecker_check.py (pure Python; no PARI/sympy on this host): transcription of `kroneckerSym` vs an independent
  binary Kronecker algorithm (Cohen Alg. 1.4.10, UNVERIFIED number) and vs J(n | |D|) for D ≡ 1 mod 4, on 30 random
  (D fundamental in [−200, 200], 0 ≤ n ≤ 400): 0 mismatches (kronecker_check-output.txt).
