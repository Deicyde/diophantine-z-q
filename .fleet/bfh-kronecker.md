# bfh-kronecker (fleet summary)

**Result.** Bump–Friedberg–Hoffstein 1990 clause (ii) is restated with the print's own character,
`χ_D(n) = (D/n)` the Kronecker symbol, and with `S ⊇` the primes dividing `N` as printed. The new leaf is
`ZInQ.BFHPrinted.BFHClauseIIKronecker`, rated **printed form** (direct instance at `k = 1`, flag unread). The hFH
discharge is rebuilt on it and applies the leaf once, at `B = 4` (`S` = the primes dividing `2N`). The proof is
`D ≡ 1 (mod 8)` and `D < 0`, so `D ≤ −7`. Target met: hFH can be replaced by the printed leaf, **−1 GLUE** in both
columns. Report: docs/research/bfh-kronecker.md.

**Compiles** (no warnings, axioms `[propext, Classical.choice, Quot.sound]`):
- `ZInQKernel/Contrib/OneProof/BFHPrinted/Kronecker.lean` (Mathlib plus fh-printed's LocalNorm). It defines
  `kroneckerSym` (textbook product formula over `ZMod.χ₈` and Mathlib's `jacobiSym`) and proves `kroneckerSym_mul`,
  `kroneckerSym_prime`, `kroneckerSym_two` (the Compat facts), and `idelicChar_eq_kroneckerSym` for **every**
  fundamental discriminant (odd and even). It also proves `kroneckerSym_eq_jacobiSym` (gz-decomp's `chiD`).
- `ZInQKernel/Contrib/OneProof/BFHKronecker.lean` contains:
  - the leaf, and `bfhClauseIIKronecker_iff : BFHClauseIIKronecker ↔ BFHClauseII` (bfh-leaf's);
  - `exists_heegnerDisc_of_bfhClauseIIKronecker` (the `B = 4` use);
  - `grossZagierCd_of_bfhClauseIIKronecker` and `frozenTarget_of_sixContactMin_tyzThm35ReadingA_bfhKronecker`;
  - `fhNonvanishing_of_bfhClauseIIKronecker`, the every-`B` drop-in.
- `scratch/bfh-kronecker/FoldCheck.lean`: `frozenTarget_bfhKronecker` is Main's body with `hFH ↦ hBFH`, standard
  axioms. `#discharges` reports 62 open hypotheses, 2301 theorems checked and 8 discharges; none comes from this
  file, as expected for a top-level hand fold. The autofold spec (hand fold) is in
  `scratch/bfh-kronecker/autofold.json`.
- Differential check: the Lean definition against an independent binary Kronecker algorithm on 30 pairs gave 0
  mismatches (pure Python; no PARI on the host).

**Remains.** The hand fold into Main.lean, kinds.tsv and locators.md (not allowed here). Clearing the *unread*
flag needs a reading of BFH pp. 543–544. One definitional identification is left, and it is not a Lean step: a Tau
Ceti newform with trivial nebentypus is the classical newform on Γ₀(N). newform-dict's `isNewform_iff` already
shows that Tau Ceti's `Newform` is the printed Atkin–Lehner newform.
