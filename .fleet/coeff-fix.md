# coeff-fix (2026-11-16)

**Result.** `dsThm966` now rests on Deligne–Serre 1974 Thm 4.1 stated as printed. Both GLUE steps the review
found inside coeff-ext's leaf are proved in Lean. `ZInQKernel/Contrib/OneProof/DSThm966EV.lean` compiles with no
sorry and only the standard axioms. Report: `docs/research/coeff-fix.md`.

* New leaf `DSThm966EV.DSThm966Printed`. The hypothesis is Tau Ceti's `EigenformAwayFromLevel N 1`: nonzero,
  in the `ε`-space of the diamond operators, an eigenvector of `T_n` for every `n` prime to `N`, with no
  `a₁ = 1`. It also assumes `ε(−1) = −1`. The conclusion is `tr ρ(Frob_p) = F.eigenvalue p` (the
  `T_p`-eigenvalue) and `det = ε(p)`. Rated printed form; the locator (Thm 4.1 (4.1.1), p. 514) is UNVERIFIED.
* Glue, all proved:
  * `exists_eigenform`: the `T_p`-eigenvalue equals `coeff g p`, from `a₁ = 1`.
  * `char_neg_one`: `χ(−1) = −1`, from the parity lemma (Parity.lean:113) supplied at the one consumer,
    `dsThm966_of_printed`.
* Fallback leaf `DSThm966PrintedFull`, over full eigenforms. It is proved to follow from the main leaf, and it
  is also a consequence of Diamond–Shurman 9.6.6. It is there in case Deligne–Serre print 4.1 for newforms
  only.
* `#discharges`: dsThm966 by `DSThm966EV.dsThm966_of_printed`, which still assumes only
  `DSThm966EV.DSThm966Printed`. Standard axioms (`scratch/coeff-fix/discharges-output.txt`).
* Autofold spec `scratch/coeff-fix/autofold.json` supersedes coeff-ext's spec: it keeps the same dsThm965Weak
  discharge and takes dsThm966 from the new leaf. The dry run gives 34/11 → 35/11 (strict and strictest), the
  same as before, because the script already counted coeff-ext's leaf as LEAF. The generated fold compiles
  (`FoldCheck.lean`).
* **`k = 2` restriction not done.** `EigenformCoeffFieldFinite` keeps general `k`, because `dsThm965Weak`'s
  consumers need general weight. The chain is DSThm965 → `r14DetWtGe2_of_ds` (all `k ≥ 2`) → R14Det /
  EigenformHT (fields r14 and r13), which TailD:137, TailK:323 and TailA:3718 use at the Serre weight. So the
  second target (−1) does not apply.

**What remains.** Page checks of Deligne–Serre 4.1 (whether the print covers non-new eigenforms), DS 9.6.5 and
DS 6.5.1 / Shimura 3.52 (no network). The locators.md row and the fold itself are left to the integrator.
