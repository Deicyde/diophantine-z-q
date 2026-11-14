# reduct-split (fleet summary)

**Result.** Seven of the eight rows (reduction of abelian varieties) are now Lean theorems from published-form leaves.
Proofs are in `scratch/reduct-split/Reduction.lean`, namespace `ReductSplit`: one file, kernel imports only, no
`sorry`, standard axioms only (20 `#print axioms`, in `axioms.txt`). Report: `docs/research/reduct-split.md`.

- **Closed, no glue:**
  - r7b `PkgI2.SerreTatePotentialGood` from Serre–Tate Thm 2 as printed (finite image of inertia) and Mumford §4
    (`serreTatePotentialGood_final`);
  - r8 `PkgI2.GrothendieckMonodromy` from SGA 7 IX 3.6, SGA 7 IX 3.5 and BLR 1.4/3 over a DVR, with Mumford §4
    (`grothendieckMonodromy_final'`);
  - `faltingsLemma5BC`, reduced to the base-field form `HeightSplit.FaltingsLemma5` (`faltingsLemma5BC_final`).
- **r6 `PkgI2.RaynaudCriterion`:** from SGA 7 IX 4.7, 3.5, BLR 1.4/3 and Mumford §4, plus one glue,
  `FixedTorsionRationalImperfect`. The glue is needed only for imperfect `K`; the perfect case, which covers every use
  in the project, is proved.
- **SS1, SS3 (height-split's global semistable-reduction leaves):** from the local SGA 7 IX 3.6/3.3 and BLR 1.4/3,
  plus the glue `SemistableLocalGlobal` (Néron models localize; fibre identification) and, for SS1,
  `SemistableAlmostAll`.
- **SS2:** the local SGA 7 IX 3.3(ii) is a leaf; the global content is in one glue
  (`SemistableNeronBaseChangeLocalGlobal`), so this row is only partly split.
- **t10 not split.** The printed Milne 15.1 is étale ℓ-adic; Mathlib has only pro-étale groups, with no comparison,
  and the Galois equivariance is not printed anywhere.

**Proved along the way:**
- a valuation ring of a finite extension over a DVR is a DVR (`e ≤ n`), and the restriction of a DVR to a subfield
  of finite index is a DVR;
- `K̄`-points are defined over finite extensions, and over perfect `K` Galois-fixed points are rational;
- divisibility of `A(K̄)[ℓ^∞]`, from Mumford;
- `deg φ_L = deg φ`, by descent of kernel points;
- `(A_{K'})_L ≅ A_L` as group schemes;
- the model height depends only on the group scheme;
- the local definitions are consistent at the zero abelian variety.

**Bundle:** `rows_of_leaves (l : ReductLeaves) (g : ReductGlue) hF5` proves all seven rows from 8 leaves and 4 glue.

**Risks** (no network; all locators UNVERIFIED): SGA 7 IX 4.7 may be printed over a strictly henselian base, and
Serre–Tate over a complete one; the leaves here are over a general DVR.

**Remaining:** the four glue Props above; t10; printed Faltings Lemma 5 (needs finite flat group schemes over `𝓞_K`).
