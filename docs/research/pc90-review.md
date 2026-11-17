# pc90-review: review of draft PR #90 (fork issue #83), head 517e05cce

Task pc90-review, 2026-11-17, branch `wip/pc90-review` (exactly the head of PR #90; nothing merged).
Sources: `diophantine_zq.tex` L1019–1121, Elliot's supplement S12 (`parity-frozen-4eaee875.tex`, md5
5b8d6f645f240603135c536001dd4756, read from `~/dzq-wt/pc-from-rc/scratch/upstream/`). Log:
`scratch/pc90-review/log.md`. All claims below are VERIFIED (compiled or read) unless marked.

## Verdict

**NOT ready to land as is, for one non-mathematical reason. The Lean and the mathematics are clean.**

1. **Blocker: the retained source S12 is committed.** `scratch/upstream/parity-frozen-4eaee875.tex` (718 lines,
   32153 bytes, md5 identical to Elliot's supplement) is tracked in the PR tree. Commit 4b2595108 added it,
   although its message says "untrack the empty scratch placeholder (the S12 copy stays local and uncommitted)";
   631a68420 had committed an empty placeholder at that path. S12 is retained source that must not be
   redistributed. Fix: remove it in a new commit, and squash or rewrite the history before merging into any
   public branch, because the file stays in the PR's history (commit 4b2595108). Early notice:
   `.fleet/pc90-review-verdict.md`.
2. Once that is fixed, the PR is clean:
   * Builds: `lake build ZInQKernel.OneProof.Main ZInQKernel.MainGreenTao` succeeds (**16114 jobs**). All 50
     Lean modules the PR adds or changes build (**16166 jobs**, no errors).
   * Axioms: `frozenTarget`, the MainGreenTao headline and 20 new main theorems use only
     `[propext, Classical.choice, Quot.sound]`.
   * No `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by`, `extern` or `unsafe` in the PR's files, and
     no file pinned by upstream is edited.
   * No false step: every glue step of tex L1019–1121 is checked by Lean.
3. Note: the PR is not on fork main 5f1fac79. Its merge base is 67950e82; 5f1fac79 adds PRs #87–#89 (docs, CI).
   `git merge-tree HEAD 5f1fac79` has no conflicts, so this is not a blocker. A plain `git diff 5f1fac79 HEAD`
   shows those PRs' changes as reverted; ignore that.

**`frozenTarget`'s exact hypothesis list** (`ZInQKernel/OneProof/Main.lean:155`):

```
theorem ZInQ.OneProof.frozenTarget
    (r : HDec.HSyn.OpenResearchLeaves57) (t : HDec.HSyn.OpenTextbookLeaves18) (l : HDec.HSyn.OpenAddedLeaves27)
    (hRC : ZInQ.Manuscript.SelmerTwoPower.RestrictedConverseGenuine)   -- Theorem 5.3 as printed
    (h54 : ZInQ.Manuscript.PoleS12.Lemma54)                             -- lem:corank
    (hKum : ZInQ.Manuscript.PoleS12.KummerSelmerM)                      -- #Sel₂(E_ℓ/ℚ) = #SelM ℓ (proved elsewhere in the PR)
    (hB : ZInQ.Manuscript.PoleS12.BCDTThmA)                             -- modularity
    (hK : ZInQ.Manuscript.PoleS12.KolyvaginThm1) :                      -- Kolyvagin, r = 1
    ZInQ.FrozenTarget
```

Proof of PC from the last five: `PoleS12.poleCompleteness_of_restrictedConverseGenuine_mw`, built from:
* `PoleRC.crm_of_restrictedConverse_proved`, with Mordell–Weil for E_ℓ (`mordellWeilM`) and the 2-descent
  (`descentGlueM`) proved;
* `PoleS12.simultaneousConstruction`, which is pc-s12's `matrixRealization` plus `dimThreeCount_S12 localGoodUnram`.

The headline `ZInQ.exists_bounded_integer_polynomial_defining_integers_of_sixContactMin_poleCompleteness`
(MainGreenTao) is unchanged, byte for byte against the merge base.

**`hKum` is true and proved in the PR** (`PoleS12.kummerSelmerM`, standard axioms). It stays a hypothesis because
of an import clash, which I confirmed: `scratch/pc90-review/Compose.lean` imports `OneProof.Main` and
`PoleCompletenessFromRCGenuineFinal` and fails with "environment already contains
'WeierstrassCurve.Affine.divisorSum'". The two definitions are Tau Ceti's `…/FunctionField/Divisor/Sum.lean` and
the vendored AnthropicFLT `Def_WeierstrassCurve_GenusOnePic0`. Main.lean's docstring states this correctly.

## (1)–(2) Build, axioms, forbidden tokens

| check | result |
| --- | --- |
| `lake build ZInQKernel.OneProof.Main ZInQKernel.MainGreenTao` | success, 16114 jobs, 0 errors |
| `lake build` of the 50 PR modules (`scratch/pc90-review/pr-modules.txt`) | success, 16166 jobs, 0 errors |
| `#print axioms frozenTarget`, the MainGreenTao headline, `poleCompleteness_of_restrictedConverseGenuine_mw` (`Compose2-output.txt`) | standard |
| `#print axioms` on 19 more (`Axioms-output.txt`: `…_final`, `kummerSelmerM`, `kummerSelmerM_proof`, `…Genuine`, both `matrixRealization`, both `dimThreeCount`, `simultaneousConstruction`, `mordellWeilM`, `descentGlueM`, `lemma54_of_leaves`, `Z2Corank.unique`, the two NonVacuity theorems, `selM_finite`, `localGoodUnram`, `localTwo`, `localGood`) | standard |
| grep `sorry\|admit\|axiom\|native_decide\|implemented_by\|extern\|unsafe` in the PR's .lean files | none |
| PR .lean files in `scratch/upstream/baseline-lean-files.txt` (pinned) | none |
| (7) `simp only [polePoly_eq]` in `PoleRC/Rescale.lean` L46 (commit f73be6ae2 replaced `simp only [polePoly]`) | builds (`PoleRC.Rescale`, 92 s); `Manuscript.polePoly` is an `abbrev` of `ZInQ.polePoly` (`Hypotheses/PoleManuscript.lean:29`) |

## (3) Each leaf against the TeX

| hypothesis | TeX | match | rating |
| --- | --- | --- | --- |
| `RestrictedConverseGenuine` | `hyp:RC` L1005–1011 | exact: ℓ > 0 squarefree, ℓ ≡ 11 (12), `Z2Corank (selmerTwoPower (curve ℓ)) 1 → AnalyticRankOne (curve ℓ)`; `curve ℓ = ⟨0,2ℓ,0,−3ℓ²,0⟩` is y² = x(x−ℓ)(x+3ℓ) | the manuscript's own theorem (Sections 7–9); open; not a literature leaf |
| `Lemma54` | `lem:corank` L1072–1084 | exact: `IsElliptic`, `#E(ℚ)[2] = 4` (full two-torsion), `#Sel₂ = 8` (dim 3; `Nat.card = 8` forces finiteness) → `Z2Corank Sel_{2^∞} 1` | **not printed form.** The PR calls it a "printed leaf", but it is the manuscript's lemma, proved from Cassels–Tate (Poonen–Stoll, cited at L1081 with no theorem number) and the Kummer sequence. It is true (STANDARD) and genuinely stated. Better: cited glue |
| `BCDTThmA` | L1092 `\cite[Theorem A]{bcdt}` | `∀ E/ℚ elliptic, IsModular E`. `IsModular` = some weight-2 cusp form on Γ₀(N) whose q-coefficients equal Mathlib's `E.LFunction n` for n ≥ 1. Mathlib's bad-prime factors (split 1−T, nonsplit 1+T, additive 1) match the newform's a_p | a consequence of the print (keeps less than a newform of conductor level); printed form, fine |
| `KolyvaginThm1` | L1093 `\cite[Theorem 1, pp. 4–5]{kolyvagin}`; Lemma 5.5 L1086–1088 states r ≤ 1 | the r = 1 case: `IsElliptic → IsModular → AnalyticRankOne → rank = 1 ∧ Finite (sha E)`; only the rank is used | **a consequence of BCDT + Kolyvagin together, not of Kolyvagin's theorem alone.** Kolyvagin's "modular" is a Weil parametrization (kolyv-cst-printed §5); passing from the L-series form `IsModular` to a parametrization needs more, but BCDT gives every E/ℚ a parametrization, so the statement is true. The source is an MPIM preprint, not a refereed print. Locator UNVERIFIED (not read) |
| `KummerSelmerM` | not in tex; Silverman X.1.4 (S12 L242; the manuscript's Silverman bibitem names Chapters IV and VII only) | `#selmerAt (curve ℓ) 1 = (SelM ℓ).ncard` for ℓ > 0 squarefree | glue, **proved** (`PoleS12.kummerSelmerM`, from the bijection `SelMTauCeti.card_selmerAt_curve`, every ℓ > 0); a hypothesis only because of the import clash |

**Analytic rank is not vacuous.** `AnalyticRankOne E` (`Hypotheses/PoleManuscript.lean:71`) says there is an
entire F equal to Mathlib's `E.LSeries` on Re s > 3/2 with `analyticOrderAt F 1 = 1`. `WeierstrassCurve.LSeries`
is the genuine Euler product of the minimal model at each prime: a_p = q + 1 − #E(𝔽_q) with the point at infinity
counted, and the bad factors as above (read in `Mathlib/AlgebraicGeometry/EllipticCurve/LFunction.lean`).
* Satisfiable: e.g. 37a1 has analytic rank one (STANDARD; Lean cannot prove analytic continuation today).
* No junk: the definition does not degenerate (F ≡ 0 has order ⊤, not 1).
* If it were unsatisfiable, `hRC` would be false, not vacuous, so soundness is unaffected either way.
* Non-vacuity on the Selmer side is proved (`SelmerTwoPowerNonVacuity.lean`: `Sel₂(E_ℓ)` contains a nonzero class,
  and some class of `H¹` lies outside `Sel₂`; `selM_finite`).

**Mazur–Rubin is a route departure, off `frozenTarget`'s path.** The manuscript does not cite Mazur–Rubin. A
case-insensitive grep finds "Mazur" only in Mazur's conjecture (L47, L84, L6470ff) and Fontaine–Mazur (L11041),
and no "Rubin" at all. The proof of `lem:corank` cites only Poonen–Stoll (L1081).

Commit 30567231a proves `Lemma54` from three statements (`lemma54_of_leaves`, standard axioms):
* `MazurRubinParityTwo`: the PR's own docstring says the print asserts it inside a proof, and the reference it
  gives ([MR2] Prop. 2.1) is stated for odd p. So at p = 2 it is **not a printed statement**;
* `SelmerCofinite` and `KummerSelmerRelation` (textbook glue).

`frozenTarget` takes `Lemma54` directly, so this alternative changes nothing in the headline. It should be
labelled a route departure if it is ever used in place of `h54`.

## (4) Manuscript check, tex L1019–1121

Source column: **MS** = the manuscript text suffices; **S12-only** = the step is supplied only by the retained
supplement S12 (not the manuscript).

| # | tex (S12) | step | proof covering it | verdict | source |
| --- | --- | --- | --- | --- | --- |
| 1 | L1020–1024 | divisors of 2730 give all real/2/3-adic signatures; 5, 7, 13 a basis | `PoleRC.bookkeeping` | OK | MS |
| 2 | L1024–1032 | β ≡ 17, θ ≡ 1 (24), disjoint, mutual local squares | `bookkeeping` | OK | MS |
| 3 | L1033–1035 | "simultaneous construction in S11–S12" | `PoleS12.simultaneousConstruction` | gap filled | S12-only (S11 not needed, not available) |
| 4 | L1036–1040 (S12 L267–315) | `s_i, λ_i, K`, target `ker K = ⟨1, 1_β⟩`, λ ∉ im K | `MatrixConditions` | OK | MS |
| 5 | L1041–1043 (S12 L567–571) | d−1 slots (0,0), one q₀ (1,1) (residues 1, 7 mod 12) | `matrixRealization` | OK | MS |
| 6 | L1044 | cross-block columns e_i + e_d | `block_injOn` (columns e_b + e_{b*}) | OK | MS |
| 7 | L1045–1048 (**S12 L586–591**) | `K♯ = K + λaᵗ` | `sharp_targets` | gap filled: tex never defines a; S12 L586–587 sets a = e_{q₀} + e_{b*} (aᵗ1 = 0, aᵗ1_B = 1), and `K = K♯T` with `T = Id − 1_B aᵗ` gives both targets from `ker K♯ = ⟨1⟩`. Rechecked by hand (log): `K♯1 = 0` uses Σλ = 0 on the support; `K♯1_B = λ` uses `K1_B = 0` | **S12-only** |
| 8 | L1046–1052 (S12 L606–652) | deleting q₀ gives [[D₁,C₁],[C₁ᵗ,0]], 1ᵗD₁1 = 1, nonsingular | `sharp_ker_of_deleted`, `block_injOn` | OK. Rechecked: lower-right zero (I–I symbols 0, I diagonal = column sum of C = 0); 1_BᵗA1_B = Σ_B λ = 1; D₁ is not diagonal | MS (argument), S12 for the prescriptions (L638) |
| 9 | L1052–1053 (S12 L654–677) | adding supp θ keeps the block | `hblockJ` in `matrixRealization` | gap filled: needs Σ_J [q_j/q_i] = 0 (S12 L564) and I–J symbols 0 | S12-only |
| 10 | L1053–1056 (**S12 L677–688**) | free q₀-symbols toggle the J-diagonal; full-product coefficient 1; one assignment for both supports | `exists_toggle_injOn` (pc-s12), `toggle` (cloud) | gap filled. Rechecked: flipping [q₀/q_j] flips its reverse (fixed reciprocity discrepancy). After deleting q₀ only K_jj changes, so det is multilinear with leading coefficient det M₀ = 1. The bits do not touch the Q₀ matrix, which is why one assignment serves both supports; the tex does not say so | **S12-only** |
| 11 | L1057–1058 (S12 L692–703) | reciprocity, CRT, Dirichlet realize the symbols | `exists_prime_lsym` (Mathlib CRT + Dirichlet) | OK | MS |
| 12 | L1060–1062 (S12 L381–394) | shape (3^δ∏q^u, ∏q^v) | `necAt_S12` | gap filled | S12-only |
| 13 | L1063–1066 (S12 L396–407) | the three local equations | `eqs_of_localBad`, `e4_of_mod3` | OK | MS |
| 14 | L1067–1068 (S12 L409–433) | matrix properties force v = 0, δ = 0, u ∈ ker K | `kmat_forces`, `e3_of_e2` | gap filled | S12-only |
| 15 | L1069–1073 (S12 L436–454) | (β,1) is local everywhere and independent | `cand_mem_S12`, `localGoodUnram` (ON THE SPOT reduction mod p + Hensel, standard, labelled in the file) | gap filled | S12-only |
| 16 | L1072–1084 | lem:corank | leaf `Lemma54` | OK (cited; argument STANDARD) | MS + Poonen–Stoll |
| 17 | L1086–1106 | lem:forward-rank | leaves `BCDTThmA`, `KolyvaginThm1` | unverified (prints not read; Kolyvagin is a preprint) | MS + cited |
| 18 | L1107–1109 | "rank one and finite Ш, hence Ш[2] = 0" | `descentGlueM` (counting: #E/2E = 8 = #SelM, Kummer map injective, hence onto) | OK; finiteness of Ш is not needed. ON THE SPOT (pc-s12 correction (c)), standard | MS |
| 19 | L1110–1112 | Kummer class from rational points, abscissa class β | `point_of_locM` | OK | MS |
| 20 | L1112–1121 | rescaling to E_{nH}, eleven witnesses, w = (eHz)⁻¹, θ = 1 reuse | `witnesses_of_points`, `poleCompleteness_of_crm` | OK | MS |

No error found in tex L1019–1121 or in the S12 passages used. My hand checks of rows 7, 8 and 10 agree with S12
and with both Lean proofs.

## (5) Duplicates: pc-s12 against the cloud

| statement | pc-s12 (round 2) | cloud | comparison |
| --- | --- | --- | --- |
| `PoleRC.MatrixRealization` | `PoleS12.matrixRealization` (`PoleS12/Realization.lean`, `SharpAlg`, `Choice`) | `PoleRC.Simul.matrixRealization` (`PoleRC/Simultaneous.lean`, `SimulLinAlg`) | **same type.** Both use S12's a = e_{q₀}+e_{b*}, columns e_b+e_{b*}, the toggle. The cloud's `block_nonsing` is stated for any support P' ⊇ B∪I with zero B-row sums, slightly more general; pc-s12 proves the toggle by kernel induction. Same strength. **On the path: pc-s12's** |
| `PoleRC.DimThreeCount` | `PoleS12.dimThreeCount` = `dimThreeCount_S12 localGoodUnram`, using necessity `necAt_S12` and only the "if" half at good primes | `PoleRC.dimThreeCount` = `dimThreeCount_of_local localTwo localThree localBad localGood` | same type. The cloud's route proves more on the way: the four full local images (iff) at 2, 3, q∣ℓ and good p are standalone stronger theorems. pc-s12's route needs less. **On the path: pc-s12's** |
| local image at good p | `LocalGoodUnram` (if-half) | `LocalGood` (iff) | **the cloud's is stronger.** Both prove the if-half by reduction to 𝔽_p plus Hensel, with independent copies of the 𝔽_p Kummer map (`PoleS12/GoodF/KummerF.lean` vs `PoleRC/KummerF.lean`), essentially the same proof |
| Kummer comparison | none (only Kummer maps over a general field) | `SelMTauCeti.card_selmerAt_curve` (bijection `SelM ℓ ≃ Sel₂(E_ℓ/ℚ)`, every ℓ > 0) | cloud only; stronger than `KummerSelmerM` (no squarefree hypothesis) |
| Mordell–Weil | hypothesis `MordellWeil` (all E/ℚ) | `mordellWeilM` (proved for E_ℓ) | the cloud's removes pc-s12's `hMW` |

Recommendation (not a blocker): one copy of each duplicated proof can be dropped after landing, e.g. keep the
cloud's local images (stronger) and pc-s12's path. Both pass the axiom check.

## (6) Does anything shorten `frozenTarget`?

* **pc-s12's statements: no.** pc-s12's final theorem has one hypothesis more (`MordellWeil`). The PR already
  uses pc-s12's simultaneous construction with the cloud's `mordellWeilM`.
* **kolyv-cst-printed's `KolyvaginThm1Printed`** (r ≤ 1, as cited at L1093): it can replace `hK`, but the count
  stays the same: one leaf for one leaf. It is closer to the citation, since it states the r ≤ 1 theorem that Lemma
  5.5 cites, and the proof of Theorem 5.3 needs its r = 0 case. Compiled:
  `scratch/pc90-review/Compose2.lean` (`frozenTarget_printed`, with `KolyvaginThm1Printed` and
  `kolyvaginThm1_of_printed` copied from c12a1a03d), standard axioms.
* **The only real shortening is dropping `hKum`.** It is proved, but `scratch/pc90-review/Compose.lean`
  (`frozenTarget_noKum`) fails at the imports (divisorSum clash; output in `compose-output.txt`). Any one of these
  would give the five-hypothesis form `(r t l hRC h54 hB hK)`:
  * rename one of the two `WeierstrassCurve.Affine.divisorSum`;
  * give `SelMTauCeti` a proof that does not import Tau Ceti's Weil pairing;
  * make the H chain stop importing the vendored AnthropicFLT definition.

## Known issues (sources and PR)

1. **PR tree contains S12** (`scratch/upstream/parity-frozen-4eaee875.tex`, commit 4b2595108, whose message says
   the opposite). Blocker; see the verdict.
2. **tex L1045–1047:** the vector a of `K♯ = K + λaᵗ` is undefined (S12 L586–587 defines it). tex L1047 writes
   D₁, which suggests a diagonal block; it is a general matrix (S12 L662).
3. **tex L1053–1056:** "a single Boolean assignment works on both supports" is right only because the toggled bits
   leave the smaller support's matrix unchanged (S12 L688). The tex does not say so.
4. **tex L1033:** S11 is cited but not available. S12 alone covers the construction.
5. **tex bibitem `kolyvagin` L11163–11166** is an MPIM preprint, not a refereed print. **bibitem `silverman`
   L11144–11145** names Chapters IV and VII only, while the Kummer identification is Chapter X (X.1.4).
6. **`PoleS12/Leaves.lean` stale line numbers:** it cites tex L1099/L1100 for BCDT/Kolyvagin (actually L1092/L1093),
   L1088 for Poonen–Stoll (actually L1081), and `lem:corank` as L1076–1093 (actually L1072–1084).
7. **`docs/research/pc-s12.md`, Manuscript check row 7:** cites S12 L581–583 for a; the definition is at L586–587.
8. **`PoleRC/Count.lean` docstrings** of `LocalTwo/Three/Bad/Good` still say "not proved in Lean"; they are proved
   (`LocalTwo.lean`, `LocalThreeBad.lean`, `LocalGood.lean`).
9. **Leaf labels:** `Lemma54` is labelled "printed leaf" but is the manuscript's own lemma (see (3)).
   `KolyvaginThm1` over `IsModular` follows from BCDT + Kolyvagin, not from Kolyvagin alone.
   `MazurRubinParityTwo` is not printed at p = 2.
10. **Merge base** 67950e82, not 5f1fac79 (clean 3-way merge).
11. My own slip: `scratch/pc90-review/build-main.txt` (raw build log, about 113k lines) was committed once by
    mistake on this review branch, then untracked. It is not part of PR #90.

## New leaves rated

This review adds no leaves. Ratings of the PR's leaves are in (3): `BCDTThmA` is printed form (a consequence).
`KolyvaginThm1` is a consequence of two prints together. `Lemma54` and `KummerSelmerM` are not printed form:
the first is a manuscript lemma, the second is glue and is proved.

## Files

`scratch/pc90-review/`:
* `log.md`;
* `Compose.lean` (fails at the imports, as expected; `compose-output.txt`);
* `Compose2.lean` (compiles; `Compose2-output.txt`);
* `Axioms.lean` (`Axioms-output.txt`);
* `pr-modules.txt`;
* the raw build logs, which are git-ignored.
