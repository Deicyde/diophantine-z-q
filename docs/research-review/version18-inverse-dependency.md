# Version 18 inverse-theorem dependency change

This record accompanies the new `manuscripts/quartic_v18.tex`, SHA256 `e594eba7c9634f445185f507f05d7436ea6e6b1acc0c226051ab40e3767aee12`, relative to the prepared source-application sequence, source SHA256 `53ca7ea3490f4cb476c03859ccaed4a2ce692b37ae93fbe14e6d43326bcbdc7b`. It records a changed proof route for Protocol B review, not an independent acceptance. The ordinary GI target and the retained increment-group theorem are unchanged. Versions 16 and 17 and the polynomial are not edited. The other status and prose changes split out of PR107 are not part of this change.

## Source editions and scope

The Candela–Szegedy source actually checked is [arXiv:1902.01098v3](https://arxiv.org/abs/1902.01098v3), 13 March 2022, 39 pages. The arXiv record calls it the final author version to appear in Crelle. The 42-page journal edition was not obtained or compared. All Candela–Szegedy page locators below are author-v3 locators, not asserted journal-page locators. The journal reference is Crelle 789 (2022), 1–42, DOI 10.1515/crelle-2022-0016.

The other nilspace sources are the official [compact nilspaces](https://discreteanalysisjournal.com/article/2106-notes-on-compact-nilspaces) and [algebraic nilspaces](https://discreteanalysisjournal.com/article/2105-notes-on-nilspaces-algebraic-aspects) papers of Candela, Discrete Analysis 2017:16 and 2017:15. The retained algebraic polynomial-map facts are Green–Tao–Ziegler, Annals 176 (2012), Corollary B.4, Proposition B.6 and Lemma B.9. They are not among the statements affected by the authors' erratum. The old Appendix C step claim is not a premise.

## Supplier-to-consumer checks

| Consumer in this source | Input and exact derivation |
|---|---|
| GI target, line 29549 | For each fixed k and delta, the same finite family of connected simply connected groups of step at most k, fixed smooth metrics, uniform Lipschitz bounds and positive linear-orbit correlation. The interval norm and conjugation conventions are unchanged. |
| Toral witnesses, line 29648 | CS Definitions 1.2–1.3, p.3; Definition 5.1, p.23; Theorem 5.2, p.26; Theorem 6.1 and its factor-consistent metric setup, pp.26–27. Choose all balance/prime thresholds before the arbitrary positive function b and before M. For large primes, complexity and balance imply torality. The finitely many small primes use Fourier inversion. Fix metrics and cube-probability metrics per isomorphism class and transport them through the chosen isomorphism. |
| Fixed models and lift, line 29734 | Candela Theorem 2.9.17 and Remark 2.9.18, pp.51–52, give the connected translation filtration and covering construction. The new text writes out compactness of each filtration quotient, using upper-face factorization and a Baire open-orbit-map argument, and proves that the cover preserves degree and cubes. CS Proposition 6.3, p.27, lifts to all integers; Lemma A.5, p.34, and GTZ B.4 check the right-difference convention. |
| Uniform metric comparison, line 29860 | A finite-net weighted interpolation of the equicontinuous pullbacks produces globally one-bounded Lipschitz tests. The bound depends only on the fixed model, metric, initial Lipschitz bound and approximation tolerance. It does not assume the nilspace isomorphism is smooth. |
| Interval transfer, line 29910 | Choose a prime between 2^(k+1)N and 2^(k+2)N. The explicit cube bijection proves the normalized zero-extension relation. The threshold eta=delta*2^(-k-2) and fixed approximation loss yield a positive correlation constant independent of N. |
| Normalization and linearization, lines 30016 and 30120 | Retain bounded normalization, the ordinary degree case of tautification and the increment-group proof. Its P1 semidirect construction keeps step k. Add the intrinsic-to-ambient distance comparison on the compact fibre, needed for its Lipschitz extension. The new witnesses satisfy every geometric and polynomial input. |

The extra compactness exposition is part of the proposed proof and needs review with the rest of this change. Prior model reports are not an acceptance of edits subsequently made during integration.

## Removed material and retained arithmetic

Every label in the old 6,267-line inverse-proof part was searched throughout the manuscript, along with macros, citations and plain-text descriptions. Of 104 old labels, only the main GI part label has outside mathematical consumers. Two other outside references were navigation links into the superseded proof and have been replaced. No local macro has an outside consumer. The downstream prime and Gaussian arguments consume the ordinary finite-family linear GI target, not the nilcharacter/rank machinery.

The integration removes 89 old labels and 23 unused bibliography entries belonging to that route. All remaining references resolve. It replaces the old current-route descriptions, retaining the same mathematical input at the consuming passages. The retained normalization is explicitly restricted to the ordinary degree case; no unused multidegree or vertical-character conclusion remains with its proof removed.

The full old proof remains at [review-archive-v17, Version 17, starting at line 28931](https://github.com/elliotglazer/diophantine-z-q/blob/review-archive-v17/manuscripts/quartic_v17.tex#L28931), commit `005b17abfbefd8bee7b34f3bbe8f5aabf872eb1f`. Its 6,267-line text matches the pre-cleanup Version 18 part after LF normalization, SHA256 `d399a7d7a7e001d040b96a14799b703ecc5a027a1a9207e018d823ce0c1e6d00`.

The arithmetic sections originally at Version 18 lines 35627–35715 remain in full, now beginning at line 30510. This PR preserves their bytes from the source-applications base, SHA256 `0210a3ba65241f67994728cdbb6960d08c1bbeb5d044537de7dacee635a78333`. That preceding, separate change clarified Silverman's Frobenius convention and corrected the Gross–Zagier singular-moduli key. Neither is a removal or change of arithmetic route in this PR.

H170's original propagation obligation remains recorded in `version18-cleanup-status.md`. This candidate removes the old Section 12 proof with its superseded route; removal is not a correction certificate for the historical copies. The archived evidence and conditional review keep their original scopes. The revised status record distinguishes the removed current proof from historical obligations and does not claim gate acceptance in advance.

## Review provenance and verification limits

Elliot authorized this route and required Carbon's source/proof check and Fable's no-objection confirmation before a PR. Carbon's report of November 14 checked the author-v3 CS statements, the official Candela sources and the GTZ appendix facts against the note and retained linearization. Fable's November 15 UTC confirmation raised no objection, retained the unavailable print-edition comparison and requested the explicit metric convention and short explanations now included. These were model reviews of the precursor note and extracts. This integrated manuscript requires its own two-reviewer Protocol B run.

The full candidate compiles in three LaTeX passes with no unresolved citations/references. Its validation PDF has 4482971 bytes, SHA256 `392a5969390f5aaad560aaf8303cc3c9b75a4563abd0579095074b377aaaa3bb`. Exact target and increment-theorem comparison, label/consumer checks and arithmetic preservation checks passed. These checks do not constitute formal verification or remove the stated source-edition limitation.


## Journal-source comparison after inverse adoption

PR118 merged at f7b803e3252fa955ab6dcdc2ac3e756a03fde184, with head 630a67ae874ceb28e50a686be0d811b780b8fb8b. The owner overrode four source-access findings after the local journal comparison and the already recorded Candela-source checks. App check 132948112036 succeeded. This was acceptance by owner override, not unanimous model acceptance.

On November 15, 2026, the owner supplied the 42-page Candela-Szegedy journal edition, DOI 10.1515/crelle-2022-0016, PDF SHA256 89f308b0d1ac435f9e895b2ba79938d6e8b9c61c1ede2aa55e4caa18c6a25580. Astra compared the cited statements with the author version and their uses. Fable independently compared the printed journal statements with the PR118 uses and confirmed agreement. The comparison is [recorded on PR118](https://github.com/elliotglazer/diophantine-z-q/pull/118#issuecomment-6900813514). This did not re-audit every proof in the paper or certify the whole manuscript. The PDF stays outside the repository.

The cited hypotheses and conclusions agree. The cleanup now uses the journal locators: Definitions 1.2 and 1.3, page 3; Definition 5.1, page 25; Theorem 5.2, page 28; Theorem 6.1 and equation (6.1), page 29; Proposition 6.3, page 30; Lemma A.5, page 36. It removes the now-obsolete inability-to-compare statement from the exposition and bibliography. These are source-edition and locator changes; no theorem statement, equation, construction or proof route changes.

The earlier source-access record describes the evidence available when the inverse PR was prepared. This dated addition supplies the later comparison without rewriting that history or treating an owner override as an independent reviewer's acceptance.

## Journal Section 1 numbering detail

The supplied journal PDF prints Theorem 1.7 on page 5, with the same finite-family, smooth-metric, periodic polynomial-orbit statement as author-v3 Theorem 1.7 on page 4. The manuscript's reference to 1.7 is therefore unchanged and now specifies journal page 5. There is a later numbering difference: the journal inserts Remark 1.9 on page 5, so the connected-cube-set/toral result is Theorem 1.10 on page 6; author v3 labels that result Theorem 1.9. This does not shift Theorem 1.7. The former comparison concerned the cited statements, not an assertion that every item in Section 1 has identical numbering. The derivation uses the explicitly listed Theorems 5.2 and 6.1 and Proposition 6.3; it does not infer connectedness of every filtration group from the short wording of Theorem 1.7. Root checked the supplied PDF directly; this note does not claim that a gate reviewer accessed it.
