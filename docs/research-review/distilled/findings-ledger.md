# Findings ledger

Part 1 lists objections raised from outside the project's own agent pool. Part 2 lists substantive findings extracted from the project's internal written reviews. Statuses are as recorded by the cited file; they have not been reconciled against later records. See README.md for the summary and limits.

# Part 1: outside audits and objections

Compiled 2026-11-13 from the repository checkout `C:\Users\glaze\Documents\Codex\2026-11-02\lo\work\pr30-completion-20261113\repository` (paths below are relative to it) and the Fable audit PDFs in `C:\Users\glaze\Downloads`. Read-only; no project script was run.

Conventions used in the table.

- **Version names.** "N4 packet" = the 4 Nov 2026 drafts Fable 5.1 audited (`manuscript_v2.tex`, `main.tex` SHA 36a2e9a9..., `main_v3.tex`). "11/5 MS" = the November 5 manuscript (`diophantine_zq.tex`, huge-polynomial construction). V4 = `quartic_4973.tex`, V6 = `quartic_962.tex`, V10...V17 = `manuscripts/quartic_vNN.tex`.
- **Status.** RESOLVED = a repair, replacement, rebuttal or withdrawal is on record. PARTIAL = part is on record, part is not. OPEN = the record itself says it is not closed, or the questioned text is unchanged in V17 and no decision is recorded. UNLOCATED = I could not find a resolution record.
- **Independent check.** "Fable" and the Issue 2 reviewer are outside the Astra/Codex pool. Astra reviewers named by path (e.g. `/root/astra_bl5_models`) are the project's own pool; where they are the only checker I say "internal only". The repository itself states repeatedly that internal model reviews are not independent human review.
- Line numbers in Fable reports refer to the source Fable audited (V15 = `research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex` unless stated).

### 1. Objections in date order

| ID | Date | Raised by | Point questioned | Raised against | Resolution (type; version) | Where the resolution lives | Checked by someone other than the fix's author? |
|---|---|---|---|---|---|---|---|
| E1 | 4 Nov | Fable 5.1, RC audit (packet row 8) | Lemma 8.10 / eq. (4.7) of the restricted-converse (RC) chain: `l_q/e_q^2 = 1+2v_q` with `v_q` in `O[G]` needs `e_q = a_q - z - z^{-1}` to be a unit, i.e. a nonzero inner-limit exponent at every graph prime; no such condition was stated. Fable flagged it as the one item that "could be a genuine missing hypothesis". | N4 packet `main.tex` | Repair (added hypothesis): the moving character is prescribed with `chi_i(Fr_q)=1` at every graph prime by putting the graph primes in Prop. 8.5's active list. Landed in the 4 Nov "full justifications" revision, carried into the 11/5 MS. | RC section (Def. 8.1 preamble; paragraph "Simultaneous prescriptions and local lifts"). The 4 Nov packet itself is not in the checkout. | Yes: Fable re-derived the repair the same day ("Verified"), and on 6 Nov confirmed it unchanged in V4. |
| E2 | 4 Nov | Fable 5.1 (row 5) | Prop. 8.6 paired functional: integrality rests on a "fixed old-support exponent a" that is named but not computed and must not depend on G; it is load-bearing in (5.5) and in `c_det` of (5.9). | N4 packet | Repair: paragraph "The fixed old-support lattice and the exponent" proves `a = 0` via an integral homotopy equivalence. 4 Nov revision. | RC section, Prop. 8.6 and following | Yes: Fable re-derived it; confirmed closed again 6 Nov. |
| E3 | 4 Nov | Fable 5.1 (row 11) | Prop. 9.6 (bound (5.5)): the quadratic-character exception at height-one primes was "a sketch"; "a first switch introduces the other sign" was not derived. | N4 packet | Repair: new two-switch proof, "Height-one regularity, including quadratic specializations". 4 Nov revision. | RC section, Prop. 9.6 | Yes: Fable ("Verified inference"). |
| E4 | 4 Nov | Fable 5.1 (rows 9, 12) | Lemma 9.2's constant `56 omega(2N)+8A+56j+70` not justified; in Lemma 9.7 / Prop. 9.8 the claim that class, functional and determinant comparison each carry at most one denominator `Upsilon` was asserted, not displayed, and `d_q <= 4` unchecked. | N4 packet | Repair: new proof of Lemma 9.2 and expanded proof of Prop. 9.8. 4 Nov revision. | RC section, Lemma 9.2, Prop. 9.8 | Yes: Fable ("Verified"; constant "recomputed, unchanged"). |
| E5 | 4 Nov | Authors (self-reported), recorded and assessed by Fable 5.1 (rows 16/17) | Odd theta phase (App. F.2): the sentence that raising the dyadic level makes the theta multiplier and the metaplectic lifts agree is false (`-I` lifts to an element of order 4 since `(-1,-1)_2 = -1`). | N4 packet | Repair: replaced by an eigenvalue comparison under one lift (`NORMALIZATION.tex`, ranks/odd_metaplectic). 4 Nov revision. | App. F.2 of the 11/5 MS | Partly. Fable "confirmed the falsity and the structure of the fix, not the full local computation"; it never re-derived the local Weil-representation computation. Fable's 6 Nov audit lists "F.2 lift independence" as closed. |
| E6 | 4 Nov | Fable 5.1 | Exposition of RC: symbol, seed and address definitions and the address lemma are used in Sec. 7.2 before being defined, the address lemma is never stated, and Secs. 7-9 and Apps. E-G contain no stated lemma ("a referee cannot cite or test a claim that is never stated as one"). Also the G.4 cross-term sentence (row 8 of the later table) and a one-line statement of the lift-independent comparison in F.2. | N4 packet | Repair (exposition). Later texts state numbered lemmas (Fable's own later table cites Defs 7.4-7.10, Lemmas 7.7, 7.9, 7.11-7.12; V15-V17 have a subsection "Coefficient symbols and the finite address lemmas"). Fable's 6 Nov audit lists the G.4 cross terms and F.2 item as closed on 4 Nov. | RC section of 11/5 MS and later | Yes for the items Fable lists as closed. I did not find a record tying each individual exposition request to an edit. |
| E7 | 4 Nov | Fable 5.1 | The role of `l = 11 (mod 12)` in RC (Theorems 5.2-5.3) is never stated; the proof of RC does not invoke it. Fable asked for a sentence saying the pole-completeness construction produces that family. Also: mark the K-split contradiction (Sec. 7.5, G.4) as a specialization of the source's argument. | N4 packet | K-split: v2 added "The contradiction is obtained only after this conditional deduction" with the curve-specific conditions (Fable's v1/v2 comparison). `11 (mod 12)`: no record found. | - | K-split wording seen by Fable. **`11 (mod 12)` sentence: UNLOCATED.** |
| E8 | 4 Nov, restated 6 Nov and 10 Nov | Fable 5.1 / 5.2 | Headline theorems are stated as unconditional while, on what was checked, they are conditional on RC and the height estimate. Theorem `thm:quartic` (and `thm:v6-962-polynomial`) says "with precisely the inherited arithmetic hypotheses and qualifications" without naming them; README headline unqualified. | N4 packet; V4; V6 | Not adopted. V17 line 15057 still reads "With precisely the inherited arithmetic hypotheses and qualifications of...". README carries scope paragraphs separately. No recorded decision. | - | **OPEN (text unchanged, no decision record).** |
| E9 | 4 Nov | Fable 5.1 (row 1e) | Kato's Thm 13.4 at `p = 2`: hypotheses needed confirming. Fable confirmed the printed statement (Asterisque 295, p. 226: parts (1)-(2) need only (i)-(v); `p != 2` only in (3)), but left "not validated": Kato 6.6, 9.7, 8.12, 13.5(2) at `p = 2`, the integral coefficient map, unsmoothing, Weierstrass comparison. | N4 packet | Citation confirmed by the auditor. The remaining Euler-system items were overtaken by E19 and E25. | Fable RC audit, p. 3, 8 | Citation: yes (Fable). Construction/normalization: see E19, E25, E38. |
| E10 | 4 Nov | Fable 5.1 | Height section (Sec. 4) replaced the source's route by discriminant 6, six contacts and von Kanel-Kret; "the two unverified pillars of the main theorem now have different provenance". | N4 packet | Replaced dependency: von Kanel-Kret removed; height argument rebuilt with Berger's theorem, explicit twist/weight and conductor steps. 11/5 MS (historical "revision 2"). | `docs/revision-2.md`; `docs/reviews/height-replacement/REPORT.md` | Four Astra reviewers (internal only). Fable later read the six-contact proof "in full" (4 Nov, per its 6 Nov report) and the five-contact proof (6 Nov), with cited theorems at citation level. |
| E11 | 5 Nov | Owner-ordered theorem-application audit, finding F001 | Height argument, de Rham step (application A009): Faltings 1988 gives only a Hodge-Tate decomposition, not the de Rham property needed before Berger and Pan. Source-strength mismatch. | 11/5 MS (SHA cb1148cd...) | Replaced dependency: Scholze Cor. 1.8 (+ corrigendum, Thms 9.1/9.3), Brinon-Conrad 5.2.1/6.3.3/6.3.8, inserted as Lemma H.1. Historical "revision 3" (5 Nov). Superseded in V14: the de Rham descent appendix was removed and `lem:qm-modularity-descent` (Pan at 5 via Calegari) put in its place. | `docs/theorem-application-audit/FINDINGS.md` F001; `evidence/parallel-a009-independent.md`; V14+ Sec. "Modularity after rational scalar descent" | "Separate Astra review" accepts the bounded repair (internal only). Fable (10 Nov) checked the V14 replacement lemma's logic; cited theorem at citation level. |
| E12 | 5 Nov | Theorem-application audit, F002 | Silverman 2009 III Ex. 3.7 and X Prop. 4.9 print a wrong sign / `a^2-b` for `a^2-4b`; the manuscript's formulas are right but the citation is to misprinted statements. | 11/5 MS | Replaced citation: Sutherland lecture statement plus a specialized recurrence calculation and direct proof of both squareclass kernels. Revision 3. | FINDINGS.md F002; `evidence/closure-batch-002.md`, `-010.md` | Closure batches (internal). Independence of the batch reviewer from the repair author is not stated in what I read. |
| E13 | 5 Nov | Theorem-application audit, F003 | Claimed that the rank-one conclusion had to wait for the two-prime torsion calculation. | 11/5 MS | Withdrawn by the audit itself (rebuttal: `|T/2T| = |T[2]| = 4`, so index 8 already gives rank 1). | FINDINGS.md F003 | n/a (withdrawn). |
| E14 | 5 Nov | Theorem-application audit, F004 | Kummer Selmer calculation over imaginary quadratic K cited Nekovar 5.7.1.6-7 (the `p=2`, real-places case) where 5.1.1-5.1.6 with Thm 6.3.4 applies. | 11/5 MS | Citation corrected; argument unchanged. Revision 3. | FINDINGS.md F004; `evidence/closure-batch-006.md` | Closure batch (internal). |
| E15 | 5 Nov | Theorem-application audit, F005 | Evaluation argument could be read as assuming injectivity of limiting cohomology in order to prove it (order of selecting the finite detecting lists). | 11/5 MS | Repair: lists chosen and padded at finite stages before the limit. Revision 3. | FINDINGS.md F005; closure batches 6-8 (A076, A067) | Closure batches (internal). |
| E16 | 5 Nov | Theorem-application audit, F006 | Custom derivative local conditions: the text did not supply all chain-level data (tame complex, uniformizer, restriction/corestriction matrices, homotopies). A substantive missing justification. | 11/5 MS | Repair: construction added; extra factor of two kills the shear term. Revision 3. | FINDINGS.md F006; `evidence/parallel-forward-modularity-a080-report.md`, `parallel-theta-local-a080-local-review.md`, `parallel-forward-modularity-a080-local-second-review.md` | "Independent second review" by an Astra agent (internal only). |
| E17 | 5 Nov | Theorem-application audit, F007/F008 | Conventions and source identity (both duals in Carayol; actual level-normalizing matrix; formal-log isometry radius incl. dyadic; Kolyvagin MPI/90-69 vs a different "Euler systems"; Serre, Pazuki, AFP versions); coverage gaps (Mertens, quaternion embedding results missing from inventory; stale `700X` vs `10000*2^24 X`; mutually dependent application IDs). | 11/5 MS | Corrections and inventory restructuring. Revision 3. | FINDINGS.md F007, F008; `DEPENDENCIES.md`; `MANUSCRIPT_EDITS.json` (53 edits) | A068 has an "independent second review"; otherwise closure batches (internal). |
| E18 | 5-6 Nov (issue titled "Full check of the 11/5 manuscript") | manvirjaswal, GitHub Issue 2, points 1, 3, 7, 8 | Attribution and history: Mazur 1992 priority and Conjecture 2; OpenAI's Turing-completeness result vs the many-one completeness claimed; local credit to OpenAI's two converse preprints; Robinson/Poonen/Koenigsmann history. | 11/5 MS | Attribution/novelty corrections. V10 (7 Nov). Mazur 1992 scan read directly in V11. | `docs/manuscript-revisions/version10/README.md`, `responses.json`; `docs/audit-history/issue2/`; V11 `evidence/mazur1992.md` | Yes: the reviewer rechecked V10 on 7 Nov ("All nine are addressed"). |
| E19 | 5-6 Nov | manvirjaswal, Issue 2 point 4 | RC, Kato input at `p = 2` (Sec. `sec:rc`, `ex:app-kato-system`): the cited Kato theorem needs `p` odd / different convention; justification at two missing. | 11/5 MS | Repair: direct application of Kato 1999 Thm 0.8, stronger `G_{Q^ab}` unipotent hypothesis, cyclotomic absolute irreducibility, comparison of 1999 and 2004 conventions. V10. Historical register classes this as "prior inputs; fuller connecting argument". | V10 `kato.tex`; `issue2/evidence/kato.md` | Reviewer rechecked V10: correct "except for one missing step" (see E25). |
| E20 | 5-6 Nov | manvirjaswal, Issue 2 point 2 | Determinant coordinate at the central calibration: generic rank / specialization not justified where it is used. | 11/5 MS | Repair: general Smith-decomposition lemma `lem:v10-determinant-specialization`; generic dimensions (1,1) proved before the calibration. V10. | V10 `coordinate.tex`; `issue2/evidence/determinants.md` | Yes: reviewer ("the new arguments in 2, 4 and 6 are right"). |
| E21 | 5-6 Nov | manvirjaswal, Issue 2 points 5, 6 | Multiplication section (`sec:mult`): the saved polynomial's conjugated ratios / template mapping not recoverable from the print; valuation step omitted, and the "some group has only unit factors" shortcut is false (reviewer's counterexample). | 11/5 MS | Repair of the printed argument: template/recipe dictionary; delta/alpha inequalities and trace contradiction (the full maximum-valuation proof pre-existed in the 3 Nov source). V10. | V10 `templates.tex`, `check_valuation.py`; `issue2/evidence/valuation.md`, `templates.md` | Yes: reviewer (point 6 "right"; all nine "addressed"). |
| E22 | 5-6 Nov | manvirjaswal, Issue 2 point 9 | No-seed congruence at primes outside the coefficient filter (`ex:sec7-ksplit-seed`, App. G.4). | 11/5 MS | Scope clarification at the consuming lemma. V10. | `issue2/evidence/off-filter.md` | Yes: reviewer (addressed). |
| E23 | 6 Nov | Fable 5.1, Version 4 audit | Checker's source table labels the accepted source "EXPLORATORY SOURCE" and `source-audit.json` has `source_pin_authorized: false`, while manuscript and README treat it as accepted. | V4 | Rebuttal/clarification; frozen bytes kept. Relabelling deferred to a future regeneration. | `research/2026-11-06-collaborator-notes/source-status.md`, `fable-repository-audit.md` | No independent check recorded. **PARTIAL**: the literal label is still in `quartics/quartic-4973/source-entry.json`. |
| E24 | 6 Nov | Fable 5.1 | Sec. 14 source carries comment lines "% UNAPPLIED CANDIDATE: global review and published Pan match are pending" and "% ... conditional on the separately audited field/ramification lemma", which read as live caveats. | V4 (lines 7243, 7350) | The strings are absent from V16 and V17 (still present in the archived `quartic_4973.tex`). I found no record of when or why they were removed. | - | No record. Resolution record **UNLOCATED** (text is gone). |
| E25 | 7 Nov | manvirjaswal, Issue 2 follow-up | V10's Kato 1999 route: the classes (K8) are defined only on Kato 2004's index set `prime(m) ∩ Sigma = {2}`, but Kato 1999 Thm 0.8 needs every level divisible by `N_K = 2Nd`; since Sigma contains 3 and the primes of d, none is covered, and Kato's class `xi` is never identified with `y_{2^infty}`. A real gap that had passed the project's internal reviews and Fable's 4 Nov audit. | V10 (l. 12680-12690) | Repair: K8 defined for all `m` prime to `c d_s`; both norm cases of (0.1.1) verified; norm from levels `N_K 2^n` identified with the dyadic class. V11 (8 Nov). Re-bound in V12 and V14. | `docs/manuscript-revisions/version11/README.md`, `kato-application.json`, `evidence/independent-review.md`; `docs/audit-history/current.json` | Astra reviewer `/root/astra_bl5_models` accepted (internal). Fable 5.2 (10 Nov) re-derived the three repair steps against Prop. 8.12 of Asterisque 295 and found no error, but could not read Kato 1999. **No record that the Issue 2 reviewer rechecked V11** (issue observed closed 8 Nov). |
| E26 | 6 Nov (reported), 7 Nov (answered) | GitHub Issue 3 contributor (name not in the files read) | Reproducibility: the exact finite cases, evaluation points, expression-hash format and `final.rows_sha256` serialization were implemented in the checkers but missing from the prose. | Original construction (commit 97cec7fd) and V4 (5cb2c199) | Documentation correction; no change to polynomial, manuscript or Lean target. 7 Nov. | `docs/audit-history/issue3/README.md` and JSON receipts | The issue itself supplied independent reproduction of finite artifacts; the project's 7 Nov replay is its own. Whether the contributor confirmed the answer is not recorded. |
| E27 | 6 Nov | Fable 5.1 | Lean: the frozen target is the 292,890,231,905-variable statement, not the quartic; `PoleValuation.lean` proves an older six-Boolean pole system, not the V4 pole lemmas. | V4 | Scope statement: Lean guide says so explicitly; target left as approved. | `fable-repository-audit.md` (last paragraph) | n/a (clarification). |
| E28 | 6 Nov (10:06 update) | Fable 5.1 | V6's new appendix "Simultaneous primes with coprime adjacent norms" (about 2,000 lines of Green-Tao-style analysis, items 2-5) is AI-written with no independent review; until audited the dependence on Sun Thm 4.1 / Frei-Tinkova Thm 1.4 should be listed as present. README and `quartics/quartic-962/PROOF.md` disagree on this. | V6 | Audit with repairs: four Astra agents reviewed tail, prime weights, transference, polynomial patterns; changes integrated (V7). Dodos-Kanellopoulos later replaced by Green-Tao relative inverse theorem + internal GI proof (by V15). | `docs/quartic-962/gaussian-audit-20261106.md` and `evidence/gaussian-four-audit-20261106/` | Astra (internal). Externally: Fable 5.2 third/fourth pass traced the chain end to end (13 steps verified, 3 followed). **PARTIAL**: `PROOF.md` line 7 still says "its current Frei-Tinkova input". |
| E29 | 6 Nov | Fable 5.1 | Gaudron-Remond 2023 Thm 1.9(1) (used in CM bound, (LT3), exponent-19 sharpening) had not been confirmed in the published Memoire. | V4 | Confirmed by a later external pass: Fable 5.2 second pass, item 6 ("Matches"). | `fable-5-2-audit-4.pdf` p. 58 | Yes (Fable 5.2). No repository record. |
| E30 | 6 Nov | Hector Pasten (per task brief; his name is not in the repository records) | Attribution: Pheidas (2000) should be credited for the rank-one elliptic curve / existential local-divisibility strategy and partial valuation predicates. | V4 | Attribution added (introduction paragraph + bibliography item); no mathematical change. V4 editorial update, 6 Nov; carried forward. | `docs/quartic-4973-validation/pheidas-20261106/README.md`, `PHEIDAS_ATTRIBUTION_REVIEW.md` | "Reviewed by the coordinating agent" (not independent). Fable's 6 Nov update notes the credit was added. Original Pheidas chapter "not retrieved for a fresh page-by-page reading". |
| E31 | 6 Nov | Collaborator notes (supplied via Sohail Farhangi; project credit lists Baranczuk, Brox, Conant, Farhangi, Freitag, Park, Terry) | Arithmetic-input note Sec. 12: with full 2-torsion and 3-dimensional 2-Selmer, the alternatives are rank one with trivial 2-primary Sha, or rank zero with Sha[2^infty] = Q_2/Z_2; excluding the divisible alternative "is an arithmetic obligation, not an automatic consequence of the dimension calculation". Their own route leaves the parity predicate P unproved and used von Kanel-Kret. | V4 | vKK: replaced dependency (exact reduction to the existing five-contact proof). Divisible-Sha alternative: in the manuscript it is discharged by RC; the note "does not certify or disprove the existing restricted-converse proof", and this update "does not re-audit" RC. | `research/2026-11-06-collaborator-notes/README.md`, `comparison.md`, `height-replacement.md` | vKK substitution: narrow algebra/number checks only (`check_replacement.py`). RC: see E19, E25, E38. |
| E32 | date not recorded (resolution lands 9 Nov, V14) | Kevin Buzzard (per task brief; not named in the repository except as author of the cited 1997 Duke paper) | Reliability of cited sources in the height/modularity chain: Hu-Tan (an ancestor inside Pan's proof; the record speaks of a "global Hu-Tan Section 6 support issue") and Baba (Baba-Granath 2008, discriminant-6 moduli data). | V13 and earlier (inferred) | Scope change / replaced immediate supplier. V14 cites Pan's prime-five theorem as published via Calegari ICM 2022 p. 624 and adds "Scope of the modularity input": the use "does not assert that every input to Pan's proof has been reproved"; Pan's local Hu-Tan ring calculations "are distinct from the global Hu-Tan support argument". The Hu-Tan question is set aside, not settled. Baba-Granath: V14 rewrites the datum (their printed form is six times the determinant-one form; cites Thm 2.1 "with the corrected principal datum"); the old "indices 4,6,2" sentence no longer appears in V17. | `research/version14/proofs/direct-p5-modularity-v1/SOURCE-STATUS.md`; `pan-utility-p5-v1/`, `pan-p5-sw99-v1/`, `pan-local-rings-v1/`; V14-V17 paragraph "Scope of the modularity input" (V17 l. ~5790); `docs/audit-history/current.json` edits | Bounded Astra acceptances of the utility proofs (internal). Fable 5.2 checked the modularity lemma's logic and that Calegari's sentence matches; "did not check Pan's theorem in his paper". I could not confirm from the record that these edits were made in response to Buzzard. **PARTIAL.** |
| E33 | date not recorded (V14) | David Savitt (per task brief; not named in the repository) | Pan's theorem suffices for the modularity step; the detour through GL2-type/Serre, auxiliary-prime, prime-cyclic base-change and Khare weight-transfer reconstructions is unnecessary. | pre-V14 working drafts (inferred) | Adopted: `lem:qm-modularity-descent` applies Pan at `p = 5` directly; the detour packages are "preserved research history ... not the current suppliers". V14. | `direct-p5-modularity-v1/SOURCE-STATUS.md` ("The audit did not ... establish that the previous detour was necessary") | Fable 5.2 first pass: lemma logic checked, theorem at citation level. Attribution to Savitt is not in the record. |
| E34 | 10 Nov | Fable 5.2, first pass on V15 | Abstract: "coefficients are explicit polynomials in a positive integer C, for which we have no effective upper bound" reads as if C were one unknown number; the theorem is that every `C = 149^(2N+1)` with `N >= N_0` works and `N_0` is ineffective. | V15 | Not changed: identical sentence in V16 (l. 69) and V17 (l. 5152). The repository records the sentence as an owner-requested edit. | - | **OPEN (text unchanged).** |
| E35 | 10 Nov | Fable 5.2, first pass | Record integrity: acceptance of the 222 construction is on GitHub (PR 26) while in-tree files say "pending"/"preparation"; root `SHA256SUMS` stops at V10. | V15 | `research/version15/README.md` names PR 26 and its protocol evaluation; `SHA256SUMS` now has V17 entries. No in-tree copy of the PR 26 evaluation found. Whether these were responses to Fable is not recorded. | `research/version15/README.md` l. 16; `SHA256SUMS` | No record. **PARTIAL.** |
| E36 | 10 Nov | Fable 5.2, first and second pass | The 6,200-line internal proof of the Gowers inverse theorem GI(k) (V15 l. 23826-30064): unaudited, self-inconsistent (opening says the modules prove the theorem; several units say they await acceptance), and it points to working files not in the manuscript (`lp04-001`, "DF002 lines 132-145", "Section 13 lines 327-343"). Cite or prove? | V15 | Audit: Fable read all 17 sections in its third pass ("verified or followed"; one missing normalization, E39). The project kept the internal proof. The dangling references and the self-disclaimers are still in V17 (l. 29016, 29169, 31179). | `fable-5-2-audit-4.pdf` pp. 43-48, 62-83; `research/version16/README.md` | One complete external reading (Fable). **PARTIAL**: exposition defects unchanged; Fable recommended "a second reader who works in this area". |
| E37 | 10 Nov | Fable 5.2, second pass ("Corrections to the text") | (a) V15 l. 32294 says "four normalized pole inputs"; the tables have three. (b) The 248-variable table stores half the real component of x in its T chart, unstated. (c) Javanpeykar "Lemma 2.3.1" pointer should be to its proof. (d) Version 13 text: "m is neither 0 nor 2" should exclude 0 and ±2. (e) Stored coordinate names keep "12" for order-10 tests. "None of these affects a proof." | V15 | Not incorporated: (a) still in V16 l. 32325 and V17; (c) V17 l. 3786, 35423; (d) V17 l. 27379. (b), (e) concern stored tables. No disposition record found (V16's `FINDINGS.json` covers only the fourth-pass items). | - | **OPEN (minor; text unchanged, no record).** |
| E38 | 10 Nov (restated 11 Nov) | Fable 5.2, second-fourth pass | Kato 1999 (Kodai, Secs 0.1, 0.6-0.8, pp. 314-318), on which the repaired `p = 2` application (E25) rests, could not be read; Asterisque 295 does not prove Thm 13.4 but attributes it to Perrin-Riou, Rubin and Kato 1999. Likewise Ribet 1990 Props 3.3, 3.6, Rem. 3.5 (step at V15 l. 15105-15116). | V15 | Recorded as an unclosed limit of Fable's audit. V16's current review "identifies the earlier independent Kato and Ribet reviews" (Astra) without changing Fable's scope. | `research/version16/FINDINGS.json` (`unclosed_audit_scope`), `protocol/CURRENT-CORRECTIONS.md` | Internal Astra source reviews only. **OPEN as an external check.** |
| E39 | 10 Nov | Fable 5.2, third pass | GI proof, V15 l. 26880-26890: the passage to a finite cover divides each frequency by M although the horizontal Taylor identities are known only modulo the larger horizontal lattice; a Heisenberg example shows the discrepancy can be nonzero. | V15 | Repair: normalize the orbit by a lattice-valued polynomial so the identities hold in the vector groups, then divide the fixed real lifts. V16 (11 Nov), l. 26819-26929. The device already appeared later in V15 (l. 27527-27534). | `research/version16/README.md`, `EDITS.json`, `APPLICATIONS.json` (V16-HORIZONTAL-NORMALIZATION), `review/current/REVIEW.md` | Yes, twice: Fable supplied and re-derived the repair text (fourth pass); Astra reviewer `/root/v16_correction_review` (not an author) accepted it and traced consumers. |
| E40 | 10 Nov | Fable 5.2, third pass | Two auxiliary Faltings-height statements (V15 l. 30633, 30646) are cited to Gaudron-Remond's Duke paper but are in Comment. Math. Helv. 89 (2014), Sec. 2.3 and Cor. 8.4. | V15 | Citation corrected; new bibliography entry. V16. | V16 `EDITS.json` (gr-lower-bound, gr-isogeny-height, gr-periods-bibliography) | Yes: `/root/v16_correction_review` checked against the published CMH paper (pp. 351-352, 400); Fable confirmed bibliographic data. |
| E41 | 10 Nov, withdrawn 11 Nov | Fable 5.2, third pass | Bogolyubov lemma cited as Lemma 6.4 of the Green-Tao U^3 paper; it is 6.3 on arXiv. | V15 l. 25988 | Withdrawn by Fable: the journal numbers it 6.4 (pp. 97-98). No change. | `FINDINGS.json` (Bogolyubov-number) | n/a (withdrawn by the objector). |
| E42 | 10 Nov | Fable 5.2, third and fourth pass | V15 l. 20063-20073: Tao-Ziegler's Theorems 11, 13, 15, Cor. 3 are applied with a modulus carrying a fixed extra factor; this is an adaptation of their proofs, not an application of their statements. Fable did not re-read the proofs of Thm 15, Props 2-3, Lemmas 4-5 with the changed modulus, and sketched a statement-only reduction. | V15 | Scope change in wording: V16 says the use adapts the proofs; a later precision amendment says the local factors "satisfy the same uniform estimates" (not identical values). The statement-only route was not adopted. | `research/version16/README.md`, `TZ-PRECISION-AMENDMENT.json`, `review/current/REVIEW.md`, `TZ-PRECISION-ADDENDUM.md` | Wording: yes (`/root/v16_correction_review`, disposition "accepted_scope_description_only"; later review says it checked the adaptation against the published proofs). Mathematics of the adaptation: internal only; `FINDINGS.json`: "Fable has not re-derived the full changed-modulus proof". |
| E43 | 12 Nov | Primary-source locator audit by AI agents with web access, run on the formalization fork (`Deicyde/diophantine-z-q`, branch `wip/w17-base`) "at the owner's request"; in this checkout as `docs/research/locators.md` | Leaf statements extracted from the 11/5 MS height proof (Thm 4.1): R2, the orders (4,6,2) cited to Baba-Granath are orbifold elliptic orders, the degree-4 Atkin-Lehner quotient has ramification (2,2,2); R5, Gonzalez-Rotger Prop. 5.6 gives `#CM(R) = 2^{#{p | D N}} h(R)`, not `h(R)`; R3, Lin-Yang arXiv v1 discriminant-6 example is Example 29, not 30; Pazuki's bound is in Deligne's metric (shift `+log pi`); Pan's JAMS numbering and the `p = 3` exception; several classical leaves UNVERIFIED. | 11/5 MS as restated in the fork's `h-decomposition.md` | Citations corrected in the fork's notes; "where a correction may affect an argument rather than a citation (A2/A5's use of ramification orders, A10's use of the CM count) ... the argument is left unchanged: a separate review task checks those". No result of that review found. | `docs/research/locators.md`; dated notes in `docs/research/h-trust.md` | **OPEN** for the two argument-affecting items. Whether V17's text is affected was not determined (V17 no longer contains the "indices 4,6,2" sentence). |

Count: 43 entries. By status: 29 RESOLVED (E1-E4, E6, E9-E22, E25-E27, E29-E31, E33, E39-E41; E13 and E41 by withdrawal, E31 with RC left to other entries, E25 repaired in the text but checked only internally and, in part, by Fable); 8 PARTIAL (E5, E7, E23, E28, E32, E35, E36, E42); 5 OPEN (E8, E34, E37, E38, E43); 1 with resolution record UNLOCATED (E24). The `11 (mod 12)` half of E7 is also unlocated.

### 2. Parts of the proof external auditors said they did not review

Fable 5.1, RC audit (4 Nov; `Audit of the restricted converse (Theorem 5.3) (3).pdf`):

- "Not accessed: the handoff repository", so sources S17, S19, S20, S28 and `outputs/twenty-two-prime-pattern-proof.txt` were not examined.
- Kato Sec. 12 could not be fetched (numdam text stops at Sec. 4.9); Kato 6.6, 9.7, 8.12, 13.5(2) at `p = 2` "not validated".
- For Waldspurger, Ramsey, Carayol, Cornut-Jetchev, Weil, Milne, Cai-Shu-Tian and Nekovar it checked "that the stated hypotheses match the use, not the theorems themselves".
- "it did not re-derive the local Weil-representation computations in F.2"; the replaced dyadic metaplectic comparison is "not independently validated beyond structure".
- Lemma 9.1-9.4 constants were first "accepted at the level of logic; constants not independently recomputed" (9.2 later re-derived).
- The fixed-field budget (5.7) "remains a baseline input".
- The remaining "next checks" were never reported done: Euler-system construction and normalization behind (E.2)-(E.8); Cornut-Jetchev H.1-H.3 and Waldspurger Cor. 2 against primary texts.
- The same document says the soundness side "was audited in the first pass"; that first-pass document was not among the files I was given.

Fable 5.1, Version 4 audit and V5/V6 update (6 Nov):

- "the prime-pattern theorem in Section 6 [Prop. `prop:fixed-prime-pattern`] ... has not been read in any pass" (closed later by Fable 5.2's fourth pass, V15 l. 2071-2530).
- Section 15 local machinery (private conics, joint graph, target-two congruences, reciprocal logarithms `G_9/G_2`, generator certificate): "statements read, proofs not re-derived".
- The 4,513 source rows were not read against Section 15 one by one; the three-day reproduction pipeline was not run; Lean modules were not compiled.
- V6: Gaussian appendix items 2-5 "not audited by me"; `lem:v5-two-anchors`, `lem:v5-height-transfer`, `lem:v5-one-place`, `lem:v5-unramified-log`, the two reduced group cardinalities and detector/pole domain claims "not re-derived"; quotient-domain claims "depend on baseline lemmas I have not read"; V5 table not recomputed.
- Per the repository's summary (`fable-repository-audit.md`): "the prime-pattern theorem in Section 6 was not read in any pass, and the Section 15 local lemmas were read only as statements."

manvirjaswal (Issue 2 recheck, 7 Nov): "I rechecked v10 against the nine points (not the new §§14–18 or Apps. I–J)." No recheck of V11 or any later version is recorded. The original review was of the 11/5 manuscript; everything added from V4 on (quartic sections, Gaussian appendix, GI proof, V9-V17 arithmetic) is outside it.

Fable 5.2, four passes on V15 (10-11 Nov; `fable-5-2-audit-4.pdf`, cumulative), state at the end of the fourth pass:

- **Kato 1999 (pp. 314-318) and Ribet 1990 (pp. 440-443): "which I have not read."** The repaired `p = 2` Kato application and one step at V15 l. 15105-15116 rest on them.
- Proofs of published theorems were not audited (BCDT, Pan at 5, Kolyvagin, Gross-Zagier, Yuan, Gaudron-Remond, Green-Tao, Tao-Ziegler, Mitsui). Pan's theorem was checked only through Calegari's survey sentence.
- Tao-Ziegler adaptation: "the proofs were not re-read with the changed modulus"; that step "stays followed".
- Three of the sixteen steps of the simultaneous-primes chain remain "followed", not verified. Euler-product estimates (D.4)-(D.23) of Green-Tao not re-derived.
- Height chain: "geometric expansions behind it (level-3 marking, rigidity, canonical models) I followed without reconstructing"; the Shimura-curve steps using Faltings 1986, Shimura 1973, Igusa 1967, Buzzard 1997, Milne, Deligne 1971/1979, Lin-Yang, Mascot and the CM elliptic-curve height formula "stay followed", sources "not reached".
- Not reached: Mitsui 1956 Lemmas 14-15; Colliot-Thelene-Salberger 1989 Prop. 1.3 and CT-Sansuc-Swinnerton-Dyer Rem. 2.3.1 (the degree-lower-bound input); Silverman's book; the two Remond papers; Scholze Thms 9.1, 9.3. Comparisons still on preprints: Pan, Yuan (published in Chinese), Remond 2022, Browning-Loughran, Browning-Heath-Brown, Bienvenu, Scholze, Kolyvagin.
- Kato Asterisque 295 was confirmed only "where legible" (OCR scan; Euler-factor formula in Prop. 8.12 and displays (14.10.2)-(14.10.3) illegible).
- Formal groups of abelian varieties in the RC section (V15 l. 3972-3992, 4100-4116): "read ... in an earlier pass and did not re-read".
- Restricted converse beyond the Kato repair: "Changed passages read; nothing else re-audited" since the 4 Nov audit of the N4 packet. The RC chain in its V15-V17 form has had no complete external re-reading.
- Six short supporting sections (unary theta series, theta transport, Tate-module and marking descent, Picard norm, conductor-one CM reduction): "Read once, not re-derived" (the Picard-norm sections were used again in pass four).
- 314-variable system: groups of detectors 1 and 2 and "the remaining rows" not compared with the text. Pole-completeness decay rates quoted from the V5 source for Versions 9, 12, 13: "followed ... did not re-derive".
- 149-adic valuations in the reduced systems: re-derived in the 248 baseline and 237 criterion, "did not re-trace it row by row in the reduced systems". Derivation of the 248 table from the Brox construction: not covered.
- No repository code was run in any pass ("the sandbox refused"); GitHub issues, PR 26 and its protocol evaluation were not readable; stage review directories of the 222 package were not evaluated.
- **Nothing after V15 was audited by Fable**: not V16's edits as integrated (Fable supplied the text but did not see the integrated source), and not the 214-variable family that V17 presents (PR 30, receiving revision 3), including its new ten-contact height bound.

Other external statements of non-review:

- Pheidas attribution: "The original Pheidas chapter was not retrieved for a fresh page-by-page reading."
- Collaborator-notes update: "the lower-bound and prime-pattern papers were not certified in full"; the stronger lower bounds "have not received a complete independent audit".
- Locator audit (12 Nov): many classical leaves "UNVERIFIED" (Shimura 1967, Kottwitz, Igusa 1962/1967 bodies, Serre-Tate Thms 1-2, SGA7 IX, Faltings Satz 3-4, Saito, Pan's JAMS numbering, Lin-Yang journal body).
- `docs/audit-history/current.json` is bound to V14 (`manuscripts/quartic_v14.tex`), not to V16 or V17; I found no V17 rebinding of the Issue 2 ledger in that file.

### 3. Objections whose resolution I could not locate

- **E7 (second half):** a sentence explaining the role of `l = 11 (mod 12)` in RC. No edit or disposition found.
- **E24:** removal of the "% UNAPPLIED CANDIDATE ... published Pan match are pending" and "conditional on the separately audited field/ramification lemma" comments. The text is gone by V16, but no record says when, or whether the underlying caveats were checked rather than deleted.
- **E8, E34, E37:** Fable's wording requests (name RC and the height theorem in the theorem statements; abstract sentence about C; the five text corrections of the second pass). The questioned text is unchanged in V17 and I found no record of a decision to decline.
- **E35:** an in-tree copy of the PR 26 protocol evaluation.
- **E28 (residual):** `quartics/quartic-962/PROOF.md` still says the claim retains "its current Frei-Tinkova input"; `compiled-ir.json`'s `pending_independent_review` pointer (Fable 6 Nov) also has no located disposition.
- **E25:** confirmation by the Issue 2 reviewer that the V11 Kato repair is right. (His own proposed replacement text is close to what V11 does, but no recheck comment is in the pinned issue snapshot of 8 Nov.)
- **E32, E33:** any record of what Buzzard and Savitt actually said, when, and against which version. The repository states that no "private correspondence or routing note is included". The resolutions in the table are matched by content only.
- **E43:** the "separate review task" on whether the Baba-Granath ramification correction and the CM-count orientation factor affect the height argument.
- Collaborators named in the brief: I found no objection attributed individually to Jose Brox, Gabriel Conant or Cameron Freer. Brox and Conant appear as credited sources of constructions (1,272- and 248-variable baselines; odd-index product-height argument); Freer appears only as the committer of the 214-variable proposal (`docs/research/up-map.md`).

### 4. Method and limits

Read in full: `docs/audit-history/PROTOCOL.md`, `issue2/README.md`, `issue3/README.md`; `docs/theorem-application-audit/FINDINGS.md`, `OPEN_ITEMS.md`; `docs/manuscript-revisions/version10/README.md`, `responses.json`, `issue2.json`; `version11/README.md`, `acceptance.json`, and the reviewer comment in `issue-snapshot.json`; `docs/quartic-962/gaussian-audit-20261106.md`; `research/2026-11-06-collaborator-notes/README.md`, `fable-repository-audit.md`, `source-status.md`, `comparison.md`; `research/version16/README.md`, `FINDINGS.json`, `protocol/CURRENT-CORRECTIONS.md`; `docs/quartic-4973-validation/pheidas-20261106/README.md`, `PHEIDAS_ATTRIBUTION_REVIEW.md`; `docs/revision-2.md`; `CREDITS.md`, `CURRENT_VERSION17.md`.

Read in part: `docs/audit-history/current.json` (structure, follow-ups, a few edits); `research/version16/review/REVIEW.json` and `review/current/REVIEW.md` (opening sections); `docs/reviews/height-replacement/REPORT.md`; `docs/revision-3.md`; `research/version12-15,17/README.md`; `research/version14/proofs/direct-p5-modularity-v1/SOURCE-STATUS.md`, `pan-utility-p5-v1/README.md`, `pan-p5-sw99-v1/README.md`; `docs/research/h-trust.md`, `up-map.md`, `locators.md` (headers and main corrections only). Targeted greps of `manuscripts/quartic_v16.tex`, `quartic_v17.tex`, `archive/quartic_4973.tex` and the V15 snapshot to see whether questioned sentences are still present.

Fable PDFs: all nine named files exist; none is missing. I extracted their text with `pdftotext` rather than viewing pages, so mathematical symbols are garbled in places and tables are column-scrambled. The four "Audit of the restricted converse" files are cumulative (6, 14, 19, 26 pages); I read the 26-page "(3)" in full. "Repository audit diophantine-z-q Version 4.pdf" (19 pp.) was read in full. The four Fable 5.2 files are cumulative (39, 62, 83, 97 pp.); I read `fable-5-2-audit-4.pdf` pp. 19-61 and 82-97 in full and pp. 62-82 (third-pass detail) by keyword only. `fable-5-2-audit-4.pdf` is byte-identical to `research/version16/audits/fable-5-2-audit-4.pdf`. I did not diff the earlier cumulative versions against the last, so a finding that Fable dropped between versions would be missed.

Not read: `INVENTORY.md` (207 KB) and the per-application evidence files of the theorem-application audit; `docs/audit-history/issue2/register.json` and its evidence excerpts; `version11/evidence/*`; V12-V14 revision directories; `research/version16/APPLICATIONS.json`, `protocol/CONNECTIONS.json`; the 116 files of `docs/research/` apart from the three sampled; `docs/reviews/height-replacement` sub-reports; the Gaussian audit sub-reports; `Fable_review.png`, `Fable_review_2.png`, `fable-audit-packet-2026-11-04.zip`, `z-in-q-full-justifications-audit-2026-11-04.zip` in Downloads (not on the list I was given). GitHub itself was not consulted; the original text of Issue 2 and all of Issue 3 are known only through the repository's responses, so the wording of points 1-9 in E18-E22 is reconstructed from the dispositions.

Limits on the conclusions.

- Dates for E18-E22 come from the issue's `updated_at` (2026-11-06T00:39Z) and its title; the opening post's own timestamp is not in the checkout.
- The Nov 5 theorem-application audit (E11-E17) was carried out by Astra agents at the owner's direction. I list it as the brief asked, but its "independent" reviews are within the project's own pool.
- `docs/research/` appears to belong to a separate formalization effort (it calls this repository "upstream" and audits a fork). I sampled it only for E43; it contains many further model reviews (`rv-*.md`) of the 11/5 height proof and RC that are not ledgered here.
- For E32 and E33 the identity of the objector and the content of the objection come from the task brief, not from any file. Treat the matching as provisional.
- "Text unchanged in V17" claims rest on string searches for the specific sentences, not on a reading of the surrounding passages.

# Part 2: findings from internal reviews

## Internal reviews, batch 1

Kinds: ERROR = error in the mathematics as written; GAP = gap or missing justification; HYP = hypothesis or convention not checked / wrongly stated; OVER = overstated claim; LIM = reviewer explicitly did not check.


### R1-F01 (LIM) Arithmetic slice: supplier joins not accepted
- Path: docs/manuscript-revisions/version14/baseline-coverage/arithmetic/REPORT.md
- Reviewer/date: `/root/astra_v14_baseline_arithmetic`, 2026-11-07
- Point: Coverage of quartic_v13.tex lines 1-5930 is accepted, but "complete supplier reconciliation" is declared incomplete. 39 references to 27 labels outside the slice are not accepted on their summaries: coefficient omission/contraction/primary-isolation rules feeding the two address lemmas, simultaneous-address construction, odd visibility/stabilization (including an implicit dependence on visibility implication O.8 in the odd-source appendix), de Rham descent to the representation consumed by Berger and Pan (weights 0,-1), the literal compiler/bridge witness domain, and the current-source Kato join (full 1999 index domain, both norm cases) to the even common scalar at lines 1970-2095. No false inference found in the slice; inherited mathematics not re-proved.
- Next: left open for the parent to join; "may be reopened by a later omitted input or failed supplier join".

### R1-F02 (LIM) Gaussian slice: Dodos-Kanellopoulos final text not compared
- Path: docs/manuscript-revisions/version14/baseline-coverage/gaussian/REVIEW.md
- Reviewer/date: `/root/astra_v14_baseline_gaussian`, date not stated
- Point: DK Theorem 5.1 (interval norm (5.4), full cyclic U^(2s) majorant condition, prime cyclic size in [CL,2CL], C >= 20) was checked only in arXiv v4 and an author-linked manuscript, not the final typeset Acta Arith. 203 (2022) article. BL Theorem 4.1 and BHB Lemmas 2.1/4.1 were checked only in accepted manuscripts. "Full protocol-v1.3 proof closure is not asserted"; no fresh coefficient replay; 43 cross-slice supplier occurrences unjoined.
- Next: left open. BL later closed (F03); DK final comparison not stated as closed anywhere in this batch.

### R1-F03 (LIM) BHB final-publication comparison open
- Path: docs/manuscript-revisions/version14/baseline-coverage/published-version-checks/bl-bhb/REVIEW.md
- Reviewer/date: `/root/astra_v14_baseline_compiler`, 2026-11-07
- Point: BL Theorem 4.1 (n >= 5, M coprime to 2*disc, nonempty allowed sets of vectors nonzero mod p, error O(B^(n/2+eps) M^(n/2+eps)) uniform in M) compared with the final AMS PDF pp. 5772-5773: no difference. Browning-Heath-Brown, Forum Math. 33 (2021), Lemmas 2.1 and 4.1 and the lattice-basis argument: final text not obtained; the accepted/arXiv qualification must remain. Review notes the BL source count is unprimitive and the manuscript's Mobius inversion, the l^4-1 factors and positivity of the constant are internal deductions, not supplied by BL.
- Next: BL closed; BHB left open here. The later analytic review (F35 file) says a `final-source-bhb/FINAL-COMPARISON.md` supersedes this qualification.

### R1-F04 (HYP) Kato application: locator and cochain/support conventions corrected
- Path: docs/manuscript-revisions/version14/final5882-transport/REVIEW.md
- Reviewer/date: `/root/v14_arithmetic_review`, date not stated
- Point: The Kato application span is the one non-identical span among 32: the replacement corrects the Kato definition locator to Sections 8.2 and 12.2, identifies ordinary etale cochains, and includes 2 and the actual fixed-twist ramification support. Review stresses the contract is not broadened to a whole Kato theorem or an unproved K(pi,1) statement; the separate global-cohomology contract remains necessary.
- Next: repaired in the manuscript via TEX-EDITS.json (global-cohomology-comparison-author-002); transport accepted at bounded scope.

### R1-F05 (HYP) Q(sqrt2) squareclasses and local differential normalization
- Path: docs/manuscript-revisions/version14/resume003-grouped-source-edits/REVIEW.md
- Reviewer/date: `/root/v14_arithmetic_review`, date not stated
- Point: Two main-text edits: the fixed Q(sqrt2) source now proves principal ideals and four sign squareclasses with explicit positive embedding; the local passage now fixes a minimal invariant differential or its dual, "excluding arbitrary nonunit rescaling" (previously unrestricted). No rank, torsion, Selmer, global period or full Kato acceptance follows.
- Next: repaired in manuscript; contract V14-GROUPED-SOURCE-EDITS-001 accepted for exactly these two passages.

### R1-F06 (GAP) V14 addition: H fixed-point exclusion used a test not yet available
- Path: docs/manuscript-revisions/version14/source-review/REVIEW.md
- Reviewer/date: `/root/astra_v14_source_review`, date not stated
- Point: In the 394 -> 299/314 reduction, the old H fixed-point exclusion was stated using an order-40 test, while the new early stage supplies only positive valuation. Reviewer classes it as an existing justification needing to be made explicit.
- Next: repaired in the reviewed addition: the new EU term gives positive v(f(H)), which already contradicts the fixed unit values; no high logarithm estimate used.

### R1-F07 (GAP) V14 addition: N0 introduced before its identity was established
- Path: docs/manuscript-revisions/version14/source-review/REVIEW.md
- Reviewer/date: as F06
- Point: The reciprocal section introduced N0 through -1/z(H) before spelling out its physical identity (H not yet restored at that point). Also noted: the S alternate cache is 196/197; a rejected 202/203 artifact is not used. Earlier manuscript through line 20771 is outside this review.
- Next: repaired: N0 is set equal to the existing affine normalizer from the H equations and the quotient meaning is postponed until H is restored.

### R1-F08 (HYP) V5 Sun appendix: relative inverse theorem invoked with the wrong majorant norm
- Path: docs/quartic-1272-validation/independent-review/REVIEW.md
- Reviewer/date: not named ("Independent Version 5 review"), date not stated
- Point: The imported relative inverse-theorem invocation (Frei-Tinkova Lemmas 9.1, 9.3 with Dodos-Kanellopoulos Theorem 5.1) did not carry the correct higher majorant norm. A target U^(u+1) norm needs the U^(2u+2) majorant norm; requesting D = 4^(u+1), u >= 1, supplies it.
- Next: repaired in the appendix with an explicit local repair (`FT-local-repair.md`), "this invocation only", not closure of the external proof. In V6 the imported-theorem invocation and its repair remark were removed altogether (F12 file) and DK 5.1 is carried with the full-cyclic U^(2s) hypothesis.

### R1-F09 (GAP) V5: CM reduction-order reference ambiguous
- Path: docs/quartic-1272-validation/independent-review/REVIEW.md
- Reviewer/date: as F08
- Point: The completeness argument referred ambiguously to "reduction orders". The needed fact is that the unordered elliptic group cardinalities equal the adjacent Gaussian norms and are used as annihilators (exact orders of the reduced point not required), plus a two-prime-form argument that the needed denominator is a unit at the selected prime.
- Next: repaired: CM group-cardinality lemma and denominator-unit argument made explicit.

### R1-F10 (GAP) V5: unquantified theorem statement and undefined progression length
- Path: docs/quartic-1272-validation/independent-review/REVIEW.md
- Reviewer/date: as F08
- Point: (a) The main 1272-variable polynomial statement did not explicitly quantify every rational input. (b) In the Sun final diagonal the progression length was not explicitly defined after the piecewise choice of the shrinking parameter (obstruction error controlled for fixed positive values first, then the polynomial asymptotic applied).
- Next: both repaired in the reviewed text.

### R1-F11 (LIM) V5: source versions and inherited blocks
- Path: docs/quartic-1272-validation/independent-review/REVIEW.md
- Reviewer/date: as F08
- Point: Frei-Tinkova arXiv 2408.17441v3 Theorem 1.4 is not a verified final journal text; DK checked in arXiv v4 only. Eight foundational blocks are text-identical to V4 but not freshly proved. Sampled IR identities "do not prove global arithmetic implications or establish the existence of rational witnesses". Restrictions on Pan, Yuan, prime-pattern correction sources and the inherited restricted converse remain.
- Next: left as stated qualifications.

### R1-F12 (OVER) V6: polynomial-count proposition was asserted for arbitrary finite Galois extensions
- Path: docs/quartic-962-validation/final-assembly-review/history-b43f096/REVIEW.md (text repeated verbatim in .../history-a00e3aca/REVIEW.md and .../final-assembly-review/REVIEW.md)
- Reviewer/date: `/root/astra_sub1000_quotients`, 2026-11-06
- Point: The polynomial-count proposition "no longer asserts the result for arbitrary finite Galois extensions". It is now scoped to the fixed ray class field of Q(i) for H*Z[i] with 16 | H and to conjugation-invariant subsets of the Gaussian ray group, which is what the ray-class application uses. The Frei-Tinkova citation is reduced to method attribution.
- Next: repaired in the assembled V6 manuscript.

### R1-F13 (GAP) V6: Gaussian Siegel-Walfisz estimate had been an assumed input
- Path: same three files as F12
- Reviewer/date: as F12
- Point: The progression fragment previously invoked a displayed Gaussian SW estimate conditionally (two conditional invocations). The inserted Mitsui SW lemma now proves it uniformly for fixed Gaussian character, q up to any fixed log power, 1 <= Y <= X; the review checks the edge cases Y=0 and 0<Y<1 and that the rational SW estimate comes from the same lemma.
- Next: repaired by insertion; reviewer concludes deleting the conditional invocations "does not delete an unproved hypothesis".

### R1-F14 (LIM) V6 assembly review is fidelity only
- Path: same three files as F12
- Reviewer/date: as F12
- Point: Acceptance is for assembly fidelity. The inserted Gowers/boundary bridge's full analytic proof is "a separate review obligation"; the 962 polynomial convolution was not rerun; Kollar's theorem (degree lower bound) was checked in the author version only, full published text not compared. Degree lower bound concerns a single polynomial and total degree over Q, not witness count or systems of quadratics.
- Next: left to the separate analytic review; Kollar qualification retained.

### R1-F15 (OVER) V6 inventory: unqualified summary of the 962-variable projection
- Path: docs/quartic-962-validation/inventory-independent-review/REVIEW.md
- Reviewer/date: `/root/astra_sub1000_quotients`, 2026-11-06
- Point: An authored register summary stated the 962-variable projection without qualification. Corrected to "the same rational projection as the source, with the source's arithmetic hypotheses retained for the integers conclusion". (Also: `V5-SUN-FT-LINEAR` retired as an assumed theorem; DK 5.1 remains an active application with the corrected full-cyclic U^(2s) majorant hypothesis; DK and Kollar keep author-version qualifications.)
- Next: corrected in the register and rechecked. Acceptance is for inventory accuracy, "not an additional decision that every mathematical statement is true".

### R1-F16 (GAP) Gaussian large-prime tail: range of the cutoff L was unquantified
- Path: docs/quartic-962/evidence/gaussian-four-audit-20261106/tail/REPORT.md
- Reviewer/date: not named ("Independent Gaussian large-prime tail audit"), 2026-11-06 per directory name
- Point: The weighted tail proposition left the range of L unstated although its medium-prime input requires a sufficiently large cutoff. Repair: fix a lower cutoff L_* and state uniformity for L >= L_*. Other changes only expand compressed steps (Rankin bound for the number of t per q, content after lattice substitution supported on q, R=0 locus, t=-2 chart). Reviewer states explicitly these are not repairs of a false lattice bound or missing log saving, and that the homogeneous BHB quadric theorem is not a direct citation for the adjacent norms (homogenizing loses a power of B); the manuscript's reconstruction from BHB Lemmas 2.1 and 4.1 is the legitimate route.
- Next: `replacement-tail.tex` proposed for baseline lines 16389-16531; no shared manuscript edited by the reviewer; integration not stated in this file.

### R1-F17 (LIM) Tail audit scope
- Path: as F16
- Point: BHB and BL were read in accepted manuscripts only (final typeset editions inaccessible; zero-byte "published" files not treated as sources). The audit "does not assert the separate prime-pattern lower-bound proposition"; the medium-prime lemma's primary review is elsewhere. No TeX build.
- Next: left open.

### R1-F18 (HYP) O3 connection: BM 2.42 zero-order bound wrongly described
- Path: docs/research-review/proof-sources/ceggps-connections-v1/reviews/o3/REVIEW.md
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, 2026-11-08
- Point: Breuil-Mezard 2.42 requires the two multiplicity bounds on the same dense set of characteristic-zero closed points; it does not restrict the zero-order bound to ordinary Banach points. Compiler005 used ambiguous terminology suggesting otherwise.
- Next: corrected in compiler006 (single phrase replacement, verified); the two bounded connections (nonordinary RED; RED to first-order type multiplicity) accepted.

### R1-F19 (LIM) O3 scope
- Path: as F18
- Point: Final Dospinescu and final BM edition comparisons remain open. Henniart multiplicity, ordinary and nonsupercuspidal local inputs, original module constructions and exceptional rings not reproved. Conclusion excludes ordinary Banach representations and reducible Pi_alg; BM 4.16 exclusions and the weight-gap-one scalar exception remain necessary. O4, O5 outside.
- Next: left open.

### R1-F20 (ERROR as printed; reviewer classifies as notation ambiguity) Reflection formula signs
- Path: docs/research-review/proof-sources/interpreter-precision-inputs/work/astra-final-alpha-power-independent-review-001/REPORT.md
- Reviewer/date: not named, 2026-11-04
- Point: `04-computation-value.tex:150-152` (V4b/V4d/V4e) writes the reflection congruence with two successive plus/minus signs. Read as synchronized it is false: for n = 2lm + eps*j the value sign is (-1)^l * eps, e.g. b=4, m=2, n=3 gives v=14 and U_3 = 15 = +1, not -1 (mod 14). The proof at 172-180 uses the signs separately and is valid; no polynomial changes. Review also confirms by countermodel that the squared divisibility in clause 5 and clause 14 (2N<u) are necessary, and that gcd(u,v)=1 is false for arbitrary solutions (holds only for the chosen completeness witnesses).
- Next: `REFLECTION_SIGN_CLARIFICATION.patch` proposed; "No manuscript file was changed". Adoption not stated.

### R1-F21 (LIM) Alpha/power review scope
- Path: as F20
- Point: Does not establish that every downstream use of the exponentiation equivalence supplies natural P,Q,R (the VALUE recipe has `naturalInputs:false`; the equivalence holds only on N^3). The signed elliptic index model, its natural predicate and arithmetic operation contracts, packed-history predicates, interpreter and precision machine are outside. No Isabelle/Lean build.
- Next: named as a separate consumer obligation; left open.

### R1-F22 (GAP) Height replacement: de Rham to potentially semistable step missing for Pan
- Paths: docs/reviews/height-replacement/REPORT.md; docs/reviews/height-replacement/whole/REPORT.md
- Reviewer/date: four Astra reviewers (summary); whole-chain reviewer not named; source dated 2026-11-04
- Point: Pan's Theorem 1.0.4 (via Conjecture 1.0.1) requires potential semistability; the manuscript said only "de Rham" and omitted the named implication. Fix: cite the p-adic monodromy theorem (Berger), or use semistable reduction plus the semistable comparison after extending L'.
- Next: repaired: revised text supplies Berger's published monodromy theorem. The summary says the constant-coefficient convention, finite character twist and relative Frobenius comparison were also made explicit. No change to H6, exponent 24 or constants.

### R1-F23 (GAP) Height replacement: Herbrand conversion in the dyadic conductor estimate
- Paths: as F22 (detail in whole/REPORT.md)
- Point: At lines 769-771 the passage from the absolute upper break (<= 4D^2) to triviality of beta on G_F above relative index 3e was compressed. Needed: upper group above the break lies in G_F, the subgroup formula sends u to psi_{F/Q_2}(u) >= u, hence trivial for absolute u > max(4D^2, 3e) <= U0; no extra factor D or new exponent of M.
- Next: repaired: "final Herbrand paragraph" / dyadic upper-numbering argument added to the final text.

### R1-F24 (LIM) Whole-chain height review scope
- Path: docs/reviews/height-replacement/whole/REPORT.md
- Point: Checks the H6 interface and cutoff arithmetic (exponent 13*17*10 = 2210) but is "not an independent audit of the separate prime-catalogue or formal-group construction used to show R=D". Not a review of the restricted-converse proof or the main theorem.
- Next: left open.

### R1-F25 (ERROR) PR30 quartic214: M1 quasi-isogeny normalization printed wrongly (F1 / HGT-1)
- Paths: research/quartic214-manuscript-review/audits/astra-a8843cc-20261112/REVIEW.md; .../audits/astra-a8843cc-20261112/height/REVIEW.md
- Reviewer/date: `/root/astra_pr30_fresh_review` (and component `/height`), 2026-11-12
- Point: quartic214.tex line 2506 (PDF p. 85) prints a_sigma = D(mu_sigma)^{-1}/4, i.e. reciprocal degree divided by four. With mu_1 = 1 this gives a_1 = 1/4, and the next identity a_sigma a_tau / a_{sigma tau} = 1/|c(sigma,tau)| fails at (1,1) (1/4 vs 1). The M2/M6/H1 Tate identification and determinant consumers cannot use it literally. Intended: a_sigma = D(mu_sigma)^(-1/4), printed correctly at 3071, 3474, 6438, 13336. Source markdown `modularity.md:15-19` has ambiguous ASCII `^-1/4`.
- Next: decision "changes required". Repaired in the final held TeX/PDF and confirmed by the follow-up review (current-astra-20261112/REVIEW.md), "resolved at this receiving scope".

### R1-F26 (ERROR) PR30 quartic214: local degree sum malformed (F2 / HGT-2)
- Paths: as F25
- Point: quartic214.tex line 2812 prints `sum e_{{jf_j}} = d`; required is sum_j e_j f_j = d over all completed components with f_j the full residue degree (including inseparable degree). Correctly derived at line 2786 and in `height-different.md:17-19`. Does not invalidate the local trace argument.
- Next: changes required; repaired and confirmed in the follow-up review.

### R1-F27 (LIM) PR30 first review: coverage
- Paths: research/quartic214-manuscript-review/audits/astra-a8843cc-20261112/REVIEW.md; .../existence/REVIEW.md; .../height/REVIEW.md
- Point: "complete arithmetic review remains incomplete". Not done: recursive audit of rank/RC/Kato and Gaussian-prime/GI/transference chains; full reconstruction of the V16 horizontal-lift/Tao-Ziegler application; D210 geometry, CM, p-adic comparison, finite-duality/model, metric and modularity sources against primary publications; raw224 chart not rederived from first principles; large rational coefficients in inherited certificates not recomputed. Existence lane accepts P08-P20 joins only conditional on the height supplier, zero-preparation/RC interface and row transport; threshold is ineffective. Height lane: Fontaine/Scholze/Kato/Deligne-Serre sources not reacquired, full-11 semistability inputs and Stacks applications not all opened, no numerical computation run. The coefficient-height comparison applies for N >= 53 only. Original packet contracts bind Markdown, so they do not certify the assembled TeX (as F25/F26 show).
- Next: left open; "Correcting F1/F2 alone therefore would not turn this into a full arithmetic acceptance."

### R1-F28 (ERROR) PR30 follow-up: three further serialization errors in formulas (F3, F4, F5)
- Path: research/quartic214-manuscript-review/current-astra-20261112/REVIEW.md
- Reviewer/date: `/root/q214_astra_repair_review`, 2026-11-12
- Point: Found in the first repair candidate. F3: relative-extension labels in height-different (D_{U/V}, trace_{U/W}, relative r/e indices) printed with the slash outside the subscript. F4: numeric suffixes before Unicode powers escaped index conversion (C2^2, A3^2 in the changed factors; s1^2, s2^2 in reciprocal equations; c4^3 in the modular j formula). F5: in the revised torsion paragraph the Markdown emphasis parser consumed the pullback star in [n]^* omega = n omega and the ungrouped [n] index lost its n. All are mis-renderings of arguments whose sources are correct, not counterexamples.
- Next: reported to the author lane; all five (F1-F5) compared in the final held TeX and PDF and "resolved at this receiving scope" (19 replaced source lines).

### R1-F29 (LIM) PR30 follow-up: complete proof not accepted
- Path: as F28
- Point: "Complete assembled-proof acceptance: not accepted. Complete mathematical inventory acceptance: not accepted." Accepted only: formula incorporation, related-use coverage, source inclusion and changed joins, artifact packaging. Outstanding: inherited RC/Kato/Gaussian/GI arguments, transitive geometry/p-adic/comparison prerequisites, the historical objection corpus, exhaustive semantic and visual serialization (13 of 703 pages inspected), final 2022 Remond body (indirect source), superseded quotient route H3 not accepted. F1-F5 "refute any earlier blanket serialization-completeness inference" (TEX-F01 scope-explained, not closed).
- Next: left open.

### R1-F30 (LIM) D210 geometry/modularity component: source closure unresolved
- Path: research/quartic214-manuscript-review/current-astra-20261112/d210/REPORT.md
- Reviewer/date: `/root/q214_astra_repair_review/d210_modularity`, 2026-11-12
- Point: Inline transitions D01-D07 found coherent, but "Full source closure and complete inventory coverage remain unresolved." Not inspected at primary-source level: PEL classification and canonical-model prerequisites; stable-model extension theorems behind the tame model; Faltings, Scholze/corrigendum, Fontaine, Kato hypotheses; exact de Rham filtration data for the weight computation; Shimura twist theorem; Milne degree-polynomial theorem and Serre density; Li Fricke, Shimura quotient, Poincare; the 1967 ramification source; Milne 1986 Prop. 12.9 (image-only, unreadable); Stacks 0A18 only partially. The receiving TeX (later freeze) was not reviewed. Review notes two points that matter: the splitting-field degree must divide 576 (an inequality alone would not justify later wild valuations), and M0's B-linearity comes from V16 lines 8230-8255, not from the weaker F-linear conclusion.
- Next: left open; "Complete closure requires an authorized reviewer to finish the explicit unread source/application boundary".

### R1-F31 (LIM) V16 foundation component: large ranges unread
- Path: research/quartic214-manuscript-review/current-astra-20261112/v16/REPORT.md
- Reviewer/date: `/root/q214_astra_repair_review/v16_foundations`, 2026-11-12
- Point: No defect in the changed GI horizontal normalization, fixed-E Tao-Ziegler adaptation, GI-to-Gaussian norm join (r = max(s,4), k = r-1) and RC consumer joins. Not read in full: RC 2570-6728 and 13339-17529; complete Kato source/local control; Gaussian 17544-19441 (Type I/II, factorization); GI from 23826 onward; obstruction tail and ray-density antecedents. Fixed-E changed modulus is an adaptation of TZ, not a literal application. TZ Appendix A text extraction garbled; predecessor papers not read. Published parity/forward-rank inputs to RC not verified.
- Next: left open (V16-LIMIT-01).

### R1-F32 (ERROR) quartic214 revision 2: further serialization errors F6-F11
- Path: research/quartic214-manuscript-revision2-review/REPORT.md
- Reviewer/date: `/root/d214_geometry_source_closure`, date not stated
- Point: A complete pass over all nineteen converted proof sources (789 spans) found, at twenty source-line sites (F8-F11): wrongly evaluated Herbrand indices and a lost prime on the field F'; missing or misplaced projective/affine-space, point and differential indices; a wrongly grouped inverse in g h g^{-1}; ASCII composition and local-field conventions needing explicit notation. F6: four unit-group stars and the complete positive-real subscript were lost (the least-modulus choice makes the character primitive). F7: the text conflated four quotient-quartic invariant checks and 36 cross-ratio pairs with the separate five-form/ten-determinant certificate. No arithmetic counterexample asserted.
- Next: all repaired in the final receiving TeX; reviewer states "no finite semantic omission queue remains" at the converted-proof scope. Visual check was a 21-page sample of 703.

### R1-F33 (GAP) quartic214 revision 2: primitive-form extraction relied on Li attribution
- Path: as F32
- Point: A sixteen-line operative note was added that supplies Deligne-Serre primitive extraction before the retained historical Li existence attribution, preserving the same-good-prime eigenvalues and original representation, taking the actual twisting character's conductor, and keeping Li's uniqueness/Fricke uses separate. The original Li wording remains only as qualified historical evidence.
- Next: note incorporated; its source mathematics is stated to be accepted in a separate native application review. No new external supplier proof accepted by this serialization review.

### R1-F34 (HYP) BHB published text has slips that the application must correct
- Path: research/quartic214-protocol-d-progress/reviews/analytic/REPORT.md
- Reviewer/date: `/root/d214_analytic_source_closure`, date not stated
- Point: In the published Browning-Heath-Brown Lemma 4.1 material the "known printed slips are retained explicitly": the local quadratic form is R; the divisor sum is over d | q; the largest minimum is lambda_m. The proof gives the required bounded sum of d^(1-m). No publisher correction exists. Also recorded: BL supplies an unprimitive count only (no primitive BL is assumed by citation); the fixed-extra-factor prime majorant is a project derivation, not a clause of GT Prop. 6.4; the relative input to GT Prop. 10.1 is not one-bounded; GTZ 2012 has a 2024 author erratum (not a published theorem) and a 2014 published orbits erratum that leaves the one-variable suppliers intact.
- Next: handled in the manuscript's application as stated; no repair request from this lane.

### R1-F35 (LIM) Analytic lane scope
- Path: as F34
- Point: Gaussian appendix 17544-20356 read and accepted in scope, but the internal GI supporting range 24420-30095 "was not read in full" and is carried as an unchanged supplier at its earlier V16 scope. BL and BHB final PDFs not freshly accessed (earlier comparisons reused; the `>=` in n >= 5 rests on the earlier visual check). Elliptic interpretation of the prime generators, formal-depth calculations and new pole factors belong to other lanes. No inherited restricted-converse review.
- Next: left to parent/controller to combine.

### R1-F36 (GAP, closed by existing text) B-linearity consumed by M0
- Path: research/quartic214-protocol-d-progress/reviews/geometry/REPORT.md
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12
- Point: "The pairwise F-linear Skolem-Noether paragraph alone is insufficient" for the B-linear conjugate isogenies M0 needs. The separate V16 scalar-normalizer paragraph 8226-8255 supplies them (r*id commutes with B, rescale by 11^(-v11(q)), clear other denominators prime to 11). Related coverage item F-GEO-01: contract modularity-6 pinned H0/H1/H2 consumers but omitted the M0/M2 consumer excerpts.
- Next: F-GEO-01 resolved by an additive author contract (GEOMETRY_DIRECT_APPLICATION.json) binding the four direct edges, accepted by the reviewer; "no mathematical repair is claimed".

### R1-F37 (LIM) Geometry lane scope
- Path: as F36
- Point: Final pages of Buzzard 1997 pp. 591-592 (fixed order/involution, principal polarization) and Yuan 2024 pp. 230-231 (maximal N1 stack) were not inspected. Published Yuan metric/vertical, CM-height and GR2023 bodies not freshly audited. M1 is assumed ("Conditional on the separately checked M1 cochain identity"); M3 (finite-twist absorption, weight-two primitive form) and M3-M6 are outside. The historical H5-parent file was not available; no byte-equality claim. Finite reproduction (quartic invariants, 36 cross-ratio candidates, 10 contact determinants, support {2,3,5,7}) is finite arithmetic only.
- Next: left open; not whole-214 acceptance.


## Internal reviews, batch 2

Kinds: ERROR = error in the mathematics (or in a cited source's mathematics, marked as such); GAP = missing justification; HYPOTHESIS = hypothesis or convention not checked / mismatched; OVERSTATED; LIMITATION = something the reviewer explicitly did not check.

Path abbreviations: `Q214/` = `research/quartic214-protocol-d-progress/reviews/`; `CL/` = `research/version14/evidence/ceggps-local-reviews/`; `CLD/` = `research/version14/evidence/ceggps-local-reviews/dependencies/`; `CR3/` = `research/version14/evidence/current-reviewed-003/`; `EV/` = `research/version14/evidence/`.


### R2-F1. Unit-group stars lost in receiving TeX (item "F6")
- Path: `Q214/history-review/REPORT.md`
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12 (defect first found by Sol)
- Point: In M3's unit-group paragraph, source `modularity.md:57` has unit groups (starred); frozen receiving TeX line 2552 loses the stars (swallowed as Markdown emphasis), so the printed objects are no longer unit groups. The earlier bounded F5 check did not cover this occurrence.
- Kind: ERROR (transcription of mathematics, not an arithmetic counterexample)
- Next: OPEN at the frozen head. Needs minimal author repair, a related-star inventory, and independent TeX/PDF comparison.

### R2-F2. Li's Theorem 5 cited for existence; it is a uniqueness statement
- Path: `Q214/history-review/REPORT.md`
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12
- Point: The operative V16 foundation (native 685-691 / receiver 5768-5774) still attributes primitive-newform existence to Li's Theorem 5, which gives uniqueness only. Existence comes from the Deligne-Serre oldform decomposition; the precision note fixing this named V15, not V16.
- Kind: ERROR (misattributed theorem)
- Next: Resolved by additive overlay `CURRENT_NATIVE_PRIMITIVE_APPLICATION.json` (Sol; takes r = cond(eta)), accepted in `NATIVE_PRIMITIVE_REVIEW.json`. Old bytes preserved, i.e. the printed V16 text itself is unchanged.

### R2-F3. Kato index set omitted levels (Issue 2, point 4)
- Path: `Q214/history-review/REPORT.md`
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12
- Point: The revised Kato route's index set (K8) missed all levels divisible by 2Nd and did not identify the supplied limiting class with the Kato 1999 class; the earlier applicability check had not established the all-index transition. The other Issue 2 points (determinant, multiplication, saved-template, primed-ratio, off-filter, corollary) are classified as earlier justification with missing printed connections, not errors.
- Kind: GAP
- Next: Author acknowledged. Repaired at V16:13775-13859 (enlarged classes cover every required m; two norm relations; cofinal dyadic limit is the supplied class, no degree multiplier). Re-checked independently in `Q214/rc/REVIEW.md`.

### R2-F4. Heisenberg counterexample to lattice-refinement inference (Fable audit)
- Path: `Q214/history-review/REPORT.md`
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12
- Point: Equality modulo the old horizontal lattice does not imply equality modulo a smaller cover lattice; the Heisenberg example really invalidates that inference. The later-site normalization did not automatically cover the omitted earlier consumer.
- Kind: ERROR
- Next: Repaired by right-multiplying by lattice-valued binomial corrections, fixing real lifts before coordinate removal and dividing the same lifts at the cover. Native related-use disposition covers removals, finite cover, representation, real annihilation and join consumers.

### R2-F5. Rendered constant a1 = 1/4 contradicts the cocycle law (PR30)
- Path: `Q214/history-review/REPORT.md`
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12
- Point: The identity-element test shows the rendered a1 = 1/4 contradicts the next cocycle law; the source intended positive inverse fourth roots. Companion repairs: the local-degree product must use all complete components and full residue degrees (F3/F4/F5 of PR30 concern extension subscripts, coordinate indices, multiplication pullback).
- Kind: ERROR
- Next: Repaired in the receiving formulas; accepted earlier only within a nineteen-input / sampled-PDF scope, explicitly not exhaustive serialization (see F1).

### R2-F6. Rejected route SF11 (A0 inside J) and wrong height citations
- Path: `Q214/history-review/REPORT.md`
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12
- Point: Native SF11's "A0-inside-J" route failed and was rejected. Two Gaudron-Remond citations were wrong for the original-normalization lower bound and half-log degree cost and are replaced by the CMH paper.
- Kind: ERROR
- Next: Replaced by the same-field product/subproduct (product-averaging) route, separately reviewed for the 214 application. Not revived.

### R2-F7. Tao-Ziegler modulus-dependent statements not applicable verbatim
- Path: `Q214/history-review/REPORT.md`
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12
- Point: The TZ modulus-dependent statements are not applied word for word at the fixed extra factor. The claimed numerical-local-factor identity was later weakened to uniform estimates with boundary and order-of-limits conditions. Fable followed the adaptation only in outline, did not reread all changed-modulus proofs, and its alternative reduction was never fully written.
- Kind: OVERSTATED
- Next: Native precision correction adopted; the qualifications "remain part of reuse". (The Bogolyubov-number objection was withdrawn; not a defect.)

### R2-F8. Scope of the historical review
- Path: `Q214/history-review/REPORT.md`
- Reviewer/date: `/root/d214_geometry_source_closure`, 2026-11-12
- Point: Not a blind reconstruction; not a fresh reading of the 97-page Fable audit, of all appendices of PR30 comment 6827027005, or of the 1,313 file bodies (1,200 identical / 111 new / 2 changed is triage only). Fable's unread Kato/Ribet sources remain a limitation of that audit. Does not accept the changed 214 applications or the complete receiving serialization.
- Kind: LIMITATION
- Next: Left as stated; other decisions assigned to the concurrent closure lane.

### R2-F9. RC / Kato lane: ancestors and sources not freshly read
- Path: `Q214/rc/REVIEW.md`
- Reviewer/date: `/root/d214_rc_source_closure`, 2026-11-12
- Point: No new defect, but RC ancestors V16 2901-3301, 3385-3478, 14429-17464 were not read as whole passages; the open-image, modularity, Shimura/Faltings, parity, Kolyvagin, Edixhoven and odd-theta/Gross-Zagier/CCL source statements were not freshly inspected; Milne I.4.10/I.5.1 not read; no exhaustive Kato errata search. Acceptance covers only the RC/pole contribution to P19/P20; P16 analytic selection, height/soundness suppliers and the 224-to-214 algebra are incoming interfaces not reviewed. No numerical threshold or 214 witness tuple is supplied.
- Kind: LIMITATION
- Next: Left open as disclosure; reuse rests on native V16 acceptance.

### R2-F10. Kisin citation: bare existence statement insufficient
- Path: `CL/ceggps-c10-review-gaussian-001/REVIEW.md`
- Reviewer/date: `/root/astra_v14_baseline_gaussian`, date not stated
- Point: The cited Kisin "2.3.8" is old numbering; the final statement (Asterisque 330, Cor. 2.11) gives only Banach-lattice existence. The route needs the lattice with reduction exactly the supersingular pi (multiplicity-one hypothesis of Paskunas Image 5.56(iii)), which comes from the construction in Prop. 2.8 and Cor. 2.9-2.10. Also: the central character is det(V) epsilon^(-1); OCR drops the minus sign.
- Kind: GAP
- Next: Repaired in author supplement `CLD/ceggps-source-closure-003` Section 2; accepted as SC01-SC02.

### R2-F11. Colmez endpoint and dual conventions missing
- Path: `CL/ceggps-c10-review-gaussian-001/REVIEW.md`
- Reviewer/date: `/root/astra_v14_baseline_gaussian`, date not stated
- Point: Colmez Cor. IV.4.11 gives only D(Pi(D)) = D, not that an arbitrary Banach representation with that image is Pi(D); the draft lacked the identification of the Kisin-lattice fiber with Colmez's actual Pi(D). Also suppressed: the target central character is psi^(-1) (IV.3.2), D(B) = D(V_P) tensor psi^(-1), and the integral duals must be coefficient-valued (not a reversed inverse system). Equality of Colmez images / CEGGPS Cor. 6.19 alone does not give the fiber identification.
- Kind: GAP
- Next: Written out by the author in the successor (source-closure-003, Section 2, via IV.3.2-3, IV.4.7-9, I.3.11, II.1.14(iv), II.2.11-12); accepted as SC03-SC05.

### R2-F12. Forward de Rham implication (Colmez VI.6.13) missing in spherical-support argument
- Path: `CL/ceggps-c10-review-gaussian-001/REVIEW.md` (also recorded in `CLD/ceggps-source-closure-003/REPORT.md` Section 7)
- Reviewer/date: `/root/astra_v14_baseline_gaussian`, date not stated
- Point: SC06 applied VI.6.30 and VI.6.50 (de Rham domain) without first showing that nonzero locally algebraic vectors force D de Rham; VI.6.13 is needed. Likewise the crystalline converse needs VI.6.30 and is not a reversal of VI.6.50(i).
- Kind: GAP
- Next: Edge added in source-closure-003 Section 3; accepted later by `CL/ceggps-sc06-09-review-05`.

### R2-F13. Scope of the C10 review
- Path: `CL/ceggps-c10-review-gaussian-001/REVIEW.md`
- Reviewer/date: `/root/astra_v14_baseline_gaussian`, date not stated
- Point: Interactive, not blind (reviewer gave pre-freeze feedback); reviewer's own emerton-weak-map lemmas are excluded from the acceptance. SC06-SC09 and C10 not accepted. Final CEGGPS and BM editions unverified; BP enlargement, smooth Ext, crystalline regularity, Hecke map, patching, minimal type and classical local-global inputs remain separate.
- Kind: LIMITATION
- Next: Later bounded reviews address SC06-SC09, Ext, BP, eta; final editions stay open.

### R2-F14. Framed versus unframed deformation ring for the Hecke map eta
- Path: `CL/ceggps-eta-review-05/REVIEW.md` (target: `CLD/ceggps-eta-audit-001`)
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, 2026-11-08
- Point: CEG+16 Theorem 4.1 gives eta into the framed fixed-type ring; CEGGPS 6.17 consumes it on the unframed ring. Audit 001 identified the two without a descent argument.
- Kind: GAP
- Next: Repaired in `CLD/ceggps-eta-audit-002` (R^square = R[[x1,x2,x3]], retraction, equality at closed points plus reduced Jacobson; explicit eta(T) = 5^(a+b) t, eta(S) = 5^(2a+b-1) d in R[1/5]). Accepted. Final editions of CEG+16/CEGGPS/BM still not compared.

### R2-F15. BP Corollary 9.11 does not give the central character BM 5.2 needs
- Path: `CL/ceggps-ext-bp-review-05/REVIEW.md`
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, 2026-11-08
- Point: Breuil-Paskunas Cor. 9.11 requires the scalar uniformizer to act trivially and yields the full smooth K-injective envelope; it does not supply the prescribed full central character, admissibility, G-socle = pi, or finite-field statement required at the opening of BM Theorem 5.2.
- Kind: HYPOTHESIS
- Next: Supplied by `BP-FIXED-CENTER-BRIDGE` (unramified twist with c^2 = zeta(5)^(-1), central eigensubspace, finite K-socle), accepted conditional on BP Section 9 symmetry and tree-gluing inputs, which are not reproved. The same review accepts ELEM-EXT (smooth fixed-center principal-series self-Ext has dimension one), closing the open item F19.

### R2-F16. Wrong compact character in the projective-lift application
- Path: `CL/ceggps-projective-lift-root-001/REVIEW.md`
- Reviewer/date: `/root`, 2026-11-08
- Point: In the BM 5.2 application the compact-module central character is eta = zeta_BM^(-1) (the smooth representation is dualized); version 002 did not keep it distinct from the smooth character.
- Kind: HYPOTHESIS (convention)
- Next: Corrected in `ceggps-elementary-suppliers-003`; lifting argument is uniform in eta.

### R2-F17. Finite projectivity of the residual projective cover not shown
- Path: `CL/ceggps-projective-lift-root-001/REVIEW.md`
- Reviewer/date: `/root`, 2026-11-08
- Point: The lifting lemma needs the mod-pi projective cover Pbar of the finite semisimple K-socle target to be finite projective; the proposal lacked that step. The reviewer supplied the bridge (lift finitely many generators, essentiality, splitting).
- Kind: GAP
- Next: Written into 003. Because the reviewer contributed it (and the eta request), this review is not independent for those two points; a separate anchor review is required and bound in the decision. Prior BM assertions (construction of x, torsion-freeness of Coker(x)) remain retained inputs; BM text is arXiv v3, not the Duke edition.

### R2-F18. "Jacquet dimension two" must mean the normalized smooth J_0
- Path: `CL/ceggps-sc06-09-review-05/REVIEW.md` (also `CLD/ceggps-eta-audit-001`, `-002`)
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, 2026-11-08
- Point: In SC06 the two-dimensional Jacquet module is Colmez's J_0(Pi_alg) of the smooth factor, not J(Pi_alg) of the full algebraic tensor product; only with that reading does VI.6.30(ii) give the isomorphism with D_crab.
- Kind: HYPOTHESIS (convention)
- Next: Recorded as a condition for any future integration; frozen proposal bytes unchanged.

### R2-F19. Smooth principal-series self-Ext input not closed in SC08
- Path: `CL/ceggps-sc06-09-review-05/REVIEW.md`
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, 2026-11-08
- Point: Reducedness (RED via BM 4.19/4.11/2.32) depends on the fixed-central-character smooth unramified principal-series self-extension space having dimension one, which this packet only retains (Schneider-Stuhler via BM). Also unclosed here: BP enlargement and projective-lift comparisons, eta-map supplier, generic-fiber regularity. Acceptance of SC06-SC09 is conditional.
- Kind: GAP
- Next: Ext closed by ELEM-EXT (F15 review); lift by F16/F17 review; eta by F14 review. Final CEGGPS/BM editions, patching and minimal-level inputs remain open.

### R2-F20. CEGGPS accepted text is internally inconsistent on the determinant exponent
- Path: `CLD/ceggps-final-gaussian-001/REPORT.md` (confirmed in `CLD/emerton-weak-map-review-05/REVIEW.md`)
- Reviewer/date: author `/root/astra_v14_baseline_gaussian`, 2026-11-08
- Point: Body Section 2.1 gives sigma_(A,B) = det^A Sym^B with labels (1-A, -A-B), i.e. Sym^(v-u-1) det^(1-v) for u<v. Introductory Example 1.2 and AA3 print exponent 1-a for increasing labels a<b, which conflicts. Related: p35 inserts an inverse cyclotomic twist relative to Paskunas (V_P = r_C tensor epsilon), which preserves inertial type but changes the unramified Weil parameter.
- Kind: ERROR (in the cited source's accepted/author version; not in the manuscript)
- Next: Route fixes the body convention. Whether the final Compositio edition has the same inconsistency is unknown (F21).

### R2-F21. Final CEGGPS edition never obtained
- Path: `CLD/ceggps-final-gaussian-001/REPORT.md`
- Reviewer/date: author `/root/astra_v14_baseline_gaussian`, 2026-11-08
- Point: Publisher endpoints returned HTML, not the PDF; all checks use arXiv v2 (accepted version, "precedes possible editorial changes"). Final definitions, hypotheses, determinant formulas and corrections for Sections 1.12, 2.1-2.2, 3.4, 6.14/6.17-6.21, 7.1-7.5 are unverified. Errata search was bounded only.
- Kind: LIMITATION
- Next: Left open; repeated as an open qualification in every later CEGGPS review in this batch.

### R2-F22. Dual in CEGGPS Theorem 7.4 and scope of Assumption 2.2 / Section 3.4
- Path: `CLD/ceggps-final-gaussian-001/REPORT.md`
- Reviewer/date: author `/root/astra_v14_baseline_gaussian`, 2026-11-08
- Point: Theorem 7.4 / equation (7.2) involve the R-linear dual of the universal global representation, so the displayed homology identity is not yet the cohomological weak map; duals and topologies must be handled. Remark 7.1: arbitrary tame level does not inherit the result (minimal level Gamma_1(N), no vexing primes, p>3). Section 3.4 chooses trivial inertial type and does not give an arbitrary supercuspidal-type auxiliary point; a Jordan-Holder constituent of a lattice does not lift by the theorem alone.
- Kind: HYPOTHESIS
- Next: Handled in `ceggps-route-001` and checked in `CLD/ceggps-route-review-05` (dualization at the eigenpoint; exactness of Hom_K(-, H_s) through a composition series; actual conductor N with 193 | N).

### R2-F23. Corollary 6.19 does not identify the projective-envelope fiber (C07)
- Path: `CLD/ceggps-route-review-05/REVIEW.md`
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, 2026-11-08
- Point: CEGGPS Cor. 6.19 gives only the modified Colmez image and nonvanishing of the fiber, not its identification with the local Banach representation nor absolute topological irreducibility. The chain needs Theorem 6.18's projective-envelope isomorphism plus Paskunas's Image fiber classification; "no inference from equal Colmez images alone is accepted".
- Kind: GAP
- Next: Author confirmed it as a retained Section 6 condition; supplied by `CLD/ceggps-source-closure-003` Section 2 and accepted as SC03-SC05 (F10, F11).

### R2-F24. Auxiliary CEGGPS route accepted only conditionally; C10 open
- Path: `CLD/ceggps-route-review-05/REVIEW.md`
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, 2026-11-08
- Point: C01-C09 accepted relative to retained source hypotheses; C10 is an open ancestor audit. Still required: modular-curve patching and its minimal-deformation/factorization inputs, the restricted crystalline Paskunas ancestor path, and the Henniart minimal-type and classical local-global joins (explicitly "unclosed in the packet"). Emerton 5.3.15 is an unpublished argument reconstructed, not a published theorem.
- Kind: LIMITATION
- Next: Partly addressed by later SC/Ext/BP/eta reviews; patching, minimal-type and local-global joins not stated as closed in this batch.

### R2-F25. Cited sources depend on the disputed supercuspidal identification
- Path: `CLD/ceggps-source-closure-003/REPORT.md`
- Reviewer/date: author supplement (source-review agent), date not stated
- Point: Paskunas BM Prop. 4.14 as printed cites Emerton's supercuspidal locally algebraic identification, and Image Theorem 12.7's proof invokes the same identification, so neither may be used. Colmez VI.6.50/VI.6.51 likewise point back to Emerton.
- Kind: GAP (circular dependency in cited sources)
- Next: Replaced by a restricted argument using only pure algebraic K-types on the supersingular block (Colmez VI.5.7, VI.6.13, VI.6.18, VI.6.30, VI.6.50(i); finite-exception count in the unframed space; Berger-Breuil 4.3.1, 5.2.7, 5.3.1-4). Accepted conditionally in the SC01-05 and SC06-09 reviews.

### R2-F26. Source-closure supplement: supplier checks left open
- Path: `CLD/ceggps-source-closure-003/REPORT.md`
- Reviewer/date: author supplement, date not stated
- Point: Not checked at freeze: BP Cor. 9.11 and Paskunas 2010 Prop. 4.6 final passages; the Schneider-Stuhler dimension-one Ext application; Kisin's finite-slope/crystalline deformation-ring inputs; regularity of the crystalline generic fiber; CEG+16 Theorem 4.1; CEGGPS 7.4 patching; minimal-type theorem; classical local-global compatibility. Does not use the BM cycle formula 6.6, so Hu-Tan's use of full Breuil-Mezard for arbitrary types is not closed.
- Kind: LIMITATION
- Next: Items 3-5 partly closed by F14-F17 reviews; item 6 and final editions remain open.

### R2-F27. Emerton 2011 draft prints det^b where det^(b+1) is required
- Path: `CLD/emerton-weak-map-gaussian-001/REPORT.md` (confirmed in `CLD/emerton-weak-map-review-05/REVIEW.md`)
- Reviewer/date: author `/root/astra_v14_baseline_gaussian`, date not stated; reviewer `/root/astra_quartic_opt05_anchor`, 2026-11-08
- Point: From published Emerton 2006 Thm 7.4.2, the algebraic factor is W_E(a,b) = Sym^(a-b-1) tensor det^(b+1). Draft pp97-98 (Section 7.4) print det^b, inconsistent with the draft's own p28. Weight-two test: det^b would give det^(-1) instead of the trivial representation, and no unramified twist can absorb it.
- Kind: ERROR (in the cited unpublished source)
- Next: Replacement det^(b+1) proposed for the type tau, the classical target and the final comparison together; accepted as conditional connection EME-NORMALIZATION. Historical draft not amended.

### R2-F28. Tame-level multiplicity in the transition 6.4.3 to 7.4.2
- Path: `CLD/emerton-weak-map-gaussian-001/REPORT.md` (confirmed in `CLD/emerton-weak-map-review-05/REVIEW.md`)
- Reviewer/date: as F27
- Point: Draft Remark 6.4.3 gives a map into unrestricted tame-level cohomology; nothing shows a chosen multiplicity vector is fixed by K_1(N), and Theorem 7.4.2 does not prove strong multiplicity one.
- Kind: GAP
- Next: Bypassed by the weak-map-to-smooth-factor lemma, which works with the full multiplicity space U (matrix units for rho, semisimplicity of S tensor U, Colmez VI.5.7). Accepted as EME-WEAK-TO-ALG; the single-cuspidal-system target decomposition remains an input.

### R2-F29. Existence of the weak map itself is not established
- Path: `CLD/emerton-weak-map-gaussian-001/REPORT.md` and `CLD/emerton-weak-map-review-05/REVIEW.md`
- Reviewer/date: as F27
- Point: The step "auxiliary point in the Hecke spectrum implies a nonzero map rho tensor B(rho|G_Qp) into the completed-cohomology eigenspace" is unfilled. The fiber lemma needs X(theta) to have a finitely generated admissible smooth dual, residue-field duality, and dense nonzero allowable fibers; none rebuilt. Faithfulness is insufficient (A = E[t], M = A[1/t] has zero fiber at (t)). Citing Colmez p466 instead would be circular.
- Kind: GAP
- Next: Left open (item EME-ACTUAL-X). The CEGGPS auxiliary route is proposed as a way to avoid X(theta), with its own obligations.

### R2-F30. O2 summary omitted two hypotheses
- Path: `EV/combined007/o2-o3-incorporation/REVIEW.md`
- Reviewer/date: `/root`, 2026-11-08
- Point: The inserted summary of O2 in incorporation 001 omitted absolute irreducibility of r and finiteness of the coefficient extension, relying on an unstated implication from the Weil-Deligne condition. The O3 first-order conclusion is conditional on exact extension, type-multiplicity and endomorphism hypotheses; type multiplicity is not inferred from type detection.
- Kind: HYPOTHESIS
- Next: Qualifiers added in incorporation 002; accepted. Later R1/N2 work is not incorporated and needs its own adoption records.

### R2-F31. Scalar chart map holds on the upper half-plane only
- Path: `CR3/suppliers/h5-full-b-map-review-001/REVIEW.md`
- Reviewer/date: not named in the file (author of the earlier geometric-isogeny connection), date not stated
- Point: The source chart (Lambda_tau = i_infty(O)(tau,1)^t, lambda = cz+d) is an upper-half-plane statement, not an all-component theorem; the all-component B-linear normalizer map must come from the intrinsic commensurable-lattice argument via the PEL comparison. The premise must be that N normalizes the maximal order's finite completion, not just the principal-level subgroup. Reviewer asked for both to be explicit.
- Kind: HYPOTHESIS
- Next: Made explicit in the proof; accepted. Limits: degree is controlled only at 11; the source capture is an HTML extract, not compared with the final PDF.

### R2-F32. Hom descent attributed to an endomorphism-only source
- Path: `CR3/suppliers/h5-geometric-isogeny-review-arithmetic-001/REVIEW.md`
- Reviewer/date: not named in the file (arithmetic reviewer), date not stated
- Point: The geometric-isogeny connection needed torsion/graph descent for Hom(A, A_sigma) between two conjugate surfaces, but the cited source covered endomorphisms only. In the records, the source span omitted the graph-descent line and the quadratic-correction card listed its own target paragraph as incoming evidence.
- Kind: GAP
- Next: Author 002 wrote the two-surface descent explicitly; author 003 fixed the two records. Accepted for four bounded connections; gives no degree bound, coherent cocycle choice or bounded Q-descent.

### R2-F33. Four of twelve current owner conclusions unsupplied
- Path: `CR3/suppliers/item29-current-owner-review-arithmetic-001/REVIEW.md`
- Reviewer/date: not named in the file (author of the scalar-normalizer provider), date not stated
- Point: Sign normalization, corrected all-prime realization, all-prime absolute irreducibility, and comparison/conductor have no supplying use; 36 obligation fields remain unresolved. The partial-owner records "are not evidence that their complete current claims have been supplied".
- Kind: GAP
- Next: Left open in this record. `EV/current-source-installation/selection/REVIEW.md` names later records (beta004, B005, four-H5-joins002) as supplying them; those are not in this batch.

### R2-F34. Forward-Hodge dependency records corrected
- Path: `CR3/v14-current-residual-ledger-002/REVIEW.md` (reporting `forward-hodge-independent-adoption-001`)
- Reviewer/date: `/root/v14_gi_selection_review`, date not stated
- Point: The earlier records confused divisor classes with the local Picard construction and listed a Hodge input to a descent step whose object was already algebraic ("fictitious Hodge input"); the centralizer's genuine Hodge and descent inputs are retained.
- Kind: ERROR (wrong dependency/object in the application record; second-hand report)
- Next: Corrected in forward-hodge-independent-adoption-001; adopted at that scope only.

### R2-F35. Residual ledger: what the 31 projections do not cover
- Path: `CR3/v14-current-residual-ledger-002/REVIEW.md`
- Reviewer/date: `/root/v14_gi_selection_review`, date not stated
- Point: Reviewer wrote the projection code himself. Full RC is not discharged (only the fixed-ell connection at 2668-2685). Yuan's coarse Lemma 2.1 is described as disputed and is avoided by the direct-stack route. A052/Frobenius, CM reciprocity and specialization premises of the conductor-one reduction are retained, not discharged. Parity consumers use full Selmer corank one, not Mordell-Weil rank or finite Sha.
- Kind: LIMITATION
- Next: Named owners (global registry, H5, GI, root integration) hold the remaining joins.

### R2-F36. All-prime irreducibility proof assumed a quadratic field the constructions do not have
- Path: `CR3/v14-resume-arithmetic-review-001/REVIEW.md`
- Reviewer/date: `/root/v14_arithmetic_review`, 2026-11-09
- Point: Paragraph 3 and the contract of the all-prime irreducibility proposal 001 require a named quadratic coefficient field E embedded in B. Neither the beta construction (99d 1357-1375) nor the b construction (8100-8120) names such a field; both use a splitting field and matrix units. Proposal 001 is not accepted as their literal attachment.
- Kind: HYPOTHESIS
- Next: Changes required: frozen successor using the original matrix-unit idempotent. `CR3/suppliers/b-family-attachment-resume-proxy-001/REPORT.md` cites the accepted successor `all-prime-irreducibility-matrix-units-002`.

### R2-F37. Beta all-prime compatibility: coefficient field, ell != p, and citation
- Path: `CR3/v14-resume-arithmetic-review-001/REVIEW.md`
- Reviewer/date: `/root/v14_arithmetic_review`, 2026-11-09
- Point: Beta proxy 001 must state the common finite coefficient field, restrict the trace formula to ell != p, and cite Milne 1986 Prop. 12.9 (p125) instead of an unqualified "I Proposition 10.20". Checked conventions: arithmetic p-Frobenius (not q-Frobenius); the trace is Tr(e_p)/(2m), the denominator m must not be dropped. The r3-only receipt cannot cover p = 3. The 45 ordinary obligation fields stay unresolved.
- Kind: HYPOTHESIS
- Next: Author agreed; acceptance awaits the frozen successor. The b-family proposal (same folder as F36) already incorporates these points but is itself only "proposed, awaiting independent review".

### R2-F38. Primitive selection before the weight is known
- Path: `EV/current-source-installation/classical/independent/REVIEW.md`
- Reviewer/date: not named in the file (prior Pan record-adoption reviewer), date not stated
- Point: Primitive normalization was added to the review scope; Li's weight-two theorem cannot be used before k = 2 is known (Sol's "early-Li" scope finding), and one may not divide by the possibly zero first coefficient of the original oldform. Weight one must be excluded separately since Kato's formula needs k >= 2.
- Kind: HYPOTHESIS
- Next: Connector uses Deligne-Serre 1.9/1.6/1.7 for the primitive constituent and 3.1/4.1 for the k = 1 exclusion; accepted, "no substantive repair was requested". Does not reprove Calegari/Pan modularity.

### R2-F39. Finite replays do not give denominator nonvanishing or integrality
- Path: `EV/historical-finite-bindings/INDEPENDENT-REVIEW.md`
- Reviewer/date: `/root/astra_v14_source_review`, run dated 2026-11-07
- Point: The F8 / 4973 / 962 polynomial-identity replays do not prove denominator nonvanishing or integer input projection; the 962 checker's 127 quotient-domain obligations remain proof obligations. The 4973 source audit is not a fresh rerun, and the historical 5173-coordinate endpoint review is not approval of every later transformation.
- Kind: LIMITATION
- Next: Left to the manuscript's source arithmetic and the final coverage review.

Count: 39 findings. ERROR 8 (F1, F2, F4, F5, F6, F20, F27, F34); GAP 13 (F3, F10, F11, F12, F14, F17, F19, F23, F25, F28, F29, F32, F33); HYPOTHESIS 9 (F15, F16, F18, F22, F30, F31, F36, F37, F38); OVERSTATED 1 (F7); LIMITATION 8 (F8, F9, F13, F21, F24, F26, F35, F39).


## Internal reviews, batch 3

Path prefixes used below (all under `research/version14/evidence/`):

- `P13/` = `protocol-v1.3/activation-author/tree/`
- `P14/` = `protocol-v1.4/`
- `RC3/` ... `RC13/` = `release-completion-003/` ... `release-completion-013/`

Dates: most reviews state no date; "n.s." = not stated. Kinds: ERROR / GAP / HYPOTHESIS / OVERSTATED / LIMITATION as defined in the task.

Non-mathematical software defects (controller code for the review protocol) are flagged in the table only, not listed as findings: credential leak into collector subprocess (ingress), mutable snapshot allowing history overwrite and `42.0` accepted as repo ID (git state), key-registry decoding incompatible with operator codec and same-repo-only PR reader (runtime).


### R3-F1. Semisimple base change: G_Q-stability of the idempotent factor was not secured
- Path: `RC4/v14-current-arithmetic-suppliers-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: Source record QM-SEMISIMPLE-BASE-CHANGE (matrix-unit irreducibility via Faltings) as first written did not require a continuous normalized G_Q-action over the original finite splitting extension commuting with B. The reviewer states that "restriction alone would not make the chosen idempotent factor G_Q-stable". The same delta made AC-CHEBOTAREV explicit about continuous class functions valued in one common finite extension of Q_ell (conclusion is trace equality only, not isomorphism).
- Kind: HYPOTHESIS missing.
- Outcome: Repaired in successor `v14-current-arithmetic-suppliers-002` (exact four-field delta); accepted. Full End=B, its field of definition and the normalized restriction remain assumptions. Reviewer did not repeat the full published-source audit.

### R3-F2. Yuan model source card claimed more than the source gives (fine full-level scheme)
- Path: `RC4/v14-current-geometry-source-adoption-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: The Yuan MODEL import was narrowed: the source supplies only the maximal stack at n(U)=1 over Z (discriminant 210: regular, flat, semistable, proper, universal abelian surface, smooth over Z[1/210]). It does not construct the fine full-level scheme; the retained projection's historical full-level language is explicitly not adopted. Rank 72, rigidity, projectivity, generic inertia and degree 576 are outside the card. Also noted: the square-line multiplier in INTEGRAL->METRIC is 210, neither 210^2 nor its inverse.
- Kind: OVERSTATED claim (source import).
- Outcome: Four MODEL fields narrowed in successor 002; the full marking is constructed separately (current lines 7687-7700, Buzzard supplies the fixed-order element). Accepted. Three stale supplier line-pins were also corrected (clerical). Reviewer claims no new review of the original published papers.

### R3-F3. CM contract wording wrongly restricted all discriminants to -3/-4
- Path: `RC4/v14-h6-normalization-review-001/REVIEW.md`
- Reviewer/date: /root/v14_h6_coverage; n.s.
- Point: In the H6 CM application contracts (version 001) the exceptional-case wording appeared to restrict all discriminants to -3 and -4, instead of including those as exceptional cases alongside general (including nonmaximal) orders.
- Kind: ERROR (misstated scope of a contract).
- Outcome: Corrected in 002; accepted. PENDING.json still lists absent nodes and present-but-unapproved geometry nodes; dependency graph not closed. Reviewer discloses having authored earlier H6 prose.

### R3-F4. LP04 comparison: "lower degree" was wrong, only degree-rank drops; S9-11 antecedent missing
- Path: `RC5/v14-gi-normalization-review-h6-001/REVIEW.md`
- Reviewer/date: /root/v14_h6_coverage; 2026-11-09
- Point: The LP04 contract said the auxiliary group has lower degree; the source gives only strictly lower degree-rank (ordinary degree drops only at R=1). The S9-11 contract also omitted an explicit antecedent. Reviewer requested both; they "restore stated source premises".
- Kind: OVERSTATED claim / HYPOTHESIS missing.
- Outcome: Repaired in successor `v14-gi-normalized-subset-002` (seven-leaf diff); accepted as normalization only, not a fresh reconstruction.

### R3-F5. Section 13 at s=3 needs a degree-zero converse that GI-15-CONVERSE (d>=1) does not provide
- Path: `RC5/v14-gi-remaining-review-h6-002/REVIEW.md`
- Reviewer/date: /root/v14_h6_coverage; 2026-11-09
- Point: The Section 13 argument at s=3 invokes the converse to the inverse theorem in degree zero, but the recorded supplier GI-15-CONVERSE is stated only for d>=1. Reviewer located the mismatch.
- Kind: GAP.
- Outcome: Repaired by an inline argument appended to four S13 justifications: a degree-zero nilsequence on a taut model is a constant c, so |avg(f c)| = |c||avg f| and U1(f)=|avg f|; positive correlation excludes c=0. Accepted. The four outer Gaussian contracts are outside the review.

### R3-F6. GT08/GT12 imports: four precision corrections (Bohr quantifier order; A.10 used backwards; filtration type)
- Path: `RC6/v14-gt12-gt08-inputs-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: Reviewer requested four corrections to source profiles: (i) Bohr regularity (GT08 Def 2.6, Lemmas 8.1-8.2): quantifier order was wrong; only the bounds are fixed in terms of eta beforehand, the regular radius and test may vary with the finite system (P,u,S); (ii) lattice-logarithm profile may state only GT12 Def 2.1 and A.2; the implication "compact subgroup quotient => rational Lie algebra" is a local maximal-subalgebra argument and cannot be obtained by invoking A.10 backwards; (iii) RANK uses a rational filtration, not an ambient-induced one; (iv) locator corrections (Def 2.6 p.84, Lemmas 8.1-8.2 pp.105-106).
- Kind: HYPOTHESIS / convention (quantifier order, direction of an implication).
- Outcome: Repaired in successor `v14-gt12-gt08-inputs-author-002`; accepted for twelve imports. LIN has no GT12 use and is excluded; GTZ, Hall, selection, cube inputs remain with other reviewers.

### R3-F7. Known defects in the published GT08/GT12 sources that the proof must route around
- Path: `RC6/v14-gt12-gt08-inputs-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: The review records that (a) the general quadratic-extension statement in the GT08 chain is false; only the H={0} proper-progression finite-box specialization is used; (b) the skew-iterate route is erroneous and is bypassed by the connected polynomial realization; (c) the right-period implication is printed with the wrong orientation; the period is derived from gamma(n)^-1 gamma(n+r); (d) a bounded-height reading of Lemma 8.4 does not support the large-offset transfer, which uses the MF inverse-affine argument; (e) MF uses only the published equal-side obstruction theorem (GT14), no arbitrary-side version; (f) text extraction dropped equality bars in GT14 p.1176 / GT12 p.522 (ranges are >=1, degree >=0).
- Kind: ERROR in cited sources (worked around) / HYPOTHESIS.
- Outcome: Local replacement arguments are in the module proofs and were accepted at their scope; the DF001 objection is retained as history.

### R3-F8. Section 13 bounded selection: earlier record substituted the assembly's initial selection; printed GTZ A.5 diagonal argument is invalid
- Path: `RC7/v14-gi-external-core-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: The earlier S13 connection used the assembly's initial selection in place of the selection S13 actually needs (a common bounded family was assumed at the outset). It was removed and replaced by a new derivation (GI-S13-BOUNDED-SELECTION.md): pointwise witnesses, countable tags, a genuine A.10 exhaustion, nested finite-intersection to a common standard stage, internal choice. The review states the proof "does not use the invalid bare diagonal from the printed A.5 proof". Also: B.10's printed composition is malformed and an arbitrary group surjection does not suffice (layerwise surjectivity incl. layer zero is checked); Tointon's collection uses bracket length, so the weighted Hall quotient needs the local triangular BCH proof.
- Kind: GAP (repaired) plus ERROR in cited source.
- Outcome: Repaired in packet `v14-gi-external-core-004`; 26 connections accepted. Reviewer explicitly does not certify that the import list is exhaustive; universal-model, general compact-approximation and other Appendix A inputs still need records.

### R3-F9. GTZ E.8(vi) has a domain mismatch; almost-all internal choice needs increasing bad sets; limit orders described the wrong operation
- Path: `RC8/v14-gi-external-residual-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: (i) GTZ E.8(vi) p.1354 as printed has a domain mismatch; the degree-pullback is instead obtained for fixed standard integer linear maps by the direct iterated-difference identity, and does not give preservation of arbitrary multidegree rectangles. (ii) The almost-all variant of the internal-choice import lacked the hypothesis that the bad sets are increasing. (iii) Three needed-assertions described a coefficient lift where the consumer actually performs coefficient extraction. (iv) The DF and MF Taylor bounds O(N^-j), O(N^-|alpha|) do not follow from B.9 alone; a formal-weight/triangular extraction argument is needed (DF connection re-pointed to lines 181-259).
- Kind: ERROR in cited source / HYPOTHESIS missing / GAP in connection.
- Outcome: Corrected between 001 and 003 (002 had an empty manifest); fifteen imports accepted. Not established: exhaustiveness of the historical D.4-D.6 disposition, LINKED063-067 reconciliation.

### R3-F10. LP02 BCH-lattice connection quantified over arbitrary generating sets
- Path: `RC8/v14-gi-foundational-tail-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: The BCH-lattice statement (common D clearing BCH denominators, discreteness, compact representatives) holds for the fixed homogeneous rational model with positive weights, not for arbitrary generating sets as earlier quantified. Its image in the original Gamma additionally needs the separate rational-coordinate scaling input. For the TAUT real-hull use, GTZ Section 3 alone does not prove the normalization (composite local derivation).
- Kind: OVERSTATED claim (quantifier).
- Outcome: Corrected in packet 003; two connections accepted.

### R3-F11. Silverman reduction-kernel sequence used without a minimal-model hypothesis
- Path: `RC8/v14-heegner-descent-inputs-review-001/REVIEW.md` (author side: `RC8/v14-heegner-descent-inputs-author-002/REPORT.md`)
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: The FORMAL-COHOMOLOGY connection applied Silverman VII.2.1-2.2 (reduction kernel = formal group) without stating that the Weierstrass model is minimal; a nonminimal integral chart is not the whole reduction kernel. Also recorded: Howard's theorem is only corroboration; the broad old-conductor Frobenius congruence rests on the local CM argument with its moduli/supersingular-kernel/integral-extension premises.
- Kind: HYPOTHESIS missing.
- Outcome: Repaired in author-002 (minimal model over F, stays minimal under unramified extension); accepted. Not discharged: class-field reciprocity, CM moduli and orientations, eigenquotient, Neron foundations, fixed torsion exponent.

### R3-F12. Local norm functoriality cited to the wrong Milne statement; correct source has no printed proof
- Path: `RC11/v14-beta-local-source-inputs-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: For the step beta^4=1 on O_F^* (dyadic conductor bound of beta), the proof cited Milne CFT V Prop 3.3 (p.157), which is a global ideal diagram, not the needed local-unit norm statement. The correct statement is III Lemma 3.2 (p.107), whose printed proof reads "To be added"; the Res/Cor compatibility comes from the Theorem 3.1 discussion. The source is author course notes (v4.03), not a journal theorem. Serre's source is the 1967 Cassels-Frohlich chapter VI, not the 1979 Local Fields book.
- Kind: HYPOTHESIS / source not as cited.
- Outcome: New source card acknowledges it; three imports accepted. Correction of the locator in the current proof is NOT yet integrated (requires a preserved successor and, per `RC11/v14-source-extensions-rollout-review-001`, a distinct corrected proof path and a second frozen source supplement).

### R3-F13. Final completeness: N08 supplier proves the reverse direction, consumer needs the forward one
- Path: `RC12/v14-final-completeness-inputs-review-001/REVIEW.md` (author: `RC12/v14-final-completeness-inputs-author-002/REPORT.md`)
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: In packet 001, V13-FINAL-COMPLETENESS consumed ordinary node N08 for the half-chart step, but N08 states reverse half-chart restoration while completeness needs the forward forgetting map (source line 108). The stated supplier did not supply the needed direction.
- Kind: ERROR (wrong-direction dependency).
- Outcome: Repaired in 002: forward clause bound as inline proof ACTIVE-FINAL-COMPLETENESS-HALF-CHART-PROJECTION, N08 edge removed. Sixteen connections and six no-direct-owner dispositions (N08, N17, N22, N38, N39, N46) accepted for this consumer only; graph change must still be applied explicitly; GA-SIMULTANEOUS-PRIMES outside review.

### R3-F14. Finite-field residue cohomology: replacement proof gave only H1, source sentence claims all positive degrees
- Path: `RC13/v14-heegner-finite-field-input-review-001/REVIEW.md`; resolution in `RC13/v14-heegner-finite-field-input-review-002/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: Supporting note line 85 asserts vanishing of all positive cohomology of the additive residue module via normal-basis inducedness. The 001 proof established only H1 (trace surjectivity, cyclic cocycle argument); the reviewer accepted "at the exact H1 scope" and said the stronger sentence was not covered.
- Kind: GAP (proof weaker than the sentence it replaces).
- Outcome: Repaired in author-002: normal basis proved via minimal polynomial t^r-1 of Frobenius (valid when char divides r), periodic Z[G] resolution gives all positive degrees. Accepted in review-002. Formal filtration, lifting, completeness, Lang step and Neron geometry remain separate; overlay not installed.

### R3-F15. Prime-realization source profiles misdescribed the source's parameter ranges
- Path: `RC11/v14-prime-realization-inputs-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: In 001 the parameter_range and quantifier fields of three source profiles (BMOR Theorem 1.2 theta bound, CRT) carried the consumer's divisible-by-8 restriction rather than the source's actual domain (every reduced class, q>=3, x above a q-dependent threshold; no uniformity in q). Milne ANT CRT is course notes; a local Bezout construction is given so it is not needed.
- Kind: HYPOTHESIS / convention.
- Outcome: Corrected in 002 (six leaves); accepted. Reciprocity, type realizability, HL/BFH nonvanishing remain separate.

### R3-F16. Finite evidence: obsolete coefficient bound and rejected first 299 wiring; no replay rerun
- Path: `RC3/item4-finite-transport-review-001/REVIEW.md` (also `RC3/item4-current-transport-review-001/REVIEW.md`, `RC3/item4-current-transport-author-proxy-001/REPORT.md`)
- Reviewer/date: /root/v14_h6_coverage (finite), /root/v14_gi_selection_review (connective); n.s.
- Point: The reviews record that the ordinary 314-variable quartic's coefficient maximum 3^4098+K0 lies between 2^6495 and 2^6496, and that the historical "<2^3247" bound is obsolete; the first 299 implementation was rejected and corrected reciprocal 299-r2 is selected; the 514-variable bound is not the selected 314 one. The reviewer checked checksums only: no optimization or full replay rerun; the original P-star replay is a wiring/size check, not an expanded polynomial or a proof of recognizer arithmetic; the block-equality check is credited to another reviewer.
- Kind: LIMITATION (with recorded historical ERRORs already superseded).
- Outcome: Finite evidence reuse accepted; arithmetic soundness/completeness, input-projection equivalence and height/modularity inputs left to other reviews.

### R3-F17. Kato carryforward does not establish five stronger premises
- Path: `RC5/v14-current-carryforward-adoption-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: The adopted Kato record keeps index domain, lattice map, normed dyadic class and conditional K15 interface but "does not newly establish" abelian-restriction unipotence, cyclotomic absolute irreducibility, both-sign non-torsion, local control or the restricted converse. Empty dependency lists are a legacy representation, not a claim of no dependencies.
- Kind: LIMITATION.
- Outcome: Left open for final coverage. (README span count "nineteen" vs twenty was a clerical typo, fixed in 002.)

### R3-F18. QUARTIC-299-COMPOSITION is not the announced upper theorem
- Path: `RC5/v14-aggregate-transition-review-h6-003/REVIEW.md`
- Reviewer/date: /root/v14_h6_coverage; 2026-11-09
- Point: Replacing the pending dependency by four conditional interfaces does not discharge their antecedents; the full announced upper bound is carried by a separate proposed node V14-QUARTIC-299-314-THEOREM (authored by this reviewer, not approved here).
- Kind: LIMITATION.
- Outcome: Left open.

### R3-F19. Degree/corollary applications are author proposals with unowned incoming claims
- Path: `RC5/v14-degree-corollary-applications-author-001/REPORT.md`
- Reviewer/date: author /root/v14_h6_coverage; n.s.
- Point: Author report (not a review): CTS alone is not the full degree obstruction; minimum degree also consumes QUARTIC-299-COMPOSITION; V14-MAIN-POLYNOMIAL-DEFINITION is an incoming new claim not proved by naming it; integral HIT, DPRM/four-squares and Mazur conventions have no normalized source IDs yet.
- Kind: LIMITATION.
- Outcome: Awaiting independent comparison; not stated further in this batch.

### R3-F20. Generic-conductor CM reduction accepted for supersingularity only
- Path: `RC13/v14-heegner-cm-reduction-review-001/REVIEW.md`
- Reviewer/date: /root/v14_arithmetic_review; n.s.
- Point: Gross-Zagier p.199 gives only supersingular reduction at inert primes (order discriminant d^2 D_K, symbol (D_K/ell)=-1). Not supplied: integral realization, closure of raising kernels, uniqueness of the order-ell subgroup scheme, specialization of prime-to-ell level structure, equality of modular points, extension and Frobenius compatibility of pi. The source's own CM-reduction ancestry was not re-proved.
- Kind: LIMITATION.
- Outcome: Those prerequisites of the full CM congruence remain separate; card not yet installed.


## Internal reviews, batch 4

All paths are relative to the repo root; the common prefix `research/version14/evidence/` is abbreviated `E/`. Most reviews in this batch are bounded "source-to-consumer" acceptances; none reports a false theorem in the manuscript. The findings below are the places where a reviewer required a change, identified a gap or over-attribution, or explicitly left something unchecked. "Not stated" means the review gives no date.


### R4-F1. Milne ADT I.3.8 erratum is transitively relevant and was omitted (M-03)
- Path: `E/release-completion-017/milne-review/REVIEW.md` (author side: `E/release-completion-017/milne-author-r3/REPORT.md`)
- Reviewer / date: `/root/astra_quartic_opt05_anchor`, 2026-11-07; author `/root/sol_protocol_final_review`
- Point: The printed proof of Milne, Arithmetic Duality Theorems I.3.8 (p.46) uses an invalid completion of the infinite unramified union. The author's record treated it as irrelevant because I.3.8 is not literally cited, but I.6.3 (p.74) invokes it for finite local support of global H^1 classes, which feeds the global Sha setting used by the I.7.3 isogeny identity (7.3.1) consumed at manuscript 4250–4359. The official addendum repairs it by working over each finite complete unramified extension first, then passing to the union.
- Kind: GAP or missing justification (unrecorded dependence on a corrected source proof)
- Outcome: Repaired in author record R3 (finite-complete-extension-first chain recorded). Reviewer checked the corrected source argument and notes manuscript 3214–3242 already uses the same finite-extension-first order. No manuscript change.

### R4-F2. Addendum coverage claim was false: "complete one-page" document is ten pages (M-01)
- Path: `E/release-completion-017/milne-review/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor`, 2026-11-07
- Point: The original author freeze (`SOURCE-BINDINGS.json:18`) asserted it had read the complete official second-edition ADT addendum as a one-page document; only the first page had been read. The addendum has ten pages with substantive corrections beyond page 1 (I.3.8, I.6.24 S-unit restriction, I.6.2, compact-support and flat-cohomology repairs, III.6.3 Weil restriction).
- Kind: OVERSTATED claim (of what was checked)
- Outcome: Reviewer read all ten pages independently; R2/R3 successors pin the ten-page source with a full applicability record. The false R1 field is preserved and explicitly not accepted. Reviewer states this is not evidence any V14 theorem is false.

### R4-F3. Wrong domain description for Milne Exercise I.2.21 (M-02)
- Path: `E/release-completion-017/milne-review/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor`, 2026-11-07
- Point: Author R2 described the field of Exercise I.2.21 (pp.39–40) as equal positive characteristic. It is a two-dimensional local field of characteristic zero with positive-characteristic first residue field, so "characteristic zero" alone does not separate it from the manuscript's fields; the correct non-use argument is that the manuscript's fields are ordinary one-dimensional finite extensions of Q_p.
- Kind: ERROR (in the source-applicability argument, not in a manuscript theorem)
- Outcome: Corrected in R3.

### R4-F4. Brauer reciprocity citation too broad; exact replacement proposed
- Path: `E/release-completion-017/milne-review/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor`, 2026-11-07
- Point: At manuscript 746–783 (scalar descent / comparison of two classes in H^2(Q, mu_2)) the Chapter I citation of Milne ADT does not locate the needed statement; the global Brauer exact sequence used (injectivity into local invariants, sum zero) is displayed in the proof of II.2.1, p.164. The order-two local comparison (obstruction vanishes iff the local character is trivial on -1; at p=2 no surjectivity of squaring on the sign factor is claimed) was supplied as connecting argument.
- Kind: GAP or missing justification (citation plus short connecting argument)
- Outcome: 425-byte `PROPOSED-BRAUER.tex` accepted as replacement for lines 770–774; not installed by this review. The uncited repeat at 7209–7245 passes the same check.

### R4-F5. Milne review: what was not covered
- Path: `E/release-completion-017/milne-review/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor`, 2026-11-07
- Point: The acceptance of the isogeny calibration (4250–4359) is conditional on the Edixhoven component-number input (4345–4364) and the forward theorem giving finite Sha at the known rank-zero/rank-one constituents. The Nekovar global Selmer-cone theorem, coefficient-ring transport, support switches, the real-place complex (13238–13256, which uses Tate cohomology I.2.13/I.3.7 and is not an application of I.3.2), and Poonen–Stoll's alternating pairing are explicitly not reviewed.
- Kind: LIMITATION
- Outcome: Left to separate reviews.

### R4-F6. Picard-variety identification over-attributed to Silverman (FH-001)
- Path: `E/release-completion-017/forward-hodge-independent-adoption-001/REVIEW.md`
- Reviewer / date: `/root/astra_picard_independent_001`, not stated
- Point: Author packet 002 attributed an identification of the Picard variety directly to Silverman's divisor-class proposition. Silverman supplies only the degree-zero divisor-class group; algebraic identification, representability and the norm/base-change construction are local arguments with other standard inputs (Milne 1986 Jacobians Thm 1.1, Stacks).
- Kind: OVERSTATED claim (source attribution)
- Outcome: Narrowed in successors 003/004; quotient proof itself unchanged.

### R4-F7. Spurious dependency: generic torsion descent does not use Milne's Hodge equivalence (FH-002)
- Path: `E/release-completion-017/forward-hodge-independent-adoption-001/REVIEW.md`
- Reviewer / date: `/root/astra_picard_independent_001`, not stated
- Point: The generic descent lemma starts from an already algebraic complex endomorphism and does not consume Milne's complex Hodge equivalence; the recorded use/edge was a prerequisite that the proof never uses. The centralizer step does consume both the Hodge comparison and the descent result.
- Kind: OVERSTATED claim (dependency record)
- Outcome: Dependency removed in successor 004. (FH-003, stale line numbers, is clerical.)

### R4-F8. Forward/Hodge adoption: unresolved fields and unaudited sources
- Path: `E/release-completion-017/forward-hodge-independent-adoption-001/REVIEW.md`
- Reviewer / date: `/root/astra_picard_independent_001`, not stated
- Point: 72 unresolved fields in the frozen application records remain unresolved; published sources were hash-verified but "not all freshly re-audited page-by-page"; Mordell–Weil source ancestry and standard-algebra source ancestry (for the quaternionic alternatives B and M2(k)) remain open; reviewer's own Picard acceptance covers only combined005 1976–2005, not the Kato application or the whole forward lemma. Reviewer also notes the 470 mechanical checks on packet 002 passed despite the semantic defects F6/F7.
- Kind: LIMITATION
- Outcome: Left open at stated scope.

### R4-F9. Five-to-three comparison: iota_3 mis-described as extending a map into Qbar_5
- Path: `E/release-completion-017/five-to-three-independent-review-001/REVIEW.md`
- Reviewer / date: not named in the file; not stated
- Point: In the prime-5 to prime-3 trace transfer (manuscript 8100–8131), the proof described the embedding iota_3 as extending a map with codomain Qbar_5. It must extend the original prime-three coefficient embedding of the common number field, chosen independently of iota_5; equality of algebraic numbers is established via iota_5 and then pushed through iota_3.
- Kind: ERROR (wording of the construction; the argument is otherwise accepted)
- Outcome: Corrected in author-sol-002 (sole proof change). Accepted relative to named inputs: Faltings semisimplicity, known r_5 realization, classical realization at 3, Chebotarev/Brauer–Nesbitt, and the separately reviewed full-B maps. No recursive audit of Milne 1986 Prop. 12.9.

### R4-F10. Semisimplicity of the classical representation U_{f,3} was an unneeded/unsupplied premise
- Path: `E/release-completion-017/five-to-three-length-review-arithmetic-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review` (self-described "arithmetic" complementary reviewer; route suggested by Root and SourceReview), not stated
- Point: The earlier comparison listed "semisimplicity inputs" for U_{f,3}. Successor 003 replaces this by a finite-length deduction: trace equality plus Brauer–Nesbitt identifies semisimplifications, and since r_3 is absolutely irreducible, U_{f,3} has one composition factor and is itself irreducible, so isomorphic to r_3. The deduction requires absolute irreducibility of r_3, which this review does not check.
- Kind: HYPOTHESIS or convention not checked (premise removed; replacement premise must be bound)
- Outcome: Accepted for the finite-length step only. Final projection must bind actual absolute irreducibility of r_3 and the classical trace realization; the all-prime irreducibility companion and the Frobenius/reduction/degree-polynomial arguments are outside this decision.

### R4-F11. Degree/sign normalization for quasi-isogenies needed its own imports
- Path: `E/release-completion-017/v14-arithmetic-active-connections-review-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: Milne 1986 Thm 8.2 (pp.115–116) concerns genuine isogenies, while the manuscript applies a degree function to rational multiples (quasi-isogenies) to normalize signs. Reviewer required two separate sign-degree imports: D(u)=deg([m]u)/m^4 is independent of the clearing denominator by multiplicativity, and D(cu)=c^4 D(u), giving c/|c| via positive fourth roots. Reviewer also required precise source/application quantifiers and correction of the Faltings citation to the retained 1986 Complements Theorem 1(a)–(b), p.204.
- Kind: GAP or missing justification
- Outcome: Repaired in author packet 002 (two degree records added, 33 to 35 uses). Reviewer notes this "does not prove rationality of c or split the resulting cocycle." The absolute-irreducibility connection requires full End = B over the actual field of definition of all endomorphisms, which the source does not construct; that remains an incoming obligation.

### R4-F12. Determinant/finite-image step in the modularity argument needed an explicit polarization pairing and an explicit finite-image hypothesis for alpha
- Path: `E/release-completion-017/v14-arithmetic-modularity-imports-review-001/REVIEW.md` (pairing later supplied: `E/release-completion-017/v14-polarization-pairing-input-review-001/REVIEW.md`)
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: In the generic modularity proof (manuscript 476–680), the Kato step needs alpha(G_Q) finite; "weight zero alone would not suffice." Packet 002 adds this as an explicit incoming hypothesis and adds two polarization-determinant records: det(V_5)=cyclotomic^2 from the nonzero top form of an alternating G_F-equivariant Tate pairing, hence alpha^2=1 on an open subgroup. The modularity-imports review states the pairing itself is not constructed or sourced there.
- Kind: GAP or missing justification
- Outcome: Hypothesis made explicit in 002. Pairing supplied by a separate packet (Milne 1986 pp.131–134, Lemma 16.2(e), Prop. 16.6), accepted without needing principal polarization, prime-to-5 degree or good reduction at 5; the overlay is not yet installed. The identification of the normalized representation's restriction with the actual Tate representation and its two-copy identity remain separately supplied hypotheses.

### R4-F13. Spreading-out claim was wrong as stated for quasi-homomorphisms
- Path: `E/release-completion-017/v14-direct-p5-finite-ramification-review-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: The first version asserted (ambiguously) that "rational homomorphisms" extend over a good model after deleting finitely many primes. Only genuine homomorphisms extend; quasi-homomorphisms first need a common denominator cleared (the source uses m*mu_sigma). The good-reduction/unramifiedness conclusion itself needs no quasi-homomorphism extension.
- Kind: GAP or missing justification (imprecise statement in the source records)
- Outcome: Repaired in successor 002; six inputs accepted. Finiteness of ramification is qualitative only; no conductor bound follows.

### R4-F14. Bound 324 was attributed to the wrong source
- Path: `E/release-completion-017/v14-datum-tame-inputs-review-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: The retained A078 proof (parallel-geometry-report.md 73–89) attributed the acting-group bound 324 to source A001. A001 does not supply it; the bound comes from the separately supplied B11 normalizer calculation (4*3^4 = 324, a characteristic-zero degree bound). Reviewer also keeps odd contact valuation inside M_S(u) "rather than declared harmless."
- Kind: OVERSTATED claim (source attribution)
- Outcome: Proposal consumes the B11 bound explicitly; old shorthand "not revived." Accepted within the conditional A078 scope; smooth integral model, genus/orbifold computation and stable-model inputs remain separate.

### R4-F15. Anchor constant mismatch between cited historical argument and current text
- Path: `E/release-completion-017/v14-middle-inherited-source-review-root-001/REVIEW.md`
- Reviewer / date: `/root`, not stated
- Point: For COMPOSE-ANCHOR the first packet cited only the historical 3-adic anchor with C=3^(2^24), whereas the current manuscript uses C=3^(2^25) (10391, 10411–10417) with a doubled-index scalar transition (10929–10973). The stated lower bounds follow from the current constant, not the historical one; the doubled s lies in 2*3^(2^24-1)Z.
- Kind: GAP or missing justification (source record cited an argument with a different parameter)
- Outcome: Corrected packet 002 cites the current passages; reviewer classifies it as a source-record omission with an existing manuscript derivation, not a mathematical repair. HEIGHT-LUCAS is accepted only as a conditional use: the scalar/contact-height inequalities are assumed, not proved, in this review.

### R4-F16. RC source-role inventory (main 2588–6674): wrong-direction and statement-only suppliers; 33 bindings still pending
- Path: `E/release-completion-017/v14-main2588-6674-independent-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: Earlier inventory versions cited statement-only or wrong-direction ranges for PC, bad reduction, the positive complex, moving determinants, matrix spanning, augmentation, generic patterns, the final family bound and the functional. In particular lines 6183–6200 use the original restricted-RC corank-one hypothesis and the known companion's rank-zero result, not a forward rank-one theorem at an unknown base. Reviewer stresses finiteness of Sha is used only at established analytic cases and local torsion budgets are not finiteness of Sha.
- Kind: GAP or missing justification (in the dependency inventory), plus LIMITATION
- Outcome: Seven final findings corrected in version 010; accepted as a partial inventory. All 33 entries of PENDING.json remain unresolved by this receipt (repeated published-source occurrences, operator/network derivations, Neron lifting and residue cohomology, duality occurrences, local/global Euler inputs).

### R4-F17. RC pending list: 18 of 33 bundles had outstanding application/derivation verification
- Path: `E/release-completion-017/v14-rc-pending-reconciliation-review-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: Outstanding at this review (original zero-based rows): Partial 3 (open-image/irreducibility, Kummer translation/injectivity, finite-field Kummer), 5 (Waldspurger application at 3430–3443), 26 (Kummer/S-unit input), 27 (local elliptic completion and derived Kummer dimensions 5484–5489); Delegated 4, 6 (odd-theta, seed/off-filter/doubling), 14–16 (Frobenius/ring-class principal ideal, prime-to-ell torsion specialization, formal inverse), 23, 25 (compact Kummer/UCT/isogeny comparison; height implication at zero derivative); Open 7 (odd lower bound and normalization), 12 (Weil pairing in the conjugate coefficient construction), 17, 18 (integral Shapiro/transfer homotopies; tame-resolution/cup/res-cor/bar-resolution), 20, 21 (Hilbert class field/Kummer/ring-class relations; repeated open-image/cyclotomic determinant), 32 (integral duality and Ext-torsion). Reviewer warns: characteristic-zero Kummer must not silently replace the finite-field Kummer input, and known-zero calibration must not replace the unknown-base height argument. "Reviewed occurrence" does not mean merged.
- Kind: LIMITATION (open verification items)
- Outcome: Left open in this review. Other reviews in this batch address several of them at bounded scope: rows 3 (`v14-rc-witness-kummer-review-001`, `v14-rc-witness-reduction-review-001`), 5, 7, 27 and the tame small complex (`v14-rc-four-residual-inputs-review-001`), 14–16, 23, 25 (`v14-rc-five-elliptic-review-001`), 20 (`v14-rc-hilbert-class-primes-review-001`, `v14-rc-kummer-ext-review-001`), 26 (`v14-rc-sunit-kummer-review-001`), 32 (`v14-rc-kummer-ext-review-001`), part of 18 (`v14-rc-tame-cup-transfer-review-002`). Rows 4 and 6 have only an unreviewed author proposal in this batch (F22); no acceptance for rows 12, 17 or 21 appears in this batch. Each of those reviews says recursive closure of the original row is not certified.

### R4-F18. Gross–Zagier-type height formula (CST Thm 1.1) used at zero derivative without its specialization hypotheses recorded
- Path: `E/release-completion-017/v14-rc-five-elliptic-review-001/REVIEW.md` (author reports `v14-rc-five-elliptic-inputs-001/-002/REPORT.md`)
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: At manuscript 5277 the conductor-one height formula is applied when the Rankin derivative vanishes, to conclude zero canonical height. Packet 001 did not pin the CST primary source or state the specialization (trivial character primitive of conductor one; all level primes split in K so the theorem's first condition holds and the common-level/discriminant condition is vacuous; f(infinity)=O so the formula uses the unaveraged trace with nonzero Petersson norm and degree, with no division by another L-value). The existing CST profile was for a different fixed genus specialization.
- Kind: HYPOTHESIS or convention not checked
- Outcome: Reviewer requested completion; supplied in successor 002 and checked directly against CST printed 2524–2525. Accepted. Model construction, smooth lifting, formal-kernel identification, perfectness and exact local orthogonality remain incoming premises.

### R4-F19. Nekovar inverse-limit application lacked the topology identification
- Path: `E/release-completion-017/v14-nekovar-cochain-inputs-review-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: Applying Nekovar, Selmer Complexes Cor. 4.1.3 to get a unique continuous degree-one class from compatible finite-stage classes requires that the quotients by J(a,n)=(2^a,(1+t)^(2^n)-1) in R=Z_2[[t]][G] be cofinal with the maximal-ideal-adic filtration and that lim^1 H^0 vanish (finite H^0 at each stage, Mittag-Leffler). Version 001 did not contain this.
- Kind: GAP or missing justification
- Outcome: Added in author packet 002 (`TOPOLOGY-APPLICATION.json`) and accepted. Kato norm relation, construction of the classes and local conditions are not covered.

### R4-F20. RC operator/network and early-theta source roles cited statements instead of proofs, and mis-scoped source profiles
- Path: `E/release-completion-017/v14-rc-pending-resolution-review-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: Operator bindings (3013–3024, 3445–3458, 3135–3147, 3540–3556) previously pointed at proposition statements; they now cite the intermediate proofs at 16015–16519 and 17135–17335. Early-theta packet 003 corrects the "available" profiles to source scope. Substantive scope notes: Kato supplies rational subscript-zero H^2 divisibility away from two, and the two-adic application needs the published 1999 bridge with its stronger hypothesis; it does not give full H^2 without the local cone. Finite Chebotarev at 3360–3372 consumes an already compatible element and does not prove it exists.
- Kind: GAP or missing justification (role records), with HYPOTHESIS retained for the 2-adic Kato use
- Outcome: Four role replacements and fourteen occurrence bindings accepted. Prerequisites inside the cited proofs are not independently closed.

### R4-F21. Atkin–Lehner eigen-action record consumed its own conclusion
- Path: `E/release-completion-017/v14-atkin-newform-input-review-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: The source note's line 11 was recorded as a consumer supplying the eigen-action it depends on. The correct supplier is lines 7–11 (weight-two slash action equals pullback of f(z)dz; Atkin–Lehner 1970 Thm 3(iii) gives eigenvalue +/-1 for the exact-divisor operator of determinant q^alpha, including q=2 and higher prime powers; plus the separately supplied pi*omega = c 2 pi i f(z)dz). No eigenvalue formula, root-number relation or twist formula follows.
- Kind: GAP or missing justification (circular supplier record)
- Outcome: Self-consumer removed in author packet 002; accepted for the two named inputs. Newness, trivial character, differential identity, cusp permutation and local norm/orientation identities remain required inputs.

### R4-F22. Unreviewed author proposals carrying open obligations
- Paths: `E/release-completion-017/v14-odd-theta-off-filter-role-repair-001/REPORT.md`; `E/release-completion-017/v14-global-published-source-replacements-author-001/REPORT.md`
- Author / date: `/root/v14_h6_coverage`; `/root/v14_arithmetic_review` (as author); not stated
- Point: (a) Odd-theta/off-filter role repair for RC rows 4 and 6 is an author proposal only; one replacement is "copied verbatim" from another agent's unreviewed repair. It states that the geometric/CM source applications, global Atkin correspondence, support/character compatibility and lambda invariance are not discharged, and that the general split-cubic doubling criterion remains a named prerequisite. (b) Class-field sources are replaced by Cox (first edition 1989, second printing, with errata: p.146 congruence subgroup read as P_{K,Z}(f), p.163 inclusion argument corrected). ACTIVE-BETA-LOCAL-NORM is explicitly not replaced: its local norm/reciprocity compatibility still lacks an eligible published source. The ideal-class/finite-idelic identification, nested-order kernel calculation and S-unit valuation argument are local bridges needing review.
- Kind: LIMITATION (awaiting independent review; one input without eligible source)
- Outcome: Not stated in this batch; no review of either packet appears here.

### R4-F23. Finite Heegner/Kummer producers at 2: no defect found, but conditional on a separate compatibility producer; Howard's theorem not usable
- Path: `E/release-completion-017/work/astra-final-finite-arithmetic-audit-001/REPORT.md`
- Reviewer / date: agent not named in file (path indicates "astra"); 4 November 2026
- Point: Independent reconstruction of producers A1–A3 for the non-CM pole curves E_l: y^2=x(x-l)(x+3l) found no missing finite implication and no hidden finite-Sha assumption, with a single integer L=C_cusp*C_bad*2^(2e) fixed before K, conductors, derivative set and precision vary. Limits stated: (i) the construction is conditional on compatibility of the finite character and Frobenius choices, supplied by a separate producer, with no Chebotarev for arbitrary independent prescriptions; (ii) A4 (moving-character existence), A9 (bounded-model and two-limit theorems), the determinant inequality and the restricted converse are not proved; (iii) uniformity as l varies is not asserted; (iv) Howard's global theorem and unique descent "require hypotheses not valid here" and are not used; his congruence (13) is extended to arbitrary old conductor by an explicit local supersingular-reduction argument; (v) the raw source's CM scalar input is not the source for the non-CM case and is replaced by Serre's open-image theorem (pp.259–260) via a scalar element argument giving exponent 2^e for E(H_c)[2^infinity].
- Kind: LIMITATION (and HYPOTHESIS: cited theorem's hypotheses fail, replaced by direct argument)
- Outcome: No manuscript correction requested.

### R4-F24. Picard quotient J_1(N) -> A: accepted, but standard inputs are implicit in the manuscript and scope is narrow
- Path: `E/release-completion-017/picard-quotient-fresh-review-001/REVIEW.md`
- Reviewer / date: `/root/astra_picard_independent_001`, not stated
- Point: The surjective Q-homomorphism J_1(N) -> A (combined005 1976–2000) is accepted, with representability of Pic^0 without a rational basepoint and the algebraic Abel map supplied in the review as explicit inputs that are only implicit in the manuscript's norm construction. Silverman's 2022 erratum warns his divisor/Picard classes are geometric, so raw Q-line-bundle classes are not identified with Q-points of the Jacobian. Not accepted: the C.16.4/newform/Hecke parts of the author contract, the rest of the forward-rank lemma including 2008–2010, Kato's finiteness conclusion. Fresh retrieval of Silverman errata timed out; held versions were used.
- Kind: LIMITATION
- Outcome: "No substantive repair is needed"; rest left to other reviews.

### R4-F25. Witness-reduction source record carried unrelated uniformity text
- Path: `E/release-completion-017/v14-rc-witness-reduction-review-001/REVIEW.md`
- Reviewer / date: `/root/v14_arithmetic_review`, not stated
- Point: Packet 001 for the finite-field specialization of the fixed-witness Kummer cocycle (manuscript 3357–3373) inherited an unrelated "finite-generation uniformity" statement; the application is for one chosen point at one chosen place ("one may not replace this by an unrelated residue place or a bound for all points").
- Kind: OVERSTATED claim (in the source record)
- Outcome: Removed in successor 002 (which also fixes a page number and bibliography). Accepted; no characteristic-zero-only Kummer assertion is applied to the finite field.


## Internal reviews, batch 5

Notes: several files are author reports/proposals rather than independent reviews; they are marked as such. "ERROR (source)" means an error in a cited published/author-version source, as opposed to an error in the project's own argument. Dates are given only where the file states one.


### R5-F1. Unary theta / Chebotarev audit: what it does not cover
- Path: research/version14/evidence/release-completion-017/work/astra-unary-chebotarev-001/REPORT.md
- Reviewer/date: not named in file (directory "astra-unary-chebotarev-001"); no date.
- Point: The audit derives the unary theta statement (F_lambda in S_{3/2}(Gamma_0(4C^2), lambda chi_{-4}), Theta_J at level 4C^2 J, cuspidal, imprimitive lambda allowed) and the finite-Chebotarev trace approximations itself, and found "no new mathematical correction". It explicitly does not construct the affine Kummer element producing the moving theta stage (current03:315-325), does not re-prove existence/local compatibility of the modular Galois representations, and does not re-check minimum-depth, graph-program or Selmer arguments. No original Shimura proof of the unary statement was read; the cap R >= 2 at current08:342-348 "remains essential".
- Kind: LIMITATION
- Next: Kummer element left to "the independent Kummer audit"; Galois-representation input left to the sealed T3 Carayol/Casselman pass. A source note (Weil I.19-20, Ramsey (1.1), Serre 2.1 Thm 1, joint finite quotient) is suggested, not required.

### R5-F2. Hu-Tan type criterion gives inertia only, not the full Weil-Deligne parameter
- Path: research/version14/evidence/research-additions-005/o2_review/REVIEW.md
- Reviewer/date: /root/astra_quartic_opt05_anchor, 2026-11-08.
- Point: Hu-Tan p.1384 type criterion (for infinite-dimensional smooth absolutely irreducible representations) detects only the inertia representation; it "does not itself state the stronger full-parameter conclusion" needed for the O2 transfer. Also unitarity of the Weil parameter cannot be inferred from unitarity of the Galois character (the cyclotomic character is a counterexample); "older compressed wording" did this.
- Kind: GAP
- Next: Repaired inside the reviewed proof (compiler004 Section 3: two parameters with same inertia differ by an unramified character; explicit Newton/Hodge admissibility argument forces v5(nu(Frob))=0). Accepted.

### R5-F3. O2 transfer: absolute irreducibility and twist conventions that must be explicit
- Path: research/version14/evidence/research-additions-005/o2_review/REVIEW.md
- Reviewer/date: /root/astra_quartic_opt05_anchor, 2026-11-08.
- Point: The argument needs absolute irreducibility of the WD parameter over an algebraic closure ("irreducibility only over a nonsplitting coefficient field would not suffice"); the reviewer checked the final freeze rather than the earlier draft for this (line 7). In Emerton Thm 7.4.2, E(n) acts on both Galois and adelic sides, so both the algebraic det^n and the smooth |.|^n factor are required (omitting the smooth factor gives a different local parameter); Emerton's printed weight convention and the Paskunas/Colmez label must be converted (k=v-u+1, n=-u), not copied.
- Kind: HYPOTHESIS or convention
- Next: Confirmed present in the frozen proof; no repair requested.

### R5-F4. O2: Saito's p-place proof not read
- Path: research/version14/evidence/research-additions-005/o2_review/REVIEW.md
- Reviewer/date: /root/astra_quartic_opt05_anchor, 2026-11-08.
- Point: Emerton 2006 Thm 2.3.1 is used as the direct supplier of p-adic local-global compatibility; p.295 attributes the p-place proof to Saito. The reviewer has "not read or certified Saito's missing final proof"; Henniart likewise remains an unaudited ancestor. General-type BM/HT, RED's Dospinescu qualification, corrected Kisin inputs, other residual branches are outside O2.
- Kind: LIMITATION
- Next: Left as retained transitive inputs.

### R5-F5. Thorne 2015 Prop 3.15(1) is false as stated (Allen-Newton-Thorne 2020 correction)
- Path: research/version14/evidence/research-additions-005/pan_author/REPORT.md
- Reviewer/date: author proposal (not independently accepted in this file), 8 November 2026.
- Point: ANT, Compositio 156 (2020), Section 3.1 corrects Thorne 2015 Prop 3.15(1): the special fiber of the unreduced trivial-character local lifting ring need not be generically reduced (also in dimension two); generic reducedness holds only after nilreduction, with consequent changes to Thorne 3.17 and 3.40(2). Pan's Lemma 4.2.10 / Prop 4.2.4 import Thorne 2015. Because Pan (p.47) passes to reductions for trivial xi_v and uses Taylor 2008 componentwise (precise locator Lemma 3.2(1) plus Lemma 2.7, not "first part of Prop 3.1" as Pan writes), the correction "does not on its own establish a failure of Pan's argument".
- Kind: ERROR (source)
- Next: Author packet PROOF.md supplies determinant-cover and nilpotent-quotient connections; independent review requested. The later rollup (qualification_rollup/REPORT.md) describes the local supplement as "independently accepted"; incorporation into the manuscript still only proposed at that snapshot.

### R5-F6. Pan Lemma 4.2.10(2): O-flatness of the nontrivial-character lifting ring not supplied by its cited source
- Path: research/version14/evidence/research-additions-005/pan_author/REPORT.md
- Reviewer/date: author proposal, 8 November 2026.
- Point: Pan 4.2.10(2) asserts O-flatness of the actual nontrivial-xi_v lifting ring citing Thorne 3.15/3.16. Thorne 3.15(2) gives irreducibility, dimension, a characteristic-zero generic point and generic-fiber smoothness; 3.16 gives connectedness. "Those statements alone do not imply O-flatness of an unreduced ring."
- Kind: GAP
- Next: New elementary rank-one determinantal matrix proof for the fixed-determinant ring in PROOF.md Section 4 (uses 2 invertible, p=5); flagged as needing independent review in this file; rollup later calls it independently accepted.

### R5-F7. Pan route: branches and editions not audited
- Path: research/version14/evidence/research-additions-005/pan_author/REPORT.md
- Reviewer/date: author proposal, 8 November 2026.
- Point: The residual-nontrivial branch (Pan p.46, Shotton descriptions) "has not been independently re-audited"; Thorne 2015 was read only in the 16 April 2014 author version (AMS final returned 403), Pan only in arXiv v2; Thorne Lemmas 1.3, 1.5, 1.6 (completed tensor products, completion/localization) imports are untouched by the correction and unverified. The manuscript still invokes Pan at lines 830-863 and 7393-7409.
- Kind: LIMITATION
- Next: Left open.

### R5-F8. Live modularity route still rests on five unverified final-source families
- Path: research/version14/evidence/research-additions-005/qualification_rollup/REPORT.md
- Reviewer/date: authored rollup (author not named), bound to manuscript 63db4260; no date.
- Point: Remaining acquisition/comparison queue for the live route: final Pan proof; final Buzzard initial-model theorem and its 2002 corrections; final Kollar singular-cubic theorem; final Kisin 2-adic / Khare-Wintenberger residual-modularity path; final Thorne 2015 local-ring/completed-tensor inputs. Characteristic-zero irreducibility and coefficient prime five "neither choose a residual branch nor remove the auxiliary two-adic step in the Serre route". The list is bounded, "not a claim that the whole manuscript inventory has no other source qualifications".
- Kind: LIMITATION
- Next: Left open; classification itself needs independent inventory review.

### R5-F9. Breuil-Mezard cites the wrong lemma of Paskunas "Image" for the principal-series locally algebraic formula
- Path: research/version14/evidence/research-additions-005/red_context/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler (also the connection author), 2026-11-08.
- Point: BM author p.24 cites `[53, Lem.11.5]` in the reducible case (a) of Prop 4.9(ii)/4.14. In the final Image paper Lemma 11.5 (p.170) is a Galois Hom statement and does not give the formula; the applicable statements are final Lemma 12.5 (pp.174-175) and, for the Steinberg quotient, Lemma 12.6 (p.175), both preceding and independent of Thm 12.7.
- Kind: ERROR (source citation)
- Next: Correction accepted in this review (Section 8); creates no new assumption.

### R5-F10. Paskunas Image Thm 12.7 depends on the disputed Emerton 2011 supercuspidal input
- Path: research/version14/evidence/research-additions-005/red_context/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler, 2026-11-08.
- Point: Final Image Thm 12.7 (pp.175-176) "explicitly calls the disputed Emerton input in its supercuspidal case" (Emerton 2011 Thm 3.3.22, also cited in the irreducible paragraph of BM 4.14). It "must not be imported wholesale as a shortcut". Only the supercuspidal part of that input is replaced, by the conditional arbitrary-target formula Pi^lalg = pi_sm(V) tensor Sym^(h2-h1-1) tensor det^h1.
- Kind: GAP
- Next: Conditional repair via the restricted CEGGPS auxiliary route; the global transfer (CEGGPS 7.4 at minimal conductor, fixed-conductor type lift, classical local-global compatibility at 5, Colmez VI.6.42) remained conditional here (subsequently reviewed in o2_review).

### R5-F11. Hu-Tan Thm 4.10: flat base change is not available
- Path: research/version14/evidence/research-additions-005/red_context/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler, 2026-11-08.
- Point: Hu-Tan Remark 4.8 says N2 is not flat over R^ps. "Replacing that proof by flat base change is invalid"; the Cohen-Macaulay statement must come from the original K-projective module and regular-sequence argument. Likewise BM 4.14-4.16 exceptional crystalline clauses (weight gap one, scalar type) cannot be removed by the new supercuspidal formula, and the full-type proof may not be replaced by the auxiliary crystalline locus.
- Kind: ERROR (rejected shortcut)
- Next: Original HT/BM proofs retained as imports; not re-proved.

### R5-F12. Hu-Tan application: what is not accepted
- Path: research/version14/evidence/research-additions-005/red_context/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler, 2026-11-08.
- Point: Reviewer authored the RED bridge and compiler001's minimal-local specialization, so neither is approved here. Dospinescu's final Compositio text was not obtained (only publisher metadata/abstract); the source obligation is "not closed". Hu-Tan applies only on the branch with residual restriction to G_Q(zeta5) absolutely irreducible; the cyclotomic-reducible (Kalyanswamy/Thorne) and residually reducible (Pan/Skinner-Wiles) branches are separate, and "characteristic-zero irreducibility proves neither residual condition". The manuscript (63db lines 830-863, 7393-7409) still uses Pan/Calegari.
- Kind: LIMITATION
- Next: Five-item open-input list (Section 7); RED bridge later accepted in red_review; local assembly later accepted in retained_local_review.

### R5-F13. RED bridge accepted only against Dospinescu's author version
- Path: research/version14/evidence/research-additions-005/red_review/REVIEW.md
- Reviewer/date: /root/astra_quartic_opt05_anchor, 2026-11-08.
- Point: The bridge (exactness on locally algebraic vectors implies density of X_lalg, hence BM Def 4.17 subspace lies in Dospinescu's Ext_alg, dimension <= 1 in the supercuspidal case) is accepted. Dospinescu Remark 1.6 records that the converse (density implies exactness) had an incorrect proof in the reducible-algebraic case; the bridge does not use it. Not established: equality of the author PDF (extalg1.pdf) with the final Compositio edition, all of Thm 1.3, BM final Duke comparison; the theorem requires p >= 5, fixed central character, fixed determinant over E[eps]/eps^2, and a supersingular Banach representation.
- Kind: LIMITATION
- Next: Accepted with those conditions; final-edition comparisons left open.

### R5-F14. Reclassifying CEGGPS Prop 2.9 as "comparison" is direct-use only
- Path: research/version14/evidence/research-additions-005/retained_delta_review/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_gaussian; no date.
- Point: The R13 change treats CEGGPS 2.9 (eta(T)=5^(a+b)t, eta(S)=5^(2a+b-1)d) as derived locally. But retained 4.30 uses 2.13, whose first proof route invokes 2.8 and 2.9 (alternative: 2.12 plus Hecke/deformation comparison); so 2.9 remains in the ancestor path and "no blanket theorem retirement is accepted". Similarly the bare 6.19 Galois-image statement cannot replace the Banach classification/functor input.
- Kind: OVERSTATED claim (guarded against)
- Next: Delta accepted with that restriction; all eighteen retained inputs remain.

### R5-F15. Restricted CEGGPS local theorem: residue field must be finite over E
- Path: research/version14/evidence/research-additions-005/retained_local_review/REVIEW.md
- Reviewer/date: /root/astra_quartic_opt05_anchor, 2026-11-08.
- Point: The first version (consolidated001) omitted the requirement that the residue field of the point be finite over E in the statement and card C09 ("a real object-description correction"). Four other recorded findings were phase/source mis-assignments (C05->R08, C06->R02, C07->R12, R14 split into three directed phases). C10 is accepted only as a conditional interface: the global/classical premises and arbitrary-target application are not discharged.
- Kind: HYPOTHESIS or convention
- Next: Repaired in consolidated003 (only normalized proof-text change); accepted.

### R5-F16. Ribet replacement: descent claimed for coarse points only
- Path: research/version14/evidence/source-incorporation-004/ribet-review/REVIEW.md
- Reviewer/date: /root, 2026-11-08.
- Point: Ribet Remark 3.5(b)'s Frobenius involution shows a supersingular point of the coarse X0(N) over F_q is F_(q^2)-valued; it does not show labelled moduli objects descend or that each supersingular curve has a scalar-Frobenius model. Two downstream manuscript sentences did not say "coarse points" and could be read as the stronger descent claim.
- Kind: OVERSTATED claim
- Next: Reviewer requested the change; author made it in successor002; accepted (metadata successor003).

### R5-F17. Ribet transporter direction must be fixed
- Path: research/version14/evidence/source-incorporation-004/ribet-review/REVIEW.md
- Reviewer/date: /root, 2026-11-08.
- Point: The transporter printed on Ribet p.440 cannot be copied without fixing direction; the application uses the right-Hom convention of Remark 3.5(a) (Hom(E0,E) = z R_hat, left order B ∩ z R_hat z^-1). "Reversing z without also changing the left-order formula would change the application." The ideal-isogeny construction remains a separate premise; the q-component is the Dieudonne-module convention, not a rank-two etale Tate module.
- Kind: HYPOTHESIS or convention
- Next: Explanation added in successor002 at reviewer's request; accepted.

### R5-F18. Voight quaternion-algebra source: misprint and erratum checked
- Path: research/version14/evidence/source-incorporation-005/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler, 2026-11-08.
- Point: In the final Springer text, the printed proof of Prop 13.3.4 / Thm 13.3.11 "occasionally writes w=v(nrd), omitting the factor 1/2"; the official errata add a division-algebra hypothesis to Cor 7.7.11. Only the nonnegativity test is used from the proof and the normalization w=v_q(nrd)/2, w(j)=1/2 is retained; 7.7.11 is not used.
- Kind: ERROR (source; not consumed)
- Next: No effect on the accepted conductor-one assembly. Retained and not re-accepted: genus/norm character, local Schwartz functions, theta modularity, rational parametrization, Atkin-Lehner eigenvalues, lambda_M, visibility witness, nonvanishing/index conclusions.

### R5-F19. Baba-Granath's printed polarization form is 6E, not principal
- Path: research/version14/proofs/a001-moduli-current-v1/reviews/INDEPENDENT-REVIEW.md
- Reviewer/date: Gaussian (/root/astra_v14_baseline_gaussian), 2026-11-08.
- Point: In B=(2,-3) with mu^2=-6 the reviewer recomputed the alternating form E with determinant 1. "The printed BG form is 6E, with determinant 1296. This is a genuine discrepancy in that construction display": 6E preserves the Rosati involution but not the polarization degree, so it cannot be fed to BG 2.1 as a principal polarization.
- Kind: ERROR (source)
- Next: The wrapper uses E itself as the principal object; accepted. "Not an unannounced correction to every polarization in that article."

### R5-F20. Baba-Granath Lemma 3.1: z3 printed where z2 is meant
- Path: research/version14/proofs/a001-moduli-current-v1/reviews/INDEPENDENT-REVIEW.md
- Reviewer/date: Gaussian, 2026-11-08.
- Point: The last paragraph of BG Lemma 3.1 supposes z2 and z6 conjugate on V3; the contradiction with distinctness of marks works only if the two printed z3 labels are read as z2.
- Kind: ERROR (source)
- Next: Already repaired in the earlier independent BABA-GRANATH-FINAL-DISPOSITION.md, reused at its bound version.

### R5-F21. A001 moduli review: disputed and unreviewed parts
- Path: research/version14/proofs/a001-moduli-current-v1/reviews/INDEPENDENT-REVIEW.md
- Reviewer/date: Gaussian, 2026-11-08.
- Point: A "new degree-four adverse finding remains separately recorded" (the "disputed degree-four isogeny"; the third mark's CM order Z[sqrt(-6)], disc -24, is instead obtained from the fixed quaternion representative mu). BG 3.7/3.8 product isomorphisms, 3.9 numerical orientation argument and 3.10 conic map have findings in the history and are not consumed. Not approved here: the explicit weighted Igusa tuple (current 856-861), the invariant/height calculation (1206-1239), the B11 full-level index, integral models, descent and the degree-324 bound. A coarse P1 "supplies no universal abelian scheme by itself".
- Kind: LIMITATION
- Next: Left to separate applications; Lin-Yang Example 30 normalization has its own Compiler decision.

### R5-F22. CM reciprocity: Frobenius convention deliberately not identified
- Path: research/version14/proofs/cj-cm-inputs-v1/REVIEW.md (same point in source-incorporation-005/REVIEW.md)
- Reviewer/date: /root/astra_v14_baseline_compiler; no date in this file.
- Point: The reciprocity formula uses Silverman's printed Frobenius convention (C.11.4); its identification with arithmetic Frobenius rests only on Milne author notes (v4.03 pp.7, 20) and "remains unclaimed". The consumer is unaffected only because the class character is quadratic (chi(a^-1)=chi(a)) and one global inversion is applied to source and target together; per-class inversion or change of reduction place is not permitted. Also: equality of j alone does not give O-linearity or preservation of the level subgroup; that needs III.1.4(b) plus faithfulness of the tangent scalar (VI.4.1).
- Kind: HYPOTHESIS or convention
- Next: Accepted as inversion-invariant; convention left unresolved. Reviewer had requested pre-freeze separation of the two conventions and explicit III.1.4(b),(c) locators.

### R5-F23. DDT Theorem 2.17(c) at real places needs Tate H^0
- Path: research/version14/proofs/general-field-tw-v1/reviews/ddt-final-source-review-compiler-001/REVIEW.md (author statement in sources/ddt/REPORT.md)
- Reviewer/date: /root/astra_v14_baseline_compiler; no date.
- Point: The degree-zero local pairing in DDT Thm 2.17(c) at a real place "cannot be read as a perfect pairing on unrestricted ordinary H0"; it requires Tate H^0 (norm correction (1+c)M in the proof of 2.18). The consumer uses only the perfect ordinary H^1 pairing and the final ratio of Thm 2.19 (ordinary H^0); neither H^1(R,M)=0 for 2-primary M nor a Tate-H^0 denominator may be assumed. The odd-prime hypothesis printed after 2.19 belongs to Section 2.4, not to 2.19.
- Kind: HYPOTHESIS or convention
- Next: Confirmed respected; DDT-FINAL-GENERAL-SELMER accepted for M = End_k(k^2), k, Z/2^j.

### R5-F24. General-field Taylor-Wiles, line 46: restriction-kernel argument used the wrong group
- Path: research/version14/proofs/general-field-tw-v1/reviews/kwii-general-field-tw-review-compiler-001/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler; no date.
- Point: In the draft, the restriction-kernel argument "used G_K where its disjointness argument controlled G_(K F_j)": vanishing on all of G_K was not supported; the class lands in H^1(K F_j/F, A) = inflated H^1(F_j/F, Z), giving the two-dimensional scalar kernel.
- Kind: ERROR
- Next: Author corrected before freeze (theta-001 line 46); excluded from this reviewer's decision; independently accepted in kwii-two-corrections-review-gaussian-001.

### R5-F25. General-field Taylor-Wiles, line 50: additive cocycle image treated as a k-vector space
- Path: research/version14/proofs/general-field-tw-v1/reviews/kwii-general-field-tw-review-compiler-001/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler; no date.
- Point: The image I of c on G_(K T_j) is only an F_2-subspace of A=End_k(k^2); the finite-group premise (KW II Lemma 4.3 submodule list) applies to W=span_k(I), not to I. Corrected argument: Z ⊂ W, Z not in (g-1)A, (g-1)A is k-linear, hence I is not contained in (g-1)A.
- Kind: ERROR
- Next: Corrected before freeze; independently accepted by Gaussian (two-corrections review).

### R5-F26. General-number-field Selmer-size formula was available only from an author version
- Path: research/version14/proofs/general-field-tw-v1/reviews/kwii-general-field-tw-review-compiler-001/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler; no date.
- Point: Input U02 (Selmer ratio over a totally real F possibly ramified at 2, 2-primary modules, real places) was recorded only via DDT's university-hosted author text; the reviewer refuses to "infer the general formula merely by removing the standing field hypothesis of KW II Section 4", and notes the odd-p argument of KW II p.544 is not extended. NSW e-edition 8.7.9 read as corroboration only. Acceptance is conditional on U01-U05.
- Kind: GAP
- Next: Closed by final DDT 1995 Thm 2.19 (sources/ddt/REPORT.md, accepted in ddt-final-source-review-compiler-001); U01, U03-U05 accepted in tw-source-table-review-root-001.

### R5-F27. General-field Taylor-Wiles, line 50: residual matrix not literally unchanged
- Path: research/version14/proofs/general-field-tw-v1/reviews/kwii-two-corrections-review-gaussian-001/REVIEW.md (accepted in kwii-scalar-correction-review-root-001/REVIEW.md)
- Reviewer/date: /root/astra_v14_baseline_gaussian (found); /root (accepted); no dates.
- Point: K is cut out by A=ad(r), not r, so tau in G_(K T_j) has r(tau)=lambda I with lambda possibly != 1. The sentence that multiplying by tau "leaves the residual matrix unchanged" is "not justified as written".
- Kind: ERROR
- Next: Repaired in theta-003: replace tau by tau^e, e = order of lambda, odd since char k = 2; then r(tau^e)=I and c(tau^e)=e c(tau)=c(tau). Accepted by /root.

### R5-F28. Finiteness of Theta_Q: no published ray-class theorem was cited
- Path: research/version14/proofs/general-field-tw-v1/reviews/tw-source-table-review-root-001/REVIEW.md (supplement: sources/ray/REPORT.md)
- Reviewer/date: /root; searches dated November 8, 2026.
- Point: For theta003 Section 6 line 90 (finiteness of the maximal abelian pro-2 extension unramified outside Q and split at S) "the original table named ray-class finiteness without an exact published theorem". Global reciprocity alone does not give it.
- Kind: GAP
- Next: Closed by Kopp-Lagarias, Essential Number Theory 4 (2025), Thm 6.9 with Defs 5.2-5.4, plus the common-modulus argument (m = product of Q, Sigma empty, principal units pro-odd); accepted. The ray report warns the related signed-modulus (AC character) use is not approved: an arbitrary unitary Hecke character need not have finite order.

### R5-F29. Milne ADT p.31 introductory sentence is wrong as printed
- Path: research/version14/proofs/general-field-tw-v1/reviews/tw-source-table-review-root-001/REVIEW.md
- Reviewer/date: /root; November 8, 2026.
- Point: Milne (2nd ed. 2006) p.31 says the local cohomology groups vanish "for r >= 2"; this "cannot be used as written" since the next Euler formula retains H^2 and Cor I.2.3 gives its possibly nonzero dual. The application uses I.2.3, I.2.6 and Lemma I.2.9 (h1-h0=h2=2 at odd auxiliary places) and never H^2=0. Also confirmed: End_k(k^2) = scalars ⊕ trace-zero cannot be used in characteristic 2.
- Kind: ERROR (source; not consumed)
- Next: Recorded, not imported; U04 accepted.

### R5-F30. Khare base cases: solvable-image branch ramified at P not covered
- Path: research/version14/proofs/khare-connections-v1/reviews/base/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_gaussian; no date.
- Point: The accepted applications (KW Thm 5.4 excludes S-type N=1, k=2,4,6; Thm 5.2(i) excludes N=1, k=2 for the FIRST reduction unramified at P) do not dispose of "an absolutely irreducible solvable-image representation ramified at P"; its classical residual-modularity input is separate. The weight-2 conclusion for T/varpi T (including l=3) comes from criterion17, not from early KW Prop 3.2 (which concerns HT(0,p)). Twisting, the nonsolvable branch, second family, RETURN and induction are not closed.
- Kind: LIMITATION
- Next: Left open.

### R5-F31. Khare author text cites Lemma 5.1(i) where only 5.1(ii) applies
- Path: research/version14/proofs/khare-connections-v1/reviews/dihedral/REVIEW.md
- Reviewer/date: /root/astra_v14_baseline_compiler, 2026-11-08.
- Point: Khare author p.26 calls its FIRST weight argument "Lemma 5.1(i)" while using the numerical conclusion of 5.1(ii). FIRST members may be ramified at a second prime (7, 11, 19, 29, 31), so the strict-level-one hypothesis of (i) is not available; only the small-weight result (cyclotomic-induced, k <= p+1 forces k=(p+3)/2, so weight 2 is locally reducible) applies. Strict level one (k=(p+1)/2, p ≡ 3 mod 4) is used only for RETURN callers.
- Kind: ERROR (source citation / hypothesis mismatch)
- Next: The replacement's fourteen-caller partition supplies the correct statement per caller; accepted. Not accepted: Khare 5.3, 5.4/Cor 5.5, class-number existence assertion, solvable-image modularity, final Khare edition.

### R5-F32. Finite-flat weight-2 criterion was only available for prime-field coefficients
- Path: research/version14/proofs/khare-connections-v1/reviews/finiteflat/REVIEW.md
- Reviewer/date: /root, 2026-11-08.
- Point: Serre Prop 4 is worded for prime-field coefficients; the Khare second-family construction needs Serre weight 2 for T/varpi T over an arbitrary finite residue field k (implication R15-WEIGHT), including the wild peu-ramifie case with elementary abelian wild group of rank [k:F_p] and l=3. SourceReview had identified this "earlier coefficient scope problem".
- Kind: GAP
- Next: Repaired by khare-finiteflat-coefficients-17 (Raynaud 3.3.3/3.3.6/3.4.4 with e=1<p-1, etale-torsor splitting argument, coordinatewise Kummer classes, Serre pp.186-187); accepted, and its selection by khare-second-family-15/finiteflat-successor-002 checked. Complete second-family construction not accepted.


## Internal reviews, batch 6

Path prefixes used below:
- `KC/` = `research/version14/proofs/khare-connections-v1/reviews/`
- `GI/` = `research/version14/proofs/local-gi-v1/proof/`
- `V14/` = `research/version14/proofs/`

"Not stated" for reviewer or date means the review text does not give it. "ERROR" includes errors the reviewers located in published sources that the manuscript's route had been relying on or had to avoid; each entry says which.


### R6-F1. Initial weight-two pair: discriminant-one input and Khare ancestry not closed
- Path: `KC/first-pair/REVIEW.md`
- Reviewer / date: /root/astra_v14_baseline_compiler (author: astra_quartic_opt05_anchor); date not stated
- Point: Triviality of the everywhere-unramified determinant character uses the "discriminant-one" theorem (no nontrivial everywhere-unramified extension of Q), which has no certified published locator in the packet. KWII pp. 550-552 and 583 themselves cite Khare/Taylor (p. 583 cites Khare to pass from the Brauer virtual expression to actual representations); the reviewer explicitly does not infer that step from equality of virtual dimensions. The construction gives a suitable pair, not an extension of an arbitrary preselected lift.
- Kind: LIMITATION
- Next: Left open as retained inputs; "requires its own source disposition". No defect in the two scoped connections.

### R6-F2. Link-back: only two of nine Khare caller obligations discharged
- Path: `KC/linkback/REVIEW.md`
- Reviewer / date: not named (states prior source-location role); date not stated
- Point: KC-FIRST-LIFTING and KC-LINK-BACK are accepted only as conditional implications; KC-NORMALIZE, KC-INITIAL-LIFT, KC-INITIAL-SYSTEM, KC-TYPE-CHANGE, KC-RETURN-SYSTEM, KC-RETURN-WEIGHT, KC-RESIDUAL-MODULARITY are not supplied. Early KW Theorems 3.3 and 4.2(i) do not replace the weight-two/type-changing constructions, and treating residual modularity in the surviving branch as known would be circular. Khare p. 24's broad "6.11/6.12" reference does not by itself establish which Savitt case is used; Section 4 tail was replaced for source precision (principal-series: BM Prop 6.1.1 + Savitt Thm 6.11). Khare is the author version, not the final Duke text.
- Kind: LIMITATION
- Next: Remaining obligations taken up in later packets (normalization18, construction14/15, selection19, RETURN); final-edition comparison left open.

### R6-F3. KC-NORMALIZE: endpoint k = P+1 lies outside Khare's printed Lemma 5.2
- Path: `KC/normalization/REVIEW.md`
- Reviewer / date: reviewer identified as "Arithmetic" in sibling reviews (author: /root); date not stated
- Point: The reviewer's source-first reconstruction "identified ... the k=P+1 issue": Khare's Lemma 5.2 covers k < P only, so the ordinary/tres-ramifie endpoint needs Serre's eqs. 2.4.8-2.4.9 (weight (alpha+1)(P+1) forces alpha=0, beta=1) and Remark 1 on p. 186 separately. The author's initial k=2 draft was "preserved, not accepted"; only the final even 8 <= k <= P+1 statement is bound. Modularity under inverse global twisting is an incoming interface, not proved here.
- Kind: GAP
- Next: Repaired in normalization18 (accepted, no further correction). Inverse-twist interface later supplied by the untwist packet (F19).

### R6-F4. Full DFG premotivic member: blanket appeal to semisimplicity unjustified
- Path: `KC/ordinary-two-connections/REVIEW.md`
- Reviewer / date: /root (author of completion002: astra_v14_baseline_theta; defect identified by compiler); date not stated
- Point: Final DFG (p. 669 definition, p. 684 footnote) gives L-admissibility via Frobenius-semisimple Weil-Deligne representations and no axiom that every Galois realization is semisimple; completion001's "blanket appeal to semisimplicity should not stand without an argument" when identifying the full object's member at the omitted coefficient place with rho-dual.
- Kind: GAP
- Next: Repaired in completion002 line 45 (Chebotarev + Brauer-Nesbitt, then a length-one argument using absolute irreducibility of rho); accepted. Saito 1997 antecedent of DFG's full-family assertion remains unchecked.

### R6-F5. Nebentype / duality normalization order in the ordinary and DFG branches
- Path: `KC/ordinary-two-connections/REVIEW.md` (same exclusion recorded in `KC/ordinary/REVIEW.md`)
- Reviewer / date: /root; date not stated
- Point: DFG eq. (18) uses geometric Frobenius with the inverse finite-character factor, so M_f "must not be equated with the naive dual of an arbitrarily normalized arithmetic realization while the finite character is nontrivial". The old text did not first prove the nebentype trivial.
- Kind: HYPOTHESIS or convention not checked
- Next: Repaired in completion002 line 47: ordinary branch computes det in arithmetic convention to get epsilon=1 before dualizing; DFG branch undoes twists by (22), uses (16) to force psi=1, then (18). Accepted. Compiler (who proposed both fixes) explicitly does not independently accept lines 45/47; /root does.

### R6-F6. Incorporation appendix: two explanations omitted in the initial draft
- Path: `KC/predecessor-incorporation/REVIEW.md`
- Reviewer / date: /root/astra_v14_baseline_theta (incorporation author: compiler); date not stated
- Point: The initial TeX appendix dropped two source14 explanations (KWI pp. 491-492 separate coefficient-prime clauses; KWII p. 529 endpoint argument: nonzero-monodromy semistable endpoint, fixed unramified gamma, valuation-coordinate argument forcing the residual unramified characters to agree). The review explicitly does not accept KC-NORMALIZE, auxiliary-prime/exponent choices, induction inequalities or any unproved residual-modularity premise; the appendix does not make the conditional constructions prove the Serre induction.
- Kind: GAP
- Next: Both restored before the target freeze; accepted as incorporation only.

### R6-F7. Prime-conductor corollary: trivial-nebentype argument must not be inherited
- Path: `KC/prime-level/REVIEW.md`
- Reviewer / date: /root/astra_v14_baseline_compiler; 2026-11-08
- Point: The reviewer required that the general-nebentype application (Khare Cor. 1.2) not reuse the earlier DFG trivial-nebentype normalization; also the earlier Kisin locator for the weight-(0,1)-crystalline-implies-BT step was incorrect (correct: corrected Lemma 2.3.8 proof, p. 1122, via Breuil).
- Kind: HYPOTHESIS or convention not checked
- Next: Author supplied a direct argument using Skinner (eq. (1) and Theorem 1, full Frobenius-semisimple WD with monodromy) for the same form with possibly nontrivial nebentype; accepted.

### R6-F8. Prime-conductor corollary: acyclicity of the dependency order not verified
- Path: `KC/prime-level/REVIEW.md`
- Reviewer / date: compiler; 2026-11-08
- Point: The corollary uses the upstream level-one theorem; the reviewer states that before adoption one must "separately verify the stated order level-one theorem -> this corollary -> later KW uses, with no cycle through this corollary in the upstream level-one proof". Early KW's own proof references to Khare (p=3 supersingular extension, local-ring details) are real dependencies, not bibliography.
- Kind: LIMITATION
- Next: Left open as an adoption obligation.

### R6-F9. RETURN: claim that the prescribed character has odd order is false
- Path: `KC/return-parity/REVIEW.md` (origin recorded in `KC/return/REVIEW.md`)
- Reviewer / date: /root (defect found by SourceReview; author: Arithmetic); date not stated
- Point: In Section 5 of the RETURN proof, the claim that the entire prescribed tame character omega_P^j has odd order, or that j is a multiple of t (P-1 = ell^r t), is "unnecessary and generally false". Correct statement: j is congruent to k-2 mod t (reduction mod ell kills exactly the ell-primary part), t is even, hence j is even and 2 <= j <= P-3. Only the quotient by the Teichmuller lift of the old residual character has ell-power order.
- Kind: ERROR in the mathematics
- Next: Repaired in the corrected Section 5; accepted by /root. Does not prove that the interval contains a suitable exponent or that the lift exists.

### R6-F10. RETURN: "integral valuations" misreads Savitt Prop. 2.17
- Path: `KC/return-parity/REVIEW.md`
- Reviewer / date: /root; date not stated
- Point: Savitt 2.17 requires x1, x2 in O_E with val_P(x1 x2) = 1; for ramified E/Q_P the normalized valuations are nonnegative, not integers. The original wording excluded the two-positive-slope (interior) case that Prop. 2.20 explicitly allows.
- Kind: ERROR in the mathematics
- Next: Corrected to "nonnegative" in Section 3; accepted. Reviewer does not re-prove the classification or the strongly divisible lattice calculations.

### R6-F11. Savitt source: no publisher facsimile; Cor. 6.15(1) wording differs; 6.12(4) was wrong as published
- Path: `KC/savitt-edition/REVIEW.md` (also `KC/return/REVIEW.md`, `KC/tame/REVIEW.md`)
- Reviewer / date: /root/astra_v14_baseline_gaussian; 2026-11-08
- Point: The text read is the author's 43-page reproduction (internal date Sept 2004), not the 57-page Duke typeset; equality is not established. Corollary 6.15(1) reads "unique then irreducible" in the linked original and "irreducible then unique" in corrected v3, a real proof-order change. Published Savitt Theorem 6.12(4) is wrong for i=1, val(b)>0 (original lattice has split reduction); Gee-Savitt Appendix A restricts (4) to i>1, adds (5), and amends 6.15(2), 6.21, 6.24. The reviewed consumers use only 6.9/6.11/6.15(1) (principal-series types, exponents divisible by P+1), and derive irreducibility from the inertia formula rather than from uniqueness.
- Kind: LIMITATION
- Next: Accepted as "author-authenticated reproduction of published text" for seven interfaces only. Not established that 6.12 is absent from every historical or current route.

### R6-F12. Second family: ordering of the inertia characters (chi,1) was asserted without proof
- Path: `KC/second-orientation/REVIEW.md` (identified in `KC/second-pair/REVIEW.md`)
- Reviewer / date: /root (author: anchor; defect found by SourceReview); 2026-11-08
- Point: KWI Theorem 5.1(3) (p. 492) needs inertia at P diagonal (chi,1); a basis starting with the inertia-fixed line gives (1,chi), and swapping is not automatic for a nonsplit extension. The base proof's line-17 paragraph claimed the ordering immediately.
- Kind: GAP or missing justification
- Next: Repaired in orientation-successor-001: for chi nontrivial the tame generator M has distinct eigenvalues, F M F^-1 = M^P = M, so both eigenlines are decomposition-stable (representation is diagonal); for chi trivial the fixed-line basis already works and the unipotent entry is retained. Accepted for that paragraph only.

### R6-F13. Second family: Serre's finite-flat weight criterion is stated only over F_l
- Path: `KC/second-pair/REVIEW.md`
- Reviewer / date: /root/astra_v14_source_review; date not stated
- Point: Final Serre p. 189 restricts the finite-flat formulation to GL2(F_l) and says the general case needs Raynaud's finite-field vector schemes; the construction applies it over a general finite coefficient field. The rank-q Proposition 3.3.2 alone must not be substituted for the general small-ramification full-faithfulness theorem. The weight-2 conclusion (and exclusion of the tres ramifie extension) is therefore conditional on retained input R15-WEIGHT.
- Kind: GAP or missing justification
- Next: Left conditional in this review ("a separate Raynaud/coefficient supplement is being authored"). `KC/predecessor-incorporation` later records it supplied by the source17 proof (Raynaud e=1, flat subquotients, Kummer coordinates), accepted by /root.

### R6-F14. Khare's W32 row: exponent j = 16 is invalid
- Path: `KC/selection/REVIEW.md` (propagation checked in `KC/predecessor002-incorporation/REVIEW.md`)
- Reviewer / date: /root/astra_v14_baseline_gaussian (author: /root, who found it); 2026-11-08
- Point: For k=32, P=31, ell=5: P-1 = 5*6, t=6, original exponent k-2 = 30. j=16 is not congruent to 30 mod 6; omega_31^16 has order 15 with nontrivial order-3 reduction in characteristic 5, so the prescribed type does not reduce to the old residual character. This is in Khare's author text p. 25 (final Duke text not checked).
- Kind: ERROR in the mathematics (in the inherited source table)
- Next: Replaced by j=18 (order 5, trivial reduction), returned weights 20 and 14, both <= 30. This is a different second family and "cannot be silently called the old selected second family". Propagated to TeX in successor002.

### R6-F15. Khare's prime-existence bound replaced by Nagura
- Path: `KC/selection/REVIEW.md`
- Reviewer / date: gaussian; 2026-11-08
- Point: The reviewer's source-first report records a "printed prime-counting-bound issue" in Khare's Chebyshev/Ellison argument (and an unrelated P29 caller-label slip). Selection19 instead uses Nagura's theorem (prime in (x, 6x/5) for x >= 25) twice, plus an argument that at most one of two consecutive Nagura primes is of the form 2^a+1, to get a non-Fermat P with B < P < 36B/25 and an odd prime-power divisor of P-1.
- Kind: ERROR in the mathematics (in the source; specifics not given in this review)
- Next: Replaced, accepted. "This decision does not repair or reapprove those historical statements." Nagura's analytic estimates not re-proved.

### R6-F16. Selection: corrected choices not yet transported to active records
- Path: `KC/selection/REVIEW.md`
- Reviewer / date: gaussian; 2026-11-08
- Point: Every active use stating j=16 / weights 18,16, and the GENERAL prime-choice input still citing Chebyshev/Ellison, must be superseded; the review "does not pretend that copied proof text has already updated those records or the manuscript". Propagating modularity to other coefficient primes still needs Corollary 5.5 or its replacement.
- Kind: LIMITATION
- Next: TeX propagation done in successor002 (`KC/predecessor002-incorporation`); record adoption left open.

### R6-F17. Tame ordinary connection: source cards overstated what Savitt proves
- Path: `KC/tame/REVIEW.md`
- Reviewer / date: Gaussian (author: Anchor); date not stated
- Point: Cards SAVITT-NONSCALAR-FILTERED and SAVITT-INTERIOR-REDUCTION attributed the explicit ordinary line/quotient to Savitt's classification; the source gives only the indecomposable filtered module (2.17/2.20) and the interior lattice reduction (6.11(3)). The ordinary quotient is a connecting deduction (PROOF section 4), "rather than a false quotation of the source's classification".
- Kind: OVERSTATED claim
- Next: Narrowed in record-successor-001 (twelve field replacements, proof unchanged); accepted.

### R6-F18. Tame ordinary connection: scalar type not covered
- Path: `KC/tame/REVIEW.md`
- Reviewer / date: Gaussian; date not stated
- Point: Scalar type (j=0, h=1) is outside Prop. 2.17's nonscalar hypothesis and "needs its own proof and decision". The six RETURN rows are checked only as a local conditional interface; their historical assertions on even residual weights, distinguishedness, global level and dihedral entry are not certified.
- Kind: LIMITATION
- Next: Left open here (other reviews say scalar cancellation uses the h=1 crystalline case of the local ordinary lemma).

### R6-F19. Cyclotomic untwist: trivial-exponent case must be separated
- Path: `KC/untwist/REVIEW.md`
- Reviewer / date: not named (author: Arithmetic; strategy: /root); date not stated
- Point: The opening draft stated the Gauss-translate construction for arbitrary exponent e; for e congruent to 0 mod P-1 the character eta is trivial (not conductor P) and the construction does not apply.
- Kind: GAP or missing justification
- Next: Final proof treats e=0 as the identity case before the Gauss construction; accepted. No optimal level/weight is produced.

### R6-F20. D/F packet: multivariable factorization used by E.11/E.13 was open
- Path: `GI/modules/05-gi-df/REPORT.md` (author report)
- Reviewer / date: author /root/astra_v14_baseline_compiler; date not stated
- Point: DF002 proves only one-variable D.3/D.4 and F.1; "the multivariable factorization consumed by E.11/E.13 is explicitly OPEN", and D.6 coset-integral / degree-rank horizontal-character application was still with Gaussian. The report also states it avoids "the defective general quadratic-extension claim" of the 2008 U3 paper.
- Kind: GAP or missing justification
- Next: Multifactor packet (`GI/modules/06-gi-multifactor`) supplies it; MF-AFFINE/MF-D4 accepted in F27-F28; MF-E11/E13 reviewed elsewhere (not in this batch).

### R6-F21. GTZ E.8-E.10: factorial omission and symmetry after an arbitrary test function
- Path: `GI/modules/11-gtz-lp05/REPORT.md` (author report)
- Reviewer / date: author compiler; date not stated
- Point: In the published multilinearization, the raw orbit is permutation-equivariant, but that "does not establish invariance after applying an arbitrary vertical test function"; and a factorial multiplier is omitted. The proposal symmetrizes by the symmetric tensor product of permuted values, normalized (nonzero since the symmetric algebra is a domain), which introduces a second d! factor; the input must be divided by (d!)^2 first (and by s for the (13.4) join).
- Kind: ERROR in the mathematics (published source step, repaired locally)
- Next: Repaired in the LP05 proposal; at the time of the report awaiting independent review. Limit transfer U03/U10 later accepted (`GI/reviews/v14-resume-lp05-transfer-review-001`).

### R6-F22. GTZ (13.14)-(13.17): wrong shift index and wrong constant
- Path: `GI/modules/11-gtz-lp05/REPORT.md`
- Reviewer / date: author compiler; date not stated
- Point: Printed pp. 1321-1322 repeat h_(s-2) where independent shifts h_j are required; with the index corrected the alternating sum gives (-1)^(s-2)(s-2)! on the multilinear diagonal, while (13.16) prints +s!. The final zero-symbol consequence can ignore an overall sign, "but that does not validate the printed exact identity".
- Kind: ERROR in the mathematics (published source)
- Next: Reported as an open Section 13 follow-up; superseded by the Section 13 proposal (F24), which records coefficient (-1)^(s-1) s! after a further slot correction.

### R6-F23. GTZ Theorem 7.4 hypothesis is stricter than what Theorem 7.1 supplies
- Path: `GI/modules/13-gi-section13/REPORT.md` (author report)
- Reviewer / date: author compiler; date not stated
- Point: Both printed statements of Theorem 7.4 (pp. 1271, 1315) assume correlation of degree strictly less than s-2, but Theorem 7.1 supplies degree at most s-2. The published theorem therefore cannot be invoked as stated at this interface.
- Kind: HYPOTHESIS or convention not checked
- Next: Section 13 proposal proves the shift and Cauchy-Schwarz chain directly under the weaker "at most s-2" hypothesis without invoking Theorem 7.4; independent review pending at time of report.

### R6-F24. GTZ Lemma 13.4 swaps the first two slots; sign of the leading term changes
- Path: `GI/modules/13-gi-section13/REPORT.md`
- Reviewer / date: author compiler; date not stated
- Point: Printed Lemma 13.4 swaps the first two slots relative to Lemma 13.3 and definition (13.10), so the actual alpha' has a negative s(s-1) antisymmetric leading term, and the independent-shift alternating cube has coefficient (-1)^(s-1) s!. The earlier LP05 review's (-1)^(s-2) s! was conditional on printed (13.13).
- Kind: ERROR in the mathematics (published source)
- Next: Corrected in the Section 13 proposal; earlier record preserved unchanged; independent review pending at time of report.

### R6-F25. Section 13: Prop 7.3 output loses lower factors; parameter box and cutoff
- Path: `GI/modules/13-gi-section13/REPORT.md`
- Reviewer / date: author compiler; date not stated
- Point: The weaker modified Proposition 7.3 output alone discards lower factors needed in the argument, so plain-correlation Proposition 8.4 must be the premise; the three Cauchy-Schwarz eliminations, the parameter substitution on its actual box I6 with a parameter-only cutoff, and the representation of the remainder beta (integer combination of multilinear words with at most s-3 copies of n, not merely an n-degree bound) had to be written out. E.11's positive-progression hypothesis is met only after partitioning signs and reflecting an orthant.
- Kind: GAP or missing justification
- Next: Supplied in the proposal; E.11/E.13, Prop 5.6 and Prop 8.4 imported, not reproved; independent review pending.

### R6-F26. Initial strong selection: scope and unchecked items
- Path: `GI/reviews/gi-initial-selection-review-astra-resume-001/REVIEW.md`
- Reviewer / date: /root/v14_gi_selection_review (author: /root); date not stated
- Point: Accepts only existence and limit selection of the initial Section 7 strong family for d=s-1>0. It is "unnecessary and unjustified to replace an arbitrary already-chosen weak nilcharacter or its symbol"; objects admitted by the literal standard-domain equivariance definition are not covered. Source hashes were not recomputed; the A.12 displayed tagged set was not visually inspected (the proof states the construction explicitly and applies A.11 directly); character countability relies on retained Mal'cev finite-generation input.
- Kind: LIMITATION
- Next: Accepted in scope; later constructors/selection sites reviewed separately.

### R6-F27. DF002 used GT12 Lemma 8.4 beyond its range (offsets of size O(N))
- Path: `GI/reviews/independent-gaussian-multifactor-001/REVIEW.md`
- Reviewer / date: /root/astra_v14_baseline_gaussian (author: compiler); date not stated
- Point: DF002 lines 132-145 transfer coefficient bounds along a dense progression with offset O(N) by an "inadequate full-height reading of GT12 Lemma 8.4". Required: an inverse-affine lemma in which offsets enter only integer numerators, one standard integer r clears denominators, and the coefficient of binom(n,alpha) is O(N^(|beta|-|alpha|)).
- Kind: GAP or missing justification
- Next: Replaced by MF-AFFINE (accepted, with the DF002 connection); valid only for integer offsets O(N) and bounded nonzero steps. MF-E11/E13, the rest of DF002 and the GI assembly are not accepted here.

### R6-F28. Published inputs that are false or misapplied in the GTZ equidistribution appendix
- Path: `GI/reviews/independent-gaussian-multifactor-001/REVIEW.md`
- Reviewer / date: gaussian; date not stated
- Point: (a) The GT14 erratum theorem is an obstruction theorem on an equal-sided cube, not total equidistribution on arbitrary rectangles ("the originally incorrect unequal-side theorem"); a dense rectangle must first be localized to an equal cube by a finite averaging argument. (b) Printed GTZ D.5 deletes rational Taylor terms; the reviewer calls this "D.5's false Taylor conclusion". (c) GTZ/GT12 A.12 has a left/right period problem (see F29).
- Kind: ERROR in the mathematics (published sources)
- Next: The MF proposal avoids all three: cube localization, minimum-dimension descent with one fixed p for all finite covers, common finite-index normal core, and a right-coset period proved directly. Accepted for lines 91-303.

### R6-F29. GT12 Lemma A.12: proof gives a left-difference period, not a right-coset period
- Path: `GI/reviews/independent-root-df-orientation-002/REVIEW.md`
- Reviewer / date: /root (author: compiler; found by sol_protocol_final_review); date not stated
- Point: A.12's displayed proof controls gamma(n+r) gamma(n)^-1; integrality of that does not give gamma(n+r)Gamma = gamma(n)Gamma for a nonnormal lattice. Heisenberg example: gamma(n) = (1/2, n, 0), r=1 has left difference (0,1,0) in the lattice but right difference (0,1,-1/2) outside it. DF001 used the invalid implication.
- Kind: ERROR in the mathematics
- Next: Repaired in DF002 lines 240-259: R(n,r) = psi(gamma(n)^-1 gamma(n+r)) has coefficients with a standard common denominator A and no r-degree-zero terms, so r=A is a right period. Accepted for that clause only. The existence-of-period conclusion of A.12 is not disproved.

### R6-F30. LIN Taylor-coordinate lemma: connectedness hypothesis missing from the contract
- Path: `GI/reviews/lin-taylor-incorporation-review-compiler-001/REVIEW.md`
- Reviewer / date: compiler; date not stated
- Point: The contract for `lem:Pi` omitted the connectedness required by the original setup; the step bound is the nilpotence class of G, and no class(P_0) <= s assertion is available.
- Kind: HYPOTHESIS or convention not checked
- Next: Corrected contract restores connectedness (changes only hypothesis, normalization and constant fields); accepted as incorporation. Compiler does not approve its own finite-evaluation embedding step.

### R6-F31. LP13: "exponential is a diffeomorphism" overstated the cited source
- Path: `GI/reviews/lp13-wording-review-compiler-001/REVIEW.md`
- Reviewer / date: compiler (correction by /root; original proof by Theta); date not stated
- Point: GTZ Section 3 states only that the exponential is a homeomorphism; the LP13 proof cited it as a diffeomorphism. The reviewer checked that the uses (closed connected subgroups, quotient topology, local lifts) need only the topological statement and that smoothness in the metric argument comes from other inputs.
- Kind: OVERSTATED claim
- Next: Changed to "homeomorphism"; accepted.

### R6-F32. Section 12 join: filtration index range left partly undefined
- Path: `GI/reviews/section12-join-independent-arithmetic/REVIEW.md`
- Reviewer / date: /root/astra_v14_assertions_arithmetic (author: Gaussian); date not stated
- Point: The phrase "with j>0" before the filtration display could restrict the declaration H_(a,j)=1 for a>1 and leave H_(a,0) unstated.
- Kind: GAP or missing justification (definition-level)
- Next: Reviewer requested the full index range be stated in a preserved successor; acceptance is conditional on that clarification (final target in DECISION.json).

### R6-F33. GTZ Section 12 as printed: false pigeonhole step and other defects
- Path: `GI/reviews/section12-join-independent-arithmetic/REVIEW.md`
- Reviewer / date: arithmetic; date not stated
- Point: (a) The near-zero pigeonhole assertion on p. 1308 fails for alpha=1/2 and odd shifts. (b) The p. 1312 illustration omits the core coordinate from H_(0,1) although the displayed orbit has it. (c) The final top group P_m can exceed the degree-rank top T on which the character is defined, so an integral extension of the character (using the Hall-basis lattice splitting) is needed before choosing the test function. (d) Scalar cutoff formulas alone do not give a globally unit-norm nilcharacter.
- Kind: ERROR in the mathematics (published source)
- Next: The join uses fixed boxes at arbitrary positions, the general p. 1314 definition, the extended character, and a same-character completion (cos(theta) W, sin(theta) W_0). Accepted conditionally. Not asserted that every earlier use of near-zero normalization has been removed.

### R6-F34. Section 12 comparison gives only a rank drop for R > 1; LP04 not independently reviewed
- Path: `GI/reviews/section12-join-independent-arithmetic/REVIEW.md`
- Reviewer / date: arithmetic; date not stated
- Point: The corrected comparison lowers ordinary degree to m-1 only when R=1; for R>1 it gives degree-rank at most (m,R-1). The stronger ordinary-degree assertion is not restored. The reviewer authored upstream LP04, so the review is conditional on LP04 and not blind.
- Kind: OVERSTATED claim (in the source statement) with LIMITATION
- Next: Rank iteration handles R>1 (`GI/reviews/v14-matrix-join-independent-001` confirms the endpoint (m,0) argument). LP04 non-author review, analytic frequency decomposition and Theorem 11.1 hypotheses remain separate.

### R6-F35. LP13 record U01 attributes the strong convention to GTZ Definition 6.19
- Path: `GI/reviews/v14-final-gi-integration-review-001/REVIEW.md`
- Reviewer / date: /root/v14_integration_review; date not stated
- Point: Published Definition 6.19 quantifies the vertical identity over standard x and g_d only; A.2/A.3 do not turn weakly defined objects into ones satisfying the identity at all limit points. The record's attribution of the all-limit ("strong") convention to the published definition is not accepted; it is a project premise supplied by the actual constructed witnesses (initial selection, constructor/matrix chain, LP05 transfer). No weak-to-strong or prescribed-symbol equivalence is accepted.
- Kind: OVERSTATED claim
- Next: Change required to `uses[id=GTZ-LP13-U01]` in module03/SOURCE-USES.json. `GI/reviews/v14-gi-package-independent-001` reports the corrected record in package-update-002.

### R6-F36. Missing lattice/rationality premises in RANK and MF
- Path: `GI/reviews/v14-gi-integration-review-001/REVIEW.md`
- Reviewer / date: /root/v14_integration_review; date not stated
- Point: (RANK) the finite bracket spans in eq:DR must exponentiate to rational subgroups for the original Gamma before GT12 Prop A.10 applies; A.10 must not be invoked by assuming the lattice conclusion. (MF) the central-quotient argument needed K = P intersect G_d to meet Gamma in a lattice, which was "previously missing"; this needs P and G_d rational, proved by a reverse implication from compactness of their lattice quotients (maximal-subalgebra argument), then A.10 and a coset injection for finite index. (LP02) E.5 must output strong selected unit/vertical functions chosen for a finite dictionary before passing to the ultrapower.
- Kind: GAP or missing justification
- Next: Supplied by the three insertions in v14-gi-source-candidates-001 (rank.tex, mf.tex, lp02.tex); accepted in narrow scope. No uniform bound over unbounded models.

### R6-F37. Lin-Yang D6 normalization: retained inputs and disputed Baba-Granath statements
- Path: `V14/ly-d6-normalization-v1/reviews/INDEPENDENT-REVIEW.md`
- Reviewer / date: /root/astra_v14_baseline_compiler (author: gaussian); date not stated
- Point: The constants c1=c2=c3=c4=1 are derived from the discriminant -4 and -24 points without the CM(-19) value or BG's explicit conic map, but the global identities (s3^2/s2^3 = c1 j, s5/(s2 s3) = c2, s6/s2^3 = c3 j + c4) and the affine shape are retained published inputs, as are Lin-Yang's eta CM values and embedding counts. The review "does not reapprove BG's printed Riemann form, the disputed displayed product map, its abstract product-isomorphism conclusions, or Theorem 3.10", and does not retire them for other consumers.
- Kind: LIMITATION
- Next: Accepted as one connection; A001-Q-MODULI application to the corrected principal datum remains separate.

### R6-F38. Thorne's generic-reducedness assertion for the unreduced trivial-character lifting ring is defective
- Path: `V14/pan-local-rings-v1/REVIEW.md`
- Reviewer / date: /root; 8 November 2026
- Point: The published correction concerns Thorne's Prop 3.15(1): generic reducedness of the special fiber of the entire unreduced trivial-character lifting ring fails (valid only after nilreduction). Pan's Lemma 4.2.10(1) / Prop 4.2.4 pass to reductions (p. 47) and are supplied by Taylor Lemma 3.2(1), and the nontrivial-character branch uses 3.15(2)/3.16, so the correction does not invalidate Pan's inference.
- Kind: ERROR in the mathematics (published source; checked not to propagate)
- Next: Accepted as not affecting the route. Pan and Thorne were read in author versions; final-version comparison open. Shotton branches outside the review.

### R6-F39. Flatness of the unreduced fixed-determinant lifting ring was not supplied by any cited source
- Path: `V14/pan-local-rings-v1/REVIEW.md`
- Reviewer / date: /root; 8 November 2026
- Point: Thorne Prop 3.15(2) and Taylor Prop 3.1(1) do not state O-flatness of the unreduced ring, and a characteristic-zero generic point plus geometric irreducibility does not exclude embedded torsion. Pan's use needs it. Reviewer and author found this independently.
- Kind: GAP or missing justification
- Next: Author's Section 4 gives a direct proof (commutation via Cayley-Hamilton, 2x2 minors, straightening basis showing the residue quotient is a domain, torsion-freeness, monic quadratic extension); accepted. Does not apply in the trivial-character case. Not yet in the manuscript TeX.

### R6-F40. Pan's fixed-determinant comparison is a degree-two etale cover, not a polynomial-ring product
- Path: `V14/pan-local-rings-v1/REVIEW.md`
- Reviewer / date: /root; 8 November 2026
- Point: Pan's "overbrief global polynomial-ring comparison" between fixed-determinant and unrestricted lifting schemes is replaced: scaling Frobenius by s gives a finite etale degree-two cover (s^2 = det(Phi)/d), "a cover, not a global affine-line product"; the formal power-series factor exists only at the chosen residual point via the sheet s=1 (2 invertible).
- Kind: GAP or missing justification
- Next: Replacement argument checked and accepted (connectedness, irreducibility, dimension, componentwise reducedness after reduction). Not yet incorporated in the TeX.

### R6-F41. Pan utility: Kisin Prop 9.5 gives less than needed (versal vs universal, W(k) vs O)
- Path: `V14/pan-utility-p5-v1/REVIEW.md` (wrapper: `V14/pan-utility-p5-v1/REPORT.md`)
- Reviewer / date: /root/astra_v14_source_review, run dated 2026-11-07 (author: arithmetic)
- Point: Kisin's author Prop 9.5 gives only smoothness in the general versal case and is stated with W(k) coefficients, whereas PAN-15 needs the completion isomorphism for the universal ring over O. KW09b Prop 2.1 and Kisin 2003 were read only in author versions.
- Kind: HYPOTHESIS or convention not checked
- Next: Resolved by a direct O-coefficient compact-lattice proof (scalar endomorphisms from the nonsplit extension give universality); local framing proved directly without KW09b. Accepted for PAN-12 to PAN-15 at p=5. No Lichtenbaum vanishing, enlarged-S extension or upper bound follows from the Euler calculation (PAN-14). Final-version comparisons open.

### R6-F42. Arthur-Clozel composite-degree Lemma III.6.3 is defective and must be avoided
- Path: `V14/prime-cyclic-base-change-v1/reviews/arthur-clozel-prime-review-root-001/REVIEW.md`
- Reviewer / date: /root (author: anchor); date not stated
- Point: The printed composite-degree descent (III.6.3, pp. 217-218) iterates without re-establishing Galois invariance of the descendant at each step (error identified in Clozel's seminar notice). The substitution uses only prime-degree III.4.2(a),(d) and III.5.1, re-proving invariance at every step from the original r, excluding self-twists in characteristic zero, and getting the split real components by a direct convolution computation so as not to import the non-split local theory (which has backward references to later arbitrary-degree results).
- Kind: ERROR in the mathematics (published source; avoided)
- Next: Substitution accepted for four application cards. Prime-degree trace formula and strong multiplicity one remain unproved inputs; no general composite-degree descent.

### R6-F43. H-D4 ascent/descent: Langlands edition and ramified local compatibility open
- Path: `V14/prime-cyclic-base-change-v1/reviews/h-d4-automorphic-review-root-001/REVIEW.md`
- Reviewer / date: /root (author: theta); date not stated
- Point: The Langlands text read is the IAS retypesetting, not compared with the 1980 edition. Langlands Chapter 2(e) restricts its Weil-parameter assertion to reducible or dihedral parameters, so it cannot be used as ramified local-global compatibility; that input (H-D5) is not supplied, nor the full Hilbert-form Galois attachment source check. The review was not blind.
- Kind: LIMITATION
- Next: Left open as retained obligations. The edition issue is made unnecessary for the global inputs by the Arthur-Clozel prime-degree substitution (F42).


## Internal reviews, batch 7

Note: 23 of the 36 files are author REPORTs (proposals or obstruction notes), not independent reviews. Where an author report records a counterexample or a failed step, it is listed as a finding. "Pending" means the file itself says independent review had not happened at freeze.

Path prefixes used below:
- `V14/` = `research/version14/`
- `V15/` = `research/version15/`
- `QOPT/` = `research/version15/snapshots/v15-018/quartics/quartic-299-314/sources/work/quartic-optimization-20261107/`


### R7-F1. Original 156-power guarded common scale: residue classes collide
- Path: `QOPT/resume-review-common-scale-20261107/REVIEW.md` (reviewing `QOPT/resume-depth-20261107/common-scale/REPORT.md`)
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, November 7, 2026 (author of reviewed argument: `/root/astra_quartic_opt03_depth`; defect first reported by the author during the review, confirmed independently)
- Point: In G2 the replaced term gamma^-156 * E * P2^2 has valuation class 4c - alpha mod 8 (c = v_p(gamma), alpha = v_p(R) odd), because P2^2 = f(U2)^4 lies in 8Z; the unchanged E * P4^2 term has class -alpha mod 8. For c even these coincide (e.g. alpha=1, c=2, v(f(U2))=78, v(f(U4))=0 gives both terms valuation -1 while the guard has valuation 20), so the claimed disjoint-class / unique-minimum proof fails. Requiring c odd would be an extra restriction the equations do not impose.
- Kind: ERROR in the mathematics
- Next: original guarded construction rejected as proved; author erratum withdraws the validity claim. A separately frozen reciprocal variant (exponents 160/40/80, guard gamma^16 E^12) is accepted at source level only; all 128 (alpha, c) residue cases checked. No full rational counterexample to a compiled system is asserted.

### R7-F2. Unguarded common inverse product across the three detectors fails
- Path: `QOPT/resume-depth-20261107/common-scale/REPORT.md`; independently replayed in `QOPT/resume-review-common-scale-20261107/REVIEW.md`
- Reviewer/date: author `/root/astra_quartic_opt03_depth`, November 7, 2026; confirmed by `/root/astra_quartic_opt05_anchor`
- Point: Replacing the per-detector E_j by a common inverse product 1/(R0 R1 R2) is unsound in the actual odd-point scale domain. With all four roots equal to [2377]P and p = 76249, lambda = p: abscissa valuations (-2, 0), scale valuations 0, -16, -32, hence v(R0), v(R1), v(R2) = 1, -75, -155, product -229; the common inverse has valuation +229 at a required contact prime of detector 0 where E0 has -1, so large powers weaken rather than enforce the comparisons. Pairwise-disjoint odd supports also cannot be presumed since repeated contact forms are allowed.
- Kind: ERROR in the mathematics (of the proposed step)
- Next: rejected; stated as an obstruction in the root/scale domain, not a counterexample to the accepted quartic. Repair would need a proved earlier restriction; left open.

### R7-F3. "Cheaper" pole guard B_new = B_old * C^2 / R_j^2 does not preserve the low tests
- Path: `QOPT/resume-depth-20261107/common-scale/REPORT.md`
- Reviewer/date: author `/root/astra_quartic_opt03_depth`, November 7, 2026
- Point: The common-place conclusion becomes only lambda_p > alpha/2 - c; for large c unchanged low terms may have negative valuation (alpha=1, c=100, unit T0 gives term valuation -8, compatible with the bound), so low-formality and the pre-H exclusion do not follow.
- Kind: ERROR in the mathematics (of the proposed step)
- Next: rejected; all low terms would need redesign; left open. The valid guarded realization costs 336 variables (no saving).

### R7-F4. Common-scale acceptance is source-level only
- Path: `QOPT/resume-review-common-scale-20261107/REVIEW.md`
- Reviewer/date: `/root/astra_quartic_opt05_anchor`, November 7, 2026
- Point: No common-scale IR, quadratic compilation, coefficient table or variable reduction was supplied or accepted; existence of the nonzero rational gamma, binding of new gates to the exact R values (t = v37, 4*v391, v37+32*v439) and the new H-bootstrap proposal are explicitly outside the review.
- Kind: LIMITATION
- Next: a later implementation needs a separate non-author review; not stated whether done in this batch (the 314/313 reports implement a shared scale but are author proposals).

### R7-F5. Removing the root square-root coordinate a (unrestricted E(K) roots) breaks the product-height lemma
- Path: `QOPT/resume-depth-20261107/root-domain313/REPORT.md`
- Reviewer/date: author `/root/astra_quartic_opt03_depth`, November 7, 2026
- Point: If roots are allowed to be arbitrary finite non-torsion points (not in ZP), take A = Q_n = [n]P, T = Q_n + T0, Z = P + T0, S fixed, n odd. Since x(Q+T0) = -D/x(Q), the product x(A)x(T)x(Z)x(S) = -D x(P+T0) x(S) is independent of n while h(x(A)) grows quadratically, so no uniform constant restores the old lower bound on the height of the product. The family also satisfies the anchor's root part (q integral at 2 and 3, q = 3 mod 8, t odd), so the current anchor does not exclude it.
- Kind: ERROR in the mathematics (of the proposed 297-variable step)
- Next: rejected; "No 297-variable construction is accepted by this note". Possible repairs (positivity at both real embeddings, x - D/x, x(2Q)) listed as open, each needing a fresh height proof.

### R7-F6. Removing b while retaining a needs two hypotheses checked on every branch
- Path: `QOPT/resume-depth-20261107/root-domain313/REPORT.md`
- Reviewer/date: author `/root/astra_quartic_opt03_depth`, November 7, 2026
- Point: Recovery b = delta/a is valid only if (i) the addition equations yield an actual K-rational ordinate delta, not merely an abscissa satisfying a Kummer relation on an unspecified twist, and (ii) a != 0, since T0 = (0,0) satisfies c = a^2 = 0 but has no lift (b^2 = -D impossible at the real embeddings). The note does not certify these on identity, tangent and zero branches.
- Kind: HYPOTHESIS or convention not checked
- Next: discharged in the 307 construction (`QOPT/reciprocal307-20261107/REPORT.md`: universal curve identity for yR, root-nonzero chain via the height-product inverse rows) and, for S, checked in `review-s299`; the 307 report itself was pending review at freeze.

### R7-F7. Binary anchor (deleting W, form <1,1> instead of <1,1,6>) loses the representation lemma
- Path: `QOPT/resume-anchor-20261107/REPORT.md`
- Reviewer/date: author agent05; date not stated in file (directory dated 2026-11-07)
- Point: With delta = (3/4)^L, L = 2^24, take g1 = 5 * 3^L: mod 121, 3^L = 3 and delta = 119, so A = 3 g1^2 - delta^2 = 66 mod 121, v_11(A) = 1; since -1 is a nonsquare mod 11, A is not a sum of two rational squares although v_3(g1) >= L and |g1| > 1/10. The blanket local representation argument therefore fails for the binary form.
- Kind: ERROR in the mathematics (of the proposed step)
- Next: rejected, recorded as "preserved unsuccessful direction"; would need an additional proved property of actual scalar values. The 379/380/381 ternary candidates in the same report are pending non-author review; the report notes the Hasse-Minkowski (Voight Thm 14.6.9) application inventory must record the changed A.

### R7-F8. Sharing another alternate logarithm as common denominator loses the index normalization
- Path: `QOPT/resume-fixed-v0-20261107/REPORT.md`
- Reviewer/date: author `/root/astra_quartic_opt05_anchor`, November 7, 2026
- Point: Deleting the V0 approximation and using V2's logarithm as denominator: with primary indices u_i = kappa n_i and H index h, defining the common value as alternate_2/primary_2 makes every alternate quotient equal kappa n_i / h, identical to the primary quotient, so all cross comparisons vanish for any kappa/h (e.g. h=3, kappa=2, n_i=7 gives 14/3, not 7). The original V0 denominator fixes the scale through its index h-1; without it the Lucas and input-height proofs lack a hypothesis.
- Kind: ERROR in the mathematics (of the proposed step)
- Next: rejected; saving zero. Also stated: the finite-field (p = 1000000007) rank probe is reconnaissance, not a characteristic-zero impossibility proof; not independently reviewed.

### R7-F9. No direct quadratic logarithm gate in the enlarged chart interface; square-root shortcut invalid
- Path: `QOPT/resume-logarithms-20261107/REPORT.md`
- Reviewer/date: author `/root/astra_quartic_opt05_anchor`, November 7, 2026
- Point: Writing G(w) = sqrt(1-w) H(w) to drop the approximation denominator is not a rational witness map (chart has both sign branches; positive root can reverse the logarithm sign; root scale a is a variable). Exact row reduction over 136 quadratic monomials in 15 variables (a,b,c,V,Qpoint,I,K,W,z,w,w2,w4,Y,Y2,L) to order g^40 gives rank 124 with a 12-dimensional kernel consisting only of existing relations, none containing L; so no quadratic equation in this interface can define L = ell + O(g^41).
- Kind: ERROR in the mathematics (proposed shortcut rejected) with stated LIMITATION
- Next: saving zero. Explicitly not a lower bound for other auxiliary functions, changed charts, coupled points, or a V0-specific construction; "has not received independent review".

### R7-F10. Initial 299 candidate bound the wrong S alternate-square cache
- Path: `QOPT/resume-depth-20261107/review-s299/REVIEW.md`; also `QOPT/resume-elimination-20261107/reciprocal299-r2/REPORT.md`
- Reviewer/date: agent03 (author of reviewed extension: agent01); date not stated
- Point: The first 299 candidate used coordinates 202/203 for B = F^2 instead of the actual cache 196/197 (rows 148/149, D*c*B + K^2 - c), leaving undeclared coordinates; the alternate curve k^2 = F - D F B and the ratio (1 - D B) z = k were therefore tied to the wrong object. Review also stresses the orientation equation a*b = D h - s (D f + c) is essential because b enters the scalar subsystem; recovering only the root abscissa would leave a sign open.
- Kind: ERROR (in the finite construction)
- Next: initial candidate rejected and preserved under sibling `reciprocal299` (FINDING-S299-1); corrected in `reciprocal299-r2`, which agent03 accepts within the S-extension scope. Not a bijection to old S square-root fibers; full composition review assigned separately to agent10.

### R7-F11. Opposite-point branch not constrained by the initial single biquadratic equation
- Path: `QOPT/reciprocal307-20261107/REPORT.md`
- Reviewer/date: author `/root/astra_bl_horizontal_repair` (construction and compiler); date not stated (directory 2026-11-07)
- Point: For f = F the first slope row forces k = -h; the initial single biquadratic equation "failed to constrain" this opposite-point branch. The three slope equations s(f-F) = h+k, s(h-k) = 1 - D(Y + fF + Yalt), s^2 = c - D(f+F) close it: h = 0 contradicts the curve with 3Df^2 = 1, so h != 0 and 2sh = 1 - 3Df^2 is the tangent slope. Also the maximum coefficient changes to 186624*C^2 exactly; "the old +64 must not be reused".
- Kind: GAP or missing justification
- Next: repaired in the 307 equations; whole 307 candidate pending independent review at freeze (later described as "accepted307" in the 301/299 reports).

### R7-F12. Published coefficient bound 2^3247 is false for the selected 314-variable ordinary lift
- Path: `QOPT/resume-depth-20261107/review-ordinary299/REVIEW.md`
- Reviewer/date: agent03 (lifts by agent10); date not stated
- Point: The exact maximum coefficient of the 314-variable lift is 3^4098 + K (K the 1514-bit inherited constant), with 2^6495 <= max < 2^6496; "The old below 2^3247 bound is false for this lift." The 315-variable lift (3^2050 + K, 3250 bits) also exceeds that cap; only 316 satisfies it. The ordinary companion must not be described as having fewer than 300 variables.
- Kind: OVERSTATED claim
- Next: correct bound (< 2^6496) stated in the review; `V15/evidence/final-assembly/REVIEW.md` uses "height below 2^6496". Lifts accepted, no correction to the artifacts.

### R7-F13. Undeclared exponent k in the two-scales amplification lemma
- Path: `V15/evidence/review-context/v15-amplification-current-review-arithmetic-001/REVIEW.md`
- Reviewer/date: not named (reviewer authored the 237 scalar criterion); date not stated
- Point: Lemma `v15:amplification:lem:two-scales` opens "Let alpha>0, H_*>0, and suppose..." with k undeclared; the argument (M^k | N, N != 0 gives M <= |N|^(1/k)) needs k a positive integer. Required wording: "Let k in Z_{>0}, alpha>0, H_*>0". Also not recomputed: the four displayed numerical comparisons (large integer products) in the improved-corollary paragraph.
- Kind: HYPOTHESIS or convention not checked
- Next: "Sent to GI/root; no frozen source was edited." `final-assembly/REVIEW.md` later says "The positive-integer amplification exponent now matches every use of M^k".

### R7-F14. Character order: statement about epsilon vs epsilon^2 in the five-contact bound
- Path: `V15/evidence/review-context/v15-application-transfer-review-h6-001/REVIEW.md` (echoed in `V15/evidence/final-assembly/REVIEW.md`)
- Reviewer/date: `/root/v14_h6_coverage`; date not stated
- Point: At manuscript lines 30725-26 the divisibility ord | [L':Q] holds for epsilon^2, not epsilon; the valid consequence is ord(epsilon) <= 2[L':Q]. The pronoun must name epsilon^2. The inequality actually used downstream (cubic degree bound via phi(R) * prod(1+1/p)) is valid.
- Kind: OVERSTATED claim (wording; stronger divisibility not available)
- Next: clarification "remains editorial" per this review; final-assembly records "The epsilon-square correction bounds the original character's order by twice the field degree, rather than asserting the stronger divisibility."

### R7-F15. Application-transfer review: abstention and unopened primary sources
- Path: `V15/evidence/review-context/v15-application-transfer-review-h6-001/REVIEW.md`
- Reviewer/date: `/root/v14_h6_coverage`; date not stated
- Point: Reviewer authored raw233/sparse233 and abstains from V15-FINAL233-TRANSFER (hash bindings checked mechanically only). Five-contact bound accepted only relative to suppliers: internal modular-realization theorem, aggregate theorem, and Remond / Gaudron-Remond surface estimates were not reproved and the primary publications were not opened in this review. "Not unconditional closure of G05."
- Kind: LIMITATION
- Next: FINAL233 left to the disjoint finite review (9a944190, cited in final-assembly); Remond/GR sources checked in the surface-height review (F16).

### R7-F16. Surface-height lemma accepted only against the author version of Remond
- Path: `V15/evidence/review-context/v15-surface-height-review-h6-001/REVIEW.md`
- Reviewer/date: `/root/v14_h6_coverage`; date not stated
- Point: Remond, "Proprietes de la hauteur de Faltings": only the June 2021 author manuscript (Cor. 1.2, stable-height extension after Cor. 1.3, Prop. 2.1) was read; the 2022 published PDF was paywalled and equality with the final version is not established. Gaudron-Remond 2023 (Thm 1.9(1)) and 2014 (Cor. 8.4, Sec. 2.3) were checked from publisher PDFs and independently give the lower bound hF(A) > -3 dim(A)/2 and isogeny cost.
- Kind: LIMITATION
- Next: left open ("final-published-version comparison for that source remains open"); final-assembly restates that the 2023 route "does not claim to have independently obtained final 2022 text".

### R7-F17. Final assembly review: reviewer's own ancestry and inherited limits
- Path: `V15/evidence/final-assembly/REVIEW.md`
- Reviewer/date: not named; date not stated
- Point: Reviewer wrote earlier residual/affine optimization work possibly ancestral to sparse233 and excludes it from fresh acceptance, relying on the disjoint 9a944190 finite review for all selected maps and 207 residuals. Not a fresh audit of unchanged external theorems. Defining threshold N0 and the aggregate intercept remain ineffective; N >= 53 is only a coefficient-size threshold; universal polynomial and consequences do not inherit variable/height bounds.
- Kind: LIMITATION
- Next: not stated beyond the disclosure.

### R7-F18. Centralizer lemma: scope narrower than recorded consumer span; rank-one hypothesis essential
- Path: `V14/proofs/qm-centralizer-v1/reviews/INDEPENDENT-REVIEW.md`
- Reviewer/date: not named (author of the earlier B11 packet); date not stated
- Point: Acceptance covers only the algebra A = M_s(E), Delta = E at manuscript lines 575-583; the recorded consumer span 575-588 also contains geometric steps (realizing matrix idempotents as abelian factors, their endomorphism algebra) that are not covered. Poincare reducibility and construction of Y are not reproved. Adverse case noted: a self-centralizing field alone does not give Delta = E (maximal subfield of a nonsplit quaternion algebra); the nonzero rank-one C-module V is essential and is retained.
- Kind: LIMITATION
- Next: geometric steps handled in the separate idempotent-image review (accepted, no change); no correction requested.

### R7-F19. A052 interface: scalar-Frobenius-model assertion not sourced; replaced by coarse-point rationality
- Path: `V14/source-use-replacements/ribet-a052-v1/REPORT.md` (author proposal)
- Reviewer/date: author not named; date not stated
- Point: The manuscript's sentence that each supersingular curve has a chosen F_{q^2}-model with scalar Frobenius is not sourced or proved, and the final Jetchev-Kane text (short Sec. 2.5 paragraph) lacks the Frobenius statement and is unavailable in final form. Replacement: Ribet, Invent. Math. 100 (1990), Prop. 3.3, Remarks 3.5(a),(b), Prop. 3.6 (Frobenius acts as an involution on supersingular enhanced classes, no squarefreeness on M), giving Frob_q^2(x) = x and hence F_{q^2}-rationality of the coarse point only. Convention points fixed: right R-module Hom(E_0,E) (not Hom(E,E_0)); transporter direction z vs z^-1; at q the Dieudonne module, not a rank-two Tate module.
- Kind: GAP or missing justification
- Next: proposed replacement; "need independent review"; root good-reduction draft `cj-good-reduction-root/PROOF-DRAFT.md` unfinished and not an accepted premise. Outcome not stated in this batch.

### R7-F20. 330-variable candidate needs a stronger completeness progression than the source supplies
- Path: `QOPT/resume-depth-20261107/strong-h330/REPORT.md`
- Reviewer/date: author `/root/astra_quartic_opt03_depth`, November 7, 2026
- Point: Moving H0^2 to the weight-158 slot requires v(U) >= 160, i.e. v(f(H)) >= 80, but the old complete witnesses guarantee only v(f(H)) >= 40. The report therefore replaces h = 0 mod Pi^19 M_- by Pi^39 M_- (compatibility argued from the V13 gcd relations at lines 20631-20649). This is a changed completeness hypothesis, not inherited.
- Kind: HYPOTHESIS or convention not checked (strengthened, pending review)
- Next: pending independent review together with 332; the later 326 construction (`three326/REPORT.md`) avoids it and returns to Pi^19 (noting M0 has only G2 precision 12, not order 40).

### R7-F21. Earlier 357 attempt / exact-valuation guard deletion has an unresolved completeness modulus
- Path: `QOPT/resume-elimination-20261107/exact319/REPORT.md`; `QOPT/resume-elimination-20261107/ordinary-chains/REPORT.md`
- Reviewer/date: author `/root/astra_quartic_opt01_elimination`, November 7, 2026
- Point: The previously recorded 357 attempt imposed a new exact 3-adic valuation and "had an unresolved completeness modulus"; deletion of the g0 inverse guard by that route is "still blocked by its recorded completeness-modulus obligation".
- Kind: GAP or missing justification
- Next: left open; not used. 319 retains the guard and uses exact unscaling instead.


## Internal reviews, batch 8

Path prefixes used below (all repo-relative):

- `OPT/` = `research/version15/snapshots/v15-018/quartics/quartic-299-314/sources/work/quartic-optimization-20261107/`
- `U300/` = `research/version15/snapshots/v15-018/quartics/quartic-299-314/sources/work/quartic-under300-20261107/`

Every review in this batch ends in acceptance (three files are author reports, not reviews). No review in this batch rejects the object it reviews. The findings below are errors recorded or reproduced by a review, hypotheses a review says had to be re-established, and stated limits.


### R8-F1. Rejected 299 candidate used undeclared coordinates
- Path: `OPT/resume-review-inventory-r6-01/REVIEW.md`
- Reviewer / date: agent01 (author of the 301 elimination and 299 compiler; not author of the inventory); date not stated (directory dated 2026-11-07)
- Point: the first reciprocal299 IR ("ab42", polynomial "18158") declares 299 coordinates but its rows use 301, with undeclared coordinates 202 and 203. The reviewer reproduced the failure literally. The fault was originally found by agent03.
- Kind: ERROR (in the candidate system as emitted)
- Outcome: repaired in reciprocal299r2 by replacing 202/203 with 196/197 in rows 120, 121, 148, 149 (all other rows identical). Rejected bytes are kept as adverse history; no acceptance attaches to them. The corrected IR has separate external reviews (not in this batch).

### R8-F2. The 156-power common-scale construction remains rejected
- Paths: `OPT/resume-review-shared314-20261107/REVIEW.md`; also recorded in `OPT/resume-review-inventory-r4-01/REVIEW.md` and `OPT/resume-review-transports314-20261107/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor`, November 7, 2026 (shared314, transports314); `/root/astra_quartic_opt01_elimination`, November 7, 2026 (inventory r4)
- Point: an earlier common-scale proposal ("original 156-power construction", "rejected156 proposal and its erratum") was rejected. These reviews state that the rejection stands and that the earlier, narrower reciprocal-variant review did not accept the shared314 H bootstrap. The reviews in this batch do not restate what was wrong with the 156-power argument.
- Kind: ERROR (prior, recorded)
- Outcome: rejected; superseded by the shared314 proof, which was reviewed afresh (F3).

### R8-F3. Shared314: the old depth-20 lemma cannot be quoted after the H bootstrap
- Path: `OPT/resume-review-shared314-20261107/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor`, November 7, 2026
- Point: in shared314 the high-H test no longer supplies H depth directly. The bootstrap (depth-one integrality of the ratios, then F(0,0,0) = -1 forcing one of L2, L3, L4 to be a unit, then z(U_i) = L_i z(H)) yields only formal depth 10 for H, hence relative precision 40 for the primary analytic correction, against surplus precision 80 in the old source. The reviewer states that the source lemma's hypotheses explicitly require H depth 20, so that lemma cannot be cited and the step must be redone. Redone, precision 40 is exactly sufficient (40 for the three high label comparisons, 10 for the first/middle comparison; the index-1 G2 quotient has precision 12). The reviewer also checks the bootstrap is noncircular: it does not use the later Lucas equality or any high H depth.
- Kind: HYPOTHESIS or convention not checked (by a naive citation; re-established here)
- Outcome: accepted; argument redone in the frozen proof and confirmed. Completeness keeps the original Pi^19 progression (depth 20).

### R8-F4. Shared314 arithmetic review does not cover the emitted system
- Path: `OPT/resume-review-shared314-20261107/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor`, November 7, 2026
- Point: the review covers the source-level arithmetic only. It explicitly leaves to a separate structural review: full compiler transport, all changed consumers, invariance of the new group and scaled-output rows under the A, T, Z root-restoration sign actions, the variable count, and the full sum-of-squares table. "This report alone does not approve ... a 314-variable quartic artifact."
- Kind: LIMITATION
- Outcome: other reviews in this batch state that agent10 wrote the separate construction review (not in this batch).

### R8-F5. Reciprocal307: the auxiliary-domain review was conditional; its missing inputs are supplied here
- Path: `OPT/resume-review-reciprocal307-01/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt01_elimination`; date not stated
- Point: agent10's review of the auxiliary-domain extension was conditional on a group law and a root restoration that it did not establish. This review supplies them: (i) the four closure equations give U - V as an actual point with orientation, including f = F (h = 0 is excluded algebraically since it would need both D f^2 = 1 or f = 0 and 3 D f^2 = 1), U = O, V = O, and unequal finite 2-torsion; (ii) c != 0 globally, because c = 0 forces coordinates 341, 342 and a triangular chain to vanish and row 352 becomes -1 = 0, so a != 0 and b = yR/a restores b^2 = c^2 - D. Other conventions pinned: enlarged auxiliary labels are U_i = k_i R0 + T_i, not integer multiples of P; the usable identities are [2m]U_i = [2k_i]H and [2(m-2)]V_i = [2(k_i - 2n_i)]V0; global rational-approximant nonvanishing certificates replace the old optional real-positivity interval; no claim that a raw f has a square root in K.
- Kind: GAP or missing justification (in the conditional domain review, closed here)
- Outcome: accepted. The result is equality of rational input projections with accepted313, explicitly not a bijection of private witness fibers. No ordinary-coefficient companion is covered.

### R8-F6. Ordinary-coefficient lifts: the middle chain misses the 3247-bit cap
- Paths: `OPT/resume-review-ordinary307-20261107/REVIEW.md`, `OPT/resume-review-ordinary313-20261107/REVIEW.md`, `OPT/resume-review-transports314-20261107/REVIEW.md`, `OPT/resume-sol-review-ordinary-chains-20261107/REVIEW.md`; restated in `OPT/resume-review-inventory-r6-01/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor` (first three) and `/root/sol_protocol_final_review` (ordinary chains), November 7, 2026
- Point: in every ordinary lift family the three chains give maximum coefficients 3^1026 + K, 3^2050 + K, 3^4098 + K (K the inherited 1514-bit constant), i.e. 1627, 3250, 6496 bits. The middle lift (323, 329, 330, 335 variables respectively) exceeds the published 2^3247 bound by three bits. The shortest lift meets only the 8193-bit cap. The exact maximum includes K; a pure power of 3 would be the wrong coefficient. The selected 299/314 pair uses the 6496-bit ordinary system, which does not satisfy the former 2^3247 bound.
- Kind: HYPOTHESIS or convention not checked (a coefficient cap that one lift in each family fails)
- Outcome: recorded as a property of the artifacts; inventories state the 3250-bit artifacts are not represented as meeting the 3247-bit bound. No repair.

### R8-F7. Squared-anchor358 changes the maximum coefficient
- Path: `OPT/resume-review358-20261107/REVIEW.md`
- Reviewer / date: `/root/astra_bl_horizontal_repair`, November 7, 2026
- Point: after replacing the anchor parameter by T = g1^2 + C*Qroots, the largest coefficient is 186624*C^2 + 64 (at v89^4), not the predecessor's 16*C^2, and specialising C produces three coefficient collisions (6,419 coefficient-power entries, 6,416 monomials). The supporting local fact v3(g1^2) = v3(f1) is stated to be specific to the orbit of multiples of P, not a general identity for square roots in K. `OPT/review-sparse-lucas320-20261107/REVIEW.md` adds that the 16*C^2 bound there must not be imported into a later anchor with a different bound.
- Kind: HYPOTHESIS or convention not checked (coefficient bound is source-specific)
- Outcome: accepted with the corrected figure. The review covers no ordinary-coefficient circuit and no composition with another reduction.

### R8-F8. Abscissa359: Laurent correction and criterion rescaling made explicit
- Path: `OPT/resume-review359-20261107/REVIEW.md`
- Reviewer / date: `/root/astra_bl_horizontal_repair`, November 7, 2026
- Point: for the new coefficient formulas (v3(X_n) = 0 for n odd, -2 - 2 v3(n) for n even; v2(X_n) = -1 for n odd) the reviewer does not rely on the author's asymptotic Laurent expansion alone. The correction is controlled by the exact identity x - z^-2 = D f, with v(f) = 3 at the place above 2, so it cannot cancel the valuation -1 coefficient. A finite computation at 2P would not prove the statement for all even n. No good reduction at 2 is used. Separately, a standard-form solution (u0, v0, w0) of the quaternion criterion must be mapped by U = C u0/g0, V = C v0/g0, W = C (w0 - 1)/g0; dividing by g0 alone omits the C scaling and the affine shift.
- Kind: GAP or missing justification (closed by the reviewer's argument)
- Outcome: accepted. Equality of input projections with 366; the reduction replaces the 362 packing and is not additive with it.

### R8-F9. Constant-gate lower bounds hold only in a restricted model
- Path: `OPT/resume-sol-review-ordinary-chains-20261107/REVIEW.md`
- Reviewer / date: `/root/sol_protocol_final_review`, November 7, 2026
- Point: the lower bounds (at least 16 constant gates under the 3247-bit cap, at least 14 under the 8193-bit cap) are accepted only for acyclic isolated monomial chains whose gates are a bounded power of 3 times at most two earlier chain coordinates, with the Q gate fixed. They exclude no more general circuit, shared gate, implicit definition, different anchor scaling or other Diophantine construction. The rank census (no nonzero linear combination of the 289 residuals is affine) is a statement about the linear span, not the ideal or eliminability.
- Kind: OVERSTATED claim (if read as an unrestricted minimum)
- Outcome: accepted within the stated model only.

### R8-F10. Combined320: the old S sign involution is not a symmetry of the new anchor row
- Path: `OPT/resume-sol-review320-20261107/REVIEW.md`; also `OPT/root-review-three319/REVIEW.md`, `OPT/resume-sol-review318-20261107/REVIEW.md`
- Reviewer / date: `/root/sol_protocol_final_review`, November 7, 2026; `/root`, date not stated
- Point: with B held fixed, the source S involution does not preserve the new row 904 (B = 2 g1 + C Q tau). The reviewer's first, unextended S sign check failed. The soundness proof survives only because of the order of restoration: Q and B are discarded and the 327 (resp. 326) system is restored before any S normalization is applied. Adding coordinate 904 to the S sign set does give an involution of the whole 320 system.
- Kind: HYPOTHESIS or convention not checked (symmetry assumed from the source fails on the composed system)
- Outcome: resolved inside the review by the sequential order; no author artifact changed. The same ordering caveat is carried into the 319 and 318 reviews.

### R8-F11. Three-anchor319: residual-label collision in the composition
- Path: `OPT/root-review-three319/REVIEW.md`; verified again in `OPT/resume-sol-review318-20261107/REVIEW.md` and `OPT/resume-sol-review315-20261107/REVIEW.md`
- Reviewer / date: `/root`, date not stated; `/root/sol_protocol_final_review`, November 7, 2026
- Point: the 326 detector and the 359 anchor both use residual IDs 903 and 904 for different equations. A union by numeric ID would silently drop two equations; the review calls the naive union unsound.
- Kind: ERROR (in the assembly procedure)
- Outcome: repaired by relabelling the anchor residuals to 1903/1904 (no coordinate renamed). Later reviews check uniqueness of all IDs and that detector rows 903/904 are preserved byte for byte.

### R8-F12. Strong-H330: source depth 20 is insufficient; completeness needs Pi^39
- Path: `OPT/resume-sol-review330-20261107/REVIEW.md`; contrast in `OPT/resume-sol-review326-20261107/REVIEW.md`, `OPT/resume-sol-review318-20261107/REVIEW.md`, `OPT/root-review-three319/REVIEW.md`
- Reviewer / date: `/root/sol_protocol_final_review`, November 7, 2026
- Point: the new G2 term E^158 H0^2 needs v(H0^2) >= 160, i.e. v(f(H)) >= 80, formal depth 40. The source construction gives depth 20, which the reviewer states is insufficient. The primary h congruence must be strengthened from Pi^19 to Pi^39; compatibility is checked from gcd(Pi, M+) = gcd(Pi, L) = 1, gcd(M-, M+) = 1, gcd(M-, L) = 16, gcd(M+, L) = 1, with no extra divisibility imposed on h - 1. The 327 chain and the 320 composition inherit Pi^39. The three-group326 detector was then checked directly from the original Pi^19 construction, using the real precisions (G2 numerator relative precision 12, not 40; primary ratios 80), and all margins are positive. The 319/318/315 line therefore must not import Pi^39.
- Kind: HYPOTHESIS or convention not checked (completeness depth)
- Outcome: handled in the 330 construction and accepted; made unnecessary on the 326 branch.

### R8-F13. Pre-H valuation of H0^2 and T0 must not use the point interpretation of H
- Paths: `OPT/resume-review332-20261107/REVIEW.md`, `OPT/resume-sol-review330-20261107/REVIEW.md`, `OPT/resume-sol-review326-20261107/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt05_anchor` (332) and `/root/sol_protocol_final_review` (330, 326), November 7, 2026
- Point: the four-group and three-group packings need v(U) in 4Z and v(T0) in 16Z before H is reconstructed, so "f is the reciprocal abscissa of a point" cannot be assumed. The reviews derive S^2 = 1/f - D f on the generic squared-H branch without dividing by c + D f, so (1/f, S/f) is a curve point even when c + D f = 0, giving even v(f). On the branches U = 0 and Q_H = 0 the leaves are zero or fixed units (v = (3+2rho)/4 or (-36+16rho)/49), checked placewise. The reviews call this the "required pre-H correction" and refer to an "inherited354 correction". The 332 review also notes that the manuscript's older order-12 statement is not the current order-10 interface.
- Kind: HYPOTHESIS or convention not checked (order of inference)
- Outcome: established in each review; all three candidates accepted.

### R8-F14. Candidate369: deleting the inverse guards admits extra auxiliary solutions
- Path: `U300/01-elimination/review369/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt01_elimination`; date not stated
- Point: with the three inverse rows 1 - w0*inverse = 0 removed, a detector whose contact radical is 1 can have R = -1, forcing z = 0 and W = 0. Not every 369 solution lifts to a 372 solution. Soundness therefore cannot be obtained by invoking 372 soundness. The reviewer reran it through the local interface: at a required prime, W != 0 follows from the odd valuation of each nonconstant factor term, then w0 != 0, z != 0, T = 1/z, and B = R/(T^2 (1+R)^2). The extra solutions are harmless only because the global proof consumes no local test from a radical-1 detector.
- Kind: HYPOTHESIS or convention not checked (guard deletion changes the solution set)
- Outcome: accepted as equality of input projections only. No full-witness bijection is asserted.

### R8-F15. Original candidate392 not accepted
- Path: `U300/01-elimination/review392t/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt01_elimination`; date not stated
- Point: a different candidate392 IR (`72cc3627...`) introduced a new zero branch that needed an additional global detector argument (a conjugate-F detector proof). This review explicitly does not accept it.
- Kind: GAP or missing justification
- Outcome: left unaccepted; replaced by 392t, in which f != 0 follows from the three field equations alone (f = 0 forces v = 0, F = 0 and K0 = -1). Notes on the original are kept in `ORIGINAL392-NOTES.md`.

### R8-F16. 392t forward map needs c + D f != 0, which the local subsystem does not give
- Path: `U300/01-elimination/review392t/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt01_elimination`; date not stated
- Point: mapping a 394 solution forward leaves f d K0 = 0 with d = c + D f = f (c x + D). The reviewer states that d != 0 must be justified and that the local polynomial subsystem alone does not do so. It comes from the inherited pre-ratio exceptional-H exclusion in the 394 proof (such an abscissa is a T0-translate of +-P, f_H is then a unit at every consumed place, all radicals are 1, contradiction with the anchor and root-height bounds). The reviewer checks this is not circular.
- Kind: HYPOTHESIS or convention not checked
- Outcome: accepted. The equivalence holds on full solution sets only; no claim is made for arbitrary assignments to the old local subsystem.

### R8-F17. Squared-H390: the source one-place lemma covers squares only
- Paths: `U300/03-depth/review390/REVIEW.md`; proposal `U300/01-elimination/squared-h/REPORT.md`
- Reviewer / date: `/root/astra_quartic_opt03_depth`; date not stated. Author: `/root/astra_quartic_opt01_elimination`
- Point: replacing f, F by W = v^2 and the squares U, V creates two new branches. On U = 0: W = v = 0, V = 1/c^2. On Q = 0: U = V = -v^2 with v = 1/(c+b) = (3+2rho)/4 or v = -1/(c-b) = (-36+16rho)/49. On Q = 0 the leaves are negative squares, so `lem:v5-one-place` as stated does not apply. The proposal and the review prove the signed version (factors 1 + eps R (D_j/R^m_j)^2, eps = +-1, the nonconstant term still has odd valuation) and use it only on the classified branch, not for arbitrary U, V. Unit status of v and 1/conj(c) is argued place by place from integral building blocks, not from a unit norm. The branches are excluded by the anchor/root-height contradiction before H is reconstructed.
- Kind: HYPOTHESIS or convention not checked (lemma applied outside its stated scope; extension proved)
- Outcome: accepted. The review binds the signed argument to the actual high U factor and low conjugate-V factor in all three detectors.

### R8-F18. S-odd366: oddness of S does not by itself restore the deleted chart
- Paths: `U300/03-depth/review366/REVIEW.md`; proposal `U300/01-elimination/s-odd366/REPORT.md`
- Reviewer / date: `/root/astra_quartic_opt03_depth`; date not stated. Author: `/root/astra_quartic_opt01_elimination`
- Point: after deleting the three S odd-chart witnesses, parity of the index a is re-proved by a 3-adic obstruction (a even makes F = 2 g0 g1 a 3-unit; then u^2 - 2(w+C)^2 + 6 v^2 = 3F^2 - 2C^2 has residue 2 on the left and 1 on the right after dividing by 3). No even-index coefficient lemma is used. Oddness alone does not restore the old witnesses for both stored representations (h, j) and (-h, -j): the two representations of P give half-abscissa norm classes -1 and -7. A global sign involution on coordinates 5, 6, 7, 8, 25, 26, 27, 28, 55, 56, 57, 120, 121, 543, 544, 549 is required and was checked on every residual.
- Kind: HYPOTHESIS or convention not checked (sign normalization)
- Outcome: accepted as equality of input projections. The reverse map is existential (choice of r with A = (1+rho) r^2, possible sign flip); no witness-fixing bijection is claimed. The reviewer authored earlier components in the inherited chain.

### R8-F19. All acceptances are relative to inherited arithmetic that was not re-proved
- Path: stated most fully in `OPT/resume-sol-review330-20261107/REVIEW.md`; also `OPT/resume-sol-review326-20261107/REVIEW.md`, `OPT/resume-review359-20261107/REVIEW.md`, `OPT/resume-sol-review320-20261107/REVIEW.md`, `U300/03-depth/review366/REVIEW.md`
- Reviewer / date: `/root/sol_protocol_final_review`, November 7, 2026 (and others as listed)
- Point: not independently re-audited in any review of this batch: the decomposition E(K) = Z R0 + E[2] (Mordell-Weil input), the elliptic label/domain theorems, the contact-height bound, the pole theorem that depends on the restricted converse, preparation-zero realization, scalar/anchor bounds, the formal-logarithm result, the simultaneous-prime/separation and real-density results, and the final Lucas implications. Finite checkers are stated not to prove these. Several reviewers also note that serving-model identity is not attested and that they authored ancestor components.
- Kind: LIMITATION
- Outcome: left as standing qualifications. No review in this batch certifies the manuscript or authorises publication; every candidate here is above the below-300 threshold except the 299 symbolic system, whose mathematical reviews are outside this batch.

### R8-F20. Inventory reviews R4, R5, R6 are structural only
- Paths: `OPT/resume-review-inventory-r4-01/REVIEW.md`, `OPT/resume-review-inventory-r5-sol/REVIEW.md`, `OPT/resume-review-inventory-r6-01/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt01_elimination`, November 7, 2026 (R4); `/root/sol_protocol_final_review`, November 7, 2026 (R5); agent01, date not stated (R6)
- Point: no mathematical replay. The recorded links are direct application links, not an exhaustive dependency graph. R5 states it "cannot establish that every unrecorded mathematical use has been discovered". The 299 candidate is outside the R5 cutoff. The R6 reviewer authored the 301 elimination and the 299 compiler and gives no approval of them. The outline TeX is preparatory; no PDF build is claimed.
- Kind: LIMITATION
- Outcome: left open; final assembled exposition and release review are named as separate later decisions.

Counts by kind: ERROR 3 (F1, F2, F11); GAP 3 (F5, F8, F15); HYPOTHESIS/convention 10 (F3, F6, F7, F10, F12, F13, F14, F16, F17, F18); OVERSTATED 1 (F9); LIMITATION 3 (F4, F19, F20).


## Internal reviews, batch 9

Path abbreviations used below:

- `U300/` = `research/version15/snapshots/v15-018/quartics/quartic-299-314/sources/work/quartic-under300-20261107/`
- `V16/` = `research/version16/review/`
- `V6A/` = `research/version6/analytic-proof/`

Note: 17 of the 33 files are author REPORTs (proposals/candidates awaiting review), not reviews. They get table rows; a finding is listed for them only where the report itself states a rejected step, a necessary extra hypothesis, or an explicit unreviewed dependency.


### R9-F1. Pre-H valuation step in the 366-to-354 detector needed a repair
- Path: `U300/10-combination/review-packed348/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt10_combination`; date not stated (directory dated 2026-11-07).
- Point: The detector argument (`06-detector-next`) needs v(conj(F^2)) in 4Z for the V0 leaf before H is reconstructed. The original argument relied on the disputed interpretation of F as the reciprocal abscissa of H-P and on dividing by c+D*f. The repair proves S^2 = 1/f - D*f directly from the identity f(b+ct+Dft)^2 - c + cDf^2 = (c+Df)K + f(b^2-c^2+D), dividing only by c and f, so (1/f, S/f) is a genuine curve point even when c*x+D=0; the U=0 and Q_H=0 branches are handled by showing the fixed leaves are units away from 2, 7, 41.
- Kind: GAP or missing justification.
- Outcome: Repaired sublemma supplied by the earlier reviewer `/root/astra_bl_synthesis`, incorporated in the corrected `06-detector-next/REPORT.md`; this review supplies the missing non-author acceptance of the repair and accepts 354 and 348.

### R9-F2. Finite checks for 354/348 were replays, not new implementations
- Path: `U300/10-combination/review-packed348/REVIEW.md`
- Reviewer / date: as F1.
- Point: The full finite checks are "disclosed replays" of two earlier independent checkers, not newly authored implementations; only the repair identities were checked directly against the eight H component rows. The review does not approve a 345 implementation, a positive-anchor composition, or an ordinary-coefficient companion, and does not re-review historical arithmetic inputs.
- Kind: LIMITATION.
- Outcome: Not stated.

### R9-F3. First reciprocal299 candidate miswired the alternate cache
- Path: `U300/10-combination/review-reciprocal299/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt10_combination`; date not stated.
- Point: The original 299-variable candidate used undeclared coordinates 202/203 for the alternate cache B=F^2; the correct cache is 196 + 2*rho*197 (source rows 148/149). Detected by agent03 and the author checker, independently confirmed by the reviewer (the checker deliberately substitutes the wrong slots and confirms detection).
- Kind: ERROR (construction wiring; the review says the mathematical argument itself was unchanged).
- Outcome: First candidate remains rejected; corrected bytes `reciprocal299-r2` accepted.

### R9-F4. 299 vs 301: only input-projection equivalence, no witness bijection
- Path: `U300/10-combination/review-reciprocal299/REVIEW.md`
- Reviewer / date: as F3.
- Point: The S conversion admits auxiliary points in E(K) not in 2E(K); the equivalence proved is of rational input projections only. It is not claimed that every new S auxiliary point has a rational old square root, and the full-witness bijection established for 301 is not extended to 299. No ordinary companion approved.
- Kind: LIMITATION.
- Outcome: Stated as scope; not pursued.

### R9-F5. Auxiliary E(K) domain extension accepted only conditionally on an oriented group-law interface
- Path: `U300/10-combination/review-auxiliary-domain313/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt10_combination`; date not stated.
- Point: The extension from doubled auxiliary points to arbitrary E(K) points requires Q_i = U_i - V_i as a genuine oriented group-law equality; an abscissa equation with an uncontrolled opposite-point branch is insufficient, and the scalar root S must be the same oriented root used by its anchor. The proposal explicitly does not prove its original single biquadratic addition equation sufficient. No 307-variable artifact was reviewed.
- Kind: HYPOTHESIS or convention not checked (left conditional).
- Outcome: Left as an implementation obligation here; `review-reciprocal299` later states these formerly conditional S point, cache, ratio and orientation inputs were checked against the actual 299 equations (orientation row a*b = D*h - s*(D*f+c)).

### R9-F6. Two places where the doubled-point argument does not carry over
- Path: `U300/10-combination/review-auxiliary-domain313/REVIEW.md`
- Reviewer / date: as F5.
- Point: (a) With arbitrary torsion components the identities must be [2m]U_i=[2k_i]H and [2(m-2)]V_i=[2(k_i-2n_i)]V0; "the smaller doubled-point identities cannot simply be reused". The resulting indices k_i/2, m/2 are half-integers (integral at odd consumed primes) and global integrality of u_i is neither obtained nor needed. (b) General auxiliary points can leave the real interval where the old positivity proof of nonvanishing of the rational approximant held; a global certificate (N has no root mod 71, Q none mod 7, both primes split in K) is necessary instead.
- Kind: HYPOTHESIS or convention not checked (checked and confirmed by the reviewer).
- Outcome: Both already handled in agent05's proposal; reviewer re-evaluated the mod 71 / mod 7 certificates independently. No repair needed.

### R9-F7. Removed raw ratios in reciprocal301 are not recoverable by substitution alone
- Path: `U300/10-combination/review-reciprocal301/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt10_combination`; date not stated.
- Point: The omitted equation k*z=F follows from A*(k*z-F) = k*g + (k^2-F+D*F^3) only once A=1-D*F^2 is known nonzero. That requires the global argument (root-height/anchor contradiction, even reciprocal valuations, low test at the successful place making A a local unit; finite two-torsion A=0 excluded by the low test). "A standalone local conic with no low tests would not justify it"; the statement is about complete rational zero sets.
- Kind: HYPOTHESIS or convention not checked (checked; order of argument verified).
- Outcome: Accepted, no correction needed. The S-oriented 299 extension was outside this acceptance.

### R9-F8. shared314 review covers construction only, not the arithmetic
- Path: `U300/10-combination/review-shared314/REVIEW.md`
- Reviewer / date: `/root/astra_quartic_opt10_combination`, 2026-11-07.
- Point: "This review does not independently prove the new arithmetic argument"; that is delegated to agent05's separate review, and neither review substitutes for the other. The review notes a convention that matters to the arithmetic: the stored pair (v253, 2*v254) is F+1, not F, and the new pair is F^4/gamma160; needed for the use of F(0,0,0)=-1.
- Kind: LIMITATION.
- Outcome: Arithmetic acceptance lives in `resume-review-shared314-20261107/REVIEW.md` (not in this batch).

### R9-F9. Old direct Rémond 2022 application for the surface height lemma not accepted; replaced by a different published supplier
- Path: `research/version15/snapshots/v15-018/review/current-adoption/independent/v15-surface-source-replacement-review-h6-001/REVIEW.md`
- Reviewer / date: not named (states they authored the earlier conditional surface review); date not stated.
- Point: The surface height bound hF(B) <= hF(J) + 3(g-2)/2 is now derived from Gaudron-Rémond, Mém. SMF 176 (2023), Lemma 16.2(1) proof (K-isogenous MM variety D, product of K-simple factors, no field enlargement), plus GR 2014 CMH §2.3 and Cor. 8.4, then 2023 Thm 1.9(1). This is explicitly "not retroactive acceptance of the old direct Rémond 2022 application in frozen 8867". Rémond 2022 Cor. 1.3 and Rémond 2017 Thm 1.6 are used only through the 2023 proof; the reviewer did not compare either article's final edition, and the final 2022 Corollary 1.2 remains unread.
- Kind: GAP (source application), with a residual LIMITATION on the two indirect sources.
- Outcome: Accepted as a proposed new source application (consolidated-tex-proposal-030); not yet installed in the manuscript at the time of the review.

### R9-F10. Horizontal normalization: identities modulo the old lattice do not survive passage to a finite cover
- Paths: `V16/REVIEW.md`; `V16/current/REVIEW.md`; `V16/coverage/REVIEW.md`
- Reviewer / date: `/root/v16_correction_review`, 2026-11-11 (first two); `/root/v16_coverage_acceptance`, 2026-11-11 (coverage).
- Point: In the nilcharacter representation (v15 lines 26729-26739) the horizontal Taylor identities hold only modulo the horizontal lattice. Passing to a finite cover shrinks the lattice, and dividing arbitrary representatives by the covering integer M does not give equality modulo the smaller lattice (vectors differing by 1 agree mod Z but not mod 2Z). A lattice-correction device existed later in the proof (27557-27565) but was not applied at this earlier finite-cover step.
- Kind: ERROR in the mathematics (omitted step; "incorporation correction").
- Outcome: Repaired in `quartic_v16.tex` lines 26822-26840 (lattice-valued right multiplier making identities exact in the real vector space, fixed real lifts used in all coordinate removals) and 26905-26931 (frequency lift x/M paired with generator image M*phi(e)). Accepted; LP04, join, rank, inverse-theorem consumers reuse unchanged interfaces.

### R9-F11. Wrong source cited for the two height inequalities
- Paths: `V16/REVIEW.md`; `V16/current/REVIEW.md`
- Reviewer / date: `/root/v16_correction_review`, 2026-11-11.
- Point: The bounds hF >= -g*log(pi*sqrt 2) and hF(A) <= hF(B) + (1/2)log(deg) (lines 30661-30678) were attributed to the wrong Gaudron-Rémond paper. The supporting source is the CMH paper (DOI 10.4171/CMH/322), §2.3 pp. 351-352 and Cor. 8.4 p. 400, with hF = h - (g/2)log(pi); the Duke `gr2014` entry supports other uses only.
- Kind: ERROR (source identification; numerical bounds and field unchanged).
- Outcome: Repaired in v16 (three citation edits plus new bibliography entry). The CMH citation does not supply the 2023 product construction or its degree bound, which remain separate inputs.

### R9-F12. Tao-Ziegler results applied with a nonsquarefree modulus W = E * primorial
- Paths: `V16/REVIEW.md`; `V16/current/REVIEW.md`
- Reviewer / date: `/root/v16_correction_review`, 2026-11-11.
- Point: Tao-Ziegler "Polynomial patterns in the primes" fixes W as the squarefree primorial (Section 3; Theorem 11, Prop. 4/Cor. 3, Theorem 15 inherit it). The manuscript's modulus has a fixed extra factor E, so its use is a proof adaptation, not a literal application. The first review accepted only the corrected scope label (lines 20060-20079) and explicitly did not re-derive the divisor-sum, exceptional-prime and uniformity estimates.
- Kind: OVERSTATED claim (literal citation where an adaptation is needed).
- Outcome: Scope wording repaired in v16. The later `current` review examined the divisor-sum argument (unit residues kill divisibility at primes dividing W; Mobius divisors squarefree; W invertible at other primes; E fixed before asymptotics) and accepted reuse of the fixed-E adaptation for lines 19989-20169, valid only for fixed E, fixed polynomial system and fixed complexities, not for growing E or a uniform family of fields.

### R9-F13. Manuscript said local factors are "unchanged" where only the same uniform estimates are justified
- Paths: `V16/coverage/REVIEW.md`; `V16/current/REVIEW.md`
- Reviewer / date: `/root/v16_coverage_acceptance` (found; 2026-11-11); `/root/v16_correction_review` (diagnosis and replacement).
- Point: In the fixed-E prime-transference passage, at primes not dividing W the manuscript asserted the remaining local factors were "unchanged". Numerical identity of the local factors or of the exceptional-prime sets is neither needed nor established; what holds is that they satisfy the same uniform estimates.
- Kind: OVERSTATED claim.
- Outcome: Two-line replacement installed in `quartic_v16.tex` (no theorem, constant or parameter order changed); pre-amendment source archived at `research/version16/snapshots/pre-precision/`. The `current` review also asked that the five TZ connections bind the full 19989-20169 passage.

### R9-F14. Stated limits of the Version 16 reviews
- Paths: `V16/REVIEW.md`; `V16/current/REVIEW.md`; `V16/coverage/REVIEW.md`
- Reviewer / date: as above, 2026-11-11.
- Point: Not a new whole-proof acceptance; unchanged arguments carried forward at earlier review status. Not done: PDF build reproduction and inspection of the 549 pages; recheck of Fable's whole report; Fable's unread Kato 1999 pp. 314-318 and Ribet 1990 pp. 440-443 (covered instead by earlier four-contract and published-Ribet reviews); final-edition comparison of Rémond 2022 Cor. 1.3 / 2017 Thm 1.6; the narrow-progressions Prop. 3 proof was read only in arXiv 1409.1327v2. The defining threshold remains ineffective and the N >= 53 coefficient bound identifies no defining member. No formal verification.
- Kind: LIMITATION.
- Outcome: Recorded as open qualifications. (Fable's Bogolyubov numbering objection was withdrawn after checking published Lemma 6.4; no change.)

### R9-F15. Bridge: polynomial-forms estimate used on x-subboxes without a localization argument
- Path: `V6A/bridge-source-independent-review/REVIEW.md`
- Reviewer / date: not named; 2026-11-06.
- Point: The first draft of `gowers-bridge/bridge.tex` invoked Tao-Ziegler Theorem 15 on fixed x-subboxes, but Theorem 15 averages x over the full cyclic group. Localization had to be derived.
- Kind: GAP or missing justification.
- Outcome: Closed in the revised fragment: anchor majorant nu_0 (at most one constant shift polynomial), Theorem 15 applied to nu_0*F, nu_0*F^2 (independent m, m') and nu_0, weighted second moment of F-1 tends to 0, weighted Cauchy-Schwarz localizes to intervals; enlarged ambient interval for outputs near the endpoint. Accepted.

### R9-F16. Bridge: hypotheses added to the linear replacement and normal-form steps
- Path: `V6A/bridge-source-independent-review/REVIEW.md`
- Reviewer / date: as F15.
- Point: The linear replacement lemma now explicitly requires nonzero integer linear parts; the normal-form extension must be an integer bijection with a full auxiliary box (not a restriction to a lower-dimensional slice); the majorant must be defined on the full cyclic group with value one outside the working interval (not zero-extended); the auxiliary cutoff is eliminated before the fixed-cutoff local-cube computation; no varying-V uniformity is used.
- Kind: HYPOTHESIS or convention not checked (added in revision).
- Outcome: Incorporated in the revised bridge; accepted.

### R9-F17. Bridge: scope and source-version limits
- Path: `V6A/bridge-source-independent-review/REVIEW.md`
- Reviewer / date: as F15.
- Point: Acceptance is for the Gaussian-ray-field implication only, "not the old unrestricted arbitrary-Galois formulation; integration must apply the stated scope restriction". Dodos-Kanellopoulos Theorem 5.1 was checked in arXiv v4 only, not the publisher-typeset text. Gaussian Siegel-Walfisz and Type I/II inputs not re-proved; no PDF compilation; bibliography entries `v6gtlinear`, `v6bienvenu` still to be added.
- Kind: LIMITATION.
- Outcome: Left to integration.

### R9-F18. Affine interpolation: coefficient lemma (A2) needed integer u, v
- Path: `V6A/factorization-independent-review/REVIEW.md`
- Reviewer / date: not named; date not stated.
- Point: In `AFFINE_PULLBACK.md` the linear coefficient lemma for composing a polynomial mod 1 with u+vt was stated without requiring u, v integral. Without integrality one cannot compose p mod 1 with a real shift without choosing lifts, and the binomial matrix need not be integral.
- Kind: HYPOTHESIS missing.
- Outcome: Repaired at the reviewer's request (the application always has integer u, v); accepted.

### R9-F19. Affine interpolation: exponent choice was not explicit
- Path: `V6A/factorization-independent-review/REVIEW.md`
- Reviewer / date: as F18.
- Point: The choice of exponents ensuring the recovered character is small enough for the total-equidistribution obstruction was not pinned down. Repaired by naming C_aff = C_aff(m,d) and choosing a < min(1, c0/(2*C_aff)), sigma < min(sigma0, 1/(2a)).
- Kind: GAP or missing justification.
- Outcome: Repaired at the reviewer's request; accepted. The reviewer also confirms the factorization parameter choice (B before E(B)) is not circular and that the conjugated lattice is H_j ∩ Gamma, not the conjugate of G' ∩ Gamma.

### R9-F20. Factorization review: what is not proved
- Path: `V6A/factorization-independent-review/REVIEW.md`
- Reviewer / date: as F18.
- Point: The W-tricked application is conditional on the ideal/ordinary mean-zero estimates, the finite ray-character expansion and the prime-power error, none proved here. The centered progression hypothesis (SW), the exact arithmetic centering constant, conjugation invariance of the ray condition and the final prime-pattern application remain separate obligations. Not a new Type I/II audit; removal of the Frei-Tinková dependency does not follow from these files.
- Kind: LIMITATION.
- Outcome: Left open in this review (SW input addressed in `sw-independent-review`).

### R9-F21. Norm transfer: product-space clause assumed too little
- Path: `V6A/norm-independent-review/REVIEW.md`
- Reviewer / date: not named; date not stated.
- Point: The original draft of `NORM_TRANSFER.md` let the product-space version follow from mean-zero (or separately equidistributed) factors. That does not imply total equidistribution of the product orbit; the diagonal orbit is a counterexample.
- Kind: OVERSTATED claim (false implication in the draft).
- Outcome: Revised clause requires total delta-equidistribution of the entire product orbit as a hypothesis (application of (NT) in dimension 2m). The reviewer warns it "must not later be quoted as a proof that a Type II product orbit is equidistributed".

### R9-F22. Norm transfer: conventions and parameter inequalities made explicit
- Path: `V6A/norm-independent-review/REVIEW.md`
- Reviewer / date: as F21.
- Point: The draft lacked the ambient conventions (G connected, simply connected nilpotent; Gamma discrete cocompact; closed connected rational filtration; adapted basis; zero-dimensional case separate) and the explicit constraints 6*Cstar*kappa < c0/2, sigma < sigma0, 2*kappa*sigma < 1/4, with all enlargements of Cstar made before kappa, sigma are fixed. These are needed for the horizontal-character contradiction and the floor estimates.
- Kind: HYPOTHESIS or convention not checked (added).
- Outcome: Incorporated by the author during the review; (NT) accepted.

### R9-F23. Norm transfer: what is not proved
- Path: `V6A/norm-independent-review/REVIEW.md`
- Reviewer / date: as F21.
- Point: Does not prove product-orbit equidistribution, the Type I/II decomposition and exceptional-pair estimates, progression prime main terms, or quantitative factorization; does not establish removal of Frei-Tinková.
- Kind: LIMITATION.
- Outcome: Not stated.

### R9-F24. Siegel-Walfisz input: source and scope caveats
- Path: `V6A/sw-independent-review/REVIEW.md`
- Reviewer / date: `/root/astra_sub1000_quotients`, 2026-11-06.
- Point: Mitsui (1956) Lemma 15 is the published input, but its proof is omitted in the article; the derivation's unsmoothing from Lemma 14 was checked instead. Uniformity is for a fixed field, fixed A, fixed Gaussian ray modulus only. The TeX statement's range starts at Y=1 (extension to 0 <= Y < 1 is immediate). The review covers these steps only, not the nilsequence-to-Gowers or final chain. No mathematical gap found; a TeX escape was repaired (typographic).
- Kind: LIMITATION.
- Outcome: Accepted; Fogels not needed as a production input.

### R9-F25. Degree lower bound: Kollár's theorem checked in the preprint only
- Path: `research/version6/lower-bound/independent-review/REVIEW.md`
- Reviewer / date: not named; date not stated.
- Point: Kollár's Theorem 2 (unirationality of cubic hypersurfaces) was checked in arXiv math/0005146v1; the publisher's typeset text (J. Inst. Math. Jussieu 1 (2002)) was not accessible, so theorem numbering/wording was not compared. The accepted statement is over Q only and gives degree >= 4, no bound on the number of variables; no novelty conclusion.
- Kind: LIMITATION.
- Outcome: Accepted with no mathematical correction; suggestion to cite the arXiv link or note which text was checked.

### R9-F26. Order-39 alternative requires a larger anchor constant (author proposal)
- Path: `U300/10-combination/order39/REPORT.md`
- Reviewer / date: author not named; date not stated. Proposal, not a review.
- Point: Lowering the high test order from 40 to 39 gives log2 B < 40832434.5 from the root-height inequality, so the first Lucas height contradiction needs C raised from 3^(2^25) to 3^(2^26) (log2|s| > 50331647.5). This changes the coefficient bound and adds a squaring to the ordinary constant chain; the three-coordinate saving is not additive with the cached-eighth-power packing.
- Kind: HYPOTHESIS (changed constant needed).
- Outcome: Not built, not reviewed, not composed with positive-anchor365. `review-packed348` explicitly does not approve a 345 implementation.

### R9-F27. Smaller ordinary companions exceed the released coefficient bound
- Paths: `U300/10-combination/ordinary-reciprocal299/REPORT.md`; `.../ordinary-reciprocal307/REPORT.md`; `.../ordinary-anchor313/REPORT.md`; `.../ordinary-sparse-shared314/REPORT.md`
- Reviewer / date: author reports; not stated.
- Point: In each family only the largest lift (316 / 324 / 330 / 331 variables) meets the published bound below 2^3247. The middle lift (315 / 323 / 329 / 330) has 3250-bit coefficients, exceeding it by three bits; the smallest (314 / 322 / 328 / 329) needs 6496 bits and meets only the 8193-bit comparison cap. "Choosing it must not silently retain the old 3247-bit bound."
- Kind: OVERSTATED claim (risk flagged by the authors).
- Outcome: All three alternatives retained; all await independent transport review. ordinary-reciprocal307 is additionally conditional on its source's separate review.

### R9-F28. Elimination search: conic parametrization rejected; savings not additive
- Path: `research/version6/optimization/elimination/REPORT.md`
- Reviewer / date: author report; not stated.
- Point: Conic parametrization gives no accepted saving: its rational inverse needs a chart condition and denominator clearing can admit extra points on the excluded chart. The 20 shear eliminations (common Hessian kernel of dimension 20) may overlap a symmetric-coefficient redesign and cannot be added to another worker's count; on the merged 1,025 checkpoint the kernel is already zero and only one elimination survives (1,024). The modulo-equation pass is a bounded heuristic, not a decision procedure.
- Kind: LIMITATION (with one rejected step).
- Outcome: 1,272 to 1,251 on the baseline; later combined checkpoints supersede the count.

### R9-F29. Positive-anchor365: new Hasse-Minkowski application and new real choice are unreviewed
- Path: `U300/11-anchor-next/REPORT.md`
- Reviewer / date: author `/root/astra_bl5_models`; not stated.
- Point: The candidate replaces the indefinite anchor by U^2+V^2+6W^2 = 3g1^2 - delta^2 and applies Voight, Quaternion algebras, Thm 14.6.9 to a new four-variable form; the report says this is "not an automatic reuse of the old indefinite-anchor citation" and needs its own application row. Completeness needs a new real condition |g1| > 1/10, incompatible with the old choice of both points near O, replaced by a new quantitative estimate 0 < b <= 8450*r^-60. Only the input projection is preserved, not old solutions.
- Kind: LIMITATION (author-stated; no review in this batch).
- Outcome: Pending independent review.
