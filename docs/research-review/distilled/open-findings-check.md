# Check of the internal findings recorded as open, against Version 17

Done 2026-11-14. Every one of the 266 internal findings in Part 2 of [findings-ledger.md](findings-ledger.md) was read. The 131 whose recorded status was not clearly closed were checked against `manuscripts/quartic_v17.tex` (45,035 lines, commit `8799c581`) by reading the relevant passages and, where useful, the original records. Six reader agents did the reading, one per slice of the ledger; Claude Fable 5.2 read the passages behind the items below marked "confirmed" and assembled this file. Line numbers refer to `quartic_v17.tex`.

The earlier estimate of "about 57 open" was a text match on status lines. Reading each entry selected 131, because many are recorded as partly resolved, pending independent review, or closed only in a record and not in the text.

## Result

**One finding is a real gap in the written proof. Two more places need a short proof or a checked source. The rest are closed, on routes Version 17 does not use, or citation and wording fixes.**

| Outcome | Count |
|---|---:|
| Resolved in Version 17 | 54 |
| Route or source not used in Version 17 | 57 |
| Citation or exposition fix | 12 |
| Marked still open by the reader | 4 |
| Could not be determined | 4 |
| **Checked** | **131** |
| Scope notes ("this review did not cover X"), listed only | 21 |
| Recorded as repaired and accepted; not re-examined | 114 |

"Resolved" means the repaired text or the now-cited step was found and read. It does not always mean the mathematics was re-derived; each row in the tables below says which.

## The items that matter

**1. Tao–Ziegler at a modulus that is not squarefree (R2-F7). Real gap in the written proof. Confirmed.**
Version 17 uses Tao–Ziegler's Theorems 11, 13, 15 and Corollary 3 at W = E × (primorial), with E a fixed extra factor. The published statements assume a squarefree primorial. The manuscript says correctly that this is an adaptation of their proofs (2018, 25167–25171). The adaptation is not written out: lines 25171–25179 assert that "the divisor-sum local factors satisfy the same uniform estimates", and line 2022 points to a review file for the derivation. Lines 24987–24992 and 25036 still say the published results "apply unchanged". The idea is routine (for a unit residue, the conditions at primes dividing W are vacuous whatever the exponent), and nothing suggests it is false. It should be proved in the manuscript, or reduced to the published squarefree case.

**2. The CM congruence (H4) for an arbitrary old conductor (R3-F20). Needs a short proof or a citation. Confirmed.**
Lines 8980–9000 give a six-sentence sketch. Howard is cited only for his conductor subfamily. The detailed section at 35236–35285 covers maximal orders and says so at 35285 ("No corresponding assertion for nonmaximal orders or arbitrary conductors has been inserted"). The argument is local at the inert prime, where the order is maximal, so the conclusion is the standard one. This is the same passage flagged in [flagged-items-check.md](flagged-items-check.md); a second reader judged it needs more than one sentence.

**3. Pan's modularity theorem and its ancestors (R5-F7, R5-F8, R1-F11). Disclosed source limitation, not a gap in the paper's argument.**
Version 17 applies the published statement (Calegari, ICM 2022, p. 624) and checks its hypotheses (2534–2540). It states that the final journal text of Pan's paper could not be obtained and was not compared with the arXiv version (2540, 4713, 4719). Someone with journal access should confirm the published statement.

**4. PR 30 "complete proof not accepted" (R1-F29). Three separate residues.**
- Rémond 2022's final text was not compared (3296–3300). The dependence is now indirect, through Gaudron–Rémond 2023.
- The manuscript says in several places that its Part I bridges are author proposals awaiting non-author review (2408, 2414, 2460, 2500, 2634). These are statements about review status and belong out of the paper; the underlying review has not happened for Versions 16–17.
- Text-conversion artifacts remain in prose, for example `\(\text{has}72/2=36\)` at 2457 (confirmed) and page numbers set as subscripts at 2620 and 2910. No formula was found affected. An exhaustive pass has not been done.

**5. Could not be determined (4).** In each case the text and citations are present and nothing wrong was found; what is missing is a check that the suppliers deliver exactly what the consumers use.
- R1-F01: joins between the arithmetic suppliers and their consumers (needs a full read of 7669–11826 and 18438–22642).
- R2-F39: the 127 quotient-domain obligations for the 962-variable predecessor polynomial in Part II. The point-quotient lemma (16973–16997) was verified; the obligations were not enumerated.
- R4-F5: inputs the Milne review did not cover (Edixhoven, Kolyvagin, Kato, Poonen–Stoll, Nekovář); the cited theorems were not opened.
- R4-F17: pending RC rows; row 12 was checked and is correct, the others only read.

## Fixes for Version 18

Mathematics:
- Write out the Tao–Ziegler adaptation (25167–25179) and correct "apply unchanged" at 24987–24992 and 25036.
- Give a short proof or a reference for (H4) at 8980–9000 for arbitrary old conductor.

Citations and sentences to add:
- 6635–6638: cite local reciprocity for β⁴ = 1 (confirmed uncited).
- 9076–9086: say the model is minimal and cite Silverman VII.2.1–2.2.
- 5742–5749 and 2606: cite the polarization-pairing determinant (Milne 1986 §16).
- 22192–22199: cite the split-cubic halving criterion.
- 8876, 9003–9015, 9135–9137, 9593–9605: add a ring-class-field reference (for example Cox); there is none in the manuscript.
- 6585–6586: cite Milne 1986 Prop. 12.9, as at 13450.
- 35770: add Rémond 2017, Theorem 1.6, to the bibliography.
- 35244: say the Frobenius follows Silverman's printed convention.
- 12168: say the three arguments of each power call are natural-valued.
- 29823–29827 and 30069–30076: say the all-limit convention is stronger than the published definition.
- 5793–5804: name the Allen–Newton–Thorne correction and cite the Pan supplements, which are in the bibliography but never cited (44781–44795).
- 13370–13378: repeat the Brauer citation given at 6513–6515.
- 19021: "derived local control" is asserted without proof or citation.

Cleanup:
- Delete the superseded Li sentence at 5785–5789 and the uncited `berger2002` entry.
- Remove review-status statements and file paths from the text (2408–2634 and similar).
- Do an exhaustive pass for text-conversion artifacts.

## Limits of this check

- Published sources were almost never opened. "Resolved" by a citation means the citation is present, not that the source was re-read.
- The 114 findings recorded as repaired and accepted were not re-examined.
- Three statements about the 299/314-variable polynomial rest on coefficient data that cannot be inspected from the manuscript (28168, 28376–28386, 28800–28811).
- Version 17 contains the whole Version 16 body after the 214-variable Part I, so findings about the earlier chain apply to live text.
- This is a check that old findings were dealt with. It is not a review of Version 17.

## Per-slice tables


### Batch 1

#### Batch 1 (ledger lines 145-361): status of non-closed findings in Version 17

Slice: 37 entries (R1-F01 to R1-F37). Selected as not clearly closed: 17
(F01, F02, F03, F11, F14, F16, F17, F19, F20, F21, F24, F27, F29, F30, F31, F35, F37).
Not selected (ledger records a repair or acceptance): F04-F10, F12, F13, F15, F18, F22, F23, F25, F26, F28, F32, F33, F34, F36.
Of the 17, three (F27, F31, F35) are treated as scope notes; the specific items inside them that could be checked are noted.

Line numbers are those of `quartic_v17.tex`. "Checked" means I followed the mathematics myself; "text only" means I confirmed the passage exists and says what is described, without re-deriving it.

#### Table

| ID | Topic | Verdict | Basis (V17 lines) | Not verified |
|---|---|---|---|---|
| R1-F01 | Arithmetic slice: supplier joins not accepted | COULD NOT DETERMINE | Each named join is present in the text: visibility (O.8) defined 21110-21137 and cited by its consumers at 8609-8614, 21881-21886, 22554; omission/primary isolation for the same form and depth 8596-8607; Kato 1999 index set and both cases of (0.1.1) at 18623, 18644, 18881-18918, 18963-18966; de Rham descent with Tate dual and weights 0,-1 at 5640-5745 (also 2536); compiler witness domain 12140-12173. V17's own carry notes C05, C07, C13 (3325, 3336, 3348) say these are carried at earlier scope with fresh acceptance pending. Text only. | Correctness of each join; the simultaneous-address construction and the "stage chosen before its primes / companion K and determinant precision fixed first" ordering were not traced. |
| R1-F02 | Dodos-Kanellopoulos Thm 5.1 final text not compared | ROUTE NOT USED | No occurrence of "Dodos", "Kanellopoulos" or a DK bib key anywhere. The relative inverse step now cites Green-Tao Prop. 10.1 with the locally proved GI(k): 24566-24595, 24815-24835, 28933-28990. | Whether GT Prop. 10.1 is applied correctly (later analytic review says yes at V16 scope). |
| R1-F03 | BHB final-publication comparison | RESOLVED IN V17 | Bib entry 44301-44308 records comparison of Lemmas 2.1, 4.1 and Section 4 with the final text pp. 150, 155-158 and the notation slips. Record `research/version14/evidence/final-source-bhb/FINAL-COMPARISON.md` read: final PDF supplied 7 Nov 2026, contracts match. Statement of both lemmas in V17 at 22875-22897 agrees with that comparison. | I did not see the BHB paper itself. |
| R1-F11 | V5 source versions (Frei-Tinkova, DK, Pan, Yuan) | ROUTE NOT USED (FT, DK); residual on Pan | FT: "no theorem from that work is assumed" 22651-22653, 23608-23619, 24300, 25085; bib 44310-44317 still says no final version verified, which is harmless. DK: absent. Yuan: published Chinese article pp. 228-231 is the cited text, 12842-12843, 15514-15520, bib 44709-44720. Pan: the supplier is now Calegari's published ICM statement, 2540, 5794-5804, 15508-15511; V17 still says the final JAMS body of Pan was not compared (2540, 2634). | Calegari's statement itself; the eight "text-identical foundational blocks". |
| R1-F14 | V6 assembly: Kollar text; Gowers/boundary bridge | ROUTE NOT USED (Kollar); bridge reviewed later | No "Kollar" in V17. The degree-four lower bound (17922-17960) now rests on Muller 2002 and Colliot-Thelene-Salberger 1989. The relative-inverse/boundary bridge (24566-24835, 24935-25062) is covered by the later analytic review record (`research/quartic214-protocol-d-progress/reviews/analytic/REPORT.md`, read), at V16 scope. | I did not re-derive the bridge; the 962-variable convolution was not rerun. |
| R1-F16 | Tail proposition: range of cutoff L | RESOLVED IN V17 | Prop. 23023-23036 states "there are L_* >= 2 ... uniformly for L >= L_*"; proof fixes L_* above the exceptional primes of the medium-prime bound 23042. Expanded steps present: Rankin bound 22973-22983, R=0 locus 22933-22935, t=-2 chart 22955-22958, content after lattice substitution 23001-23005. Checked the proposition's proof (23038-23083) for consistency with Lemma 22797-22803 and 22899-22909. | The medium-prime lemma's own proof. |
| R1-F17 | Tail audit scope (BHB/BL finals) | RESOLVED IN V17 | BL bib 44293-44299 and BHB bib 44301-44308 both record final-text comparison. | Prime-pattern lower-bound proposition (scope note in the original). |
| R1-F19 | O3: final Dospinescu / Breuil-Mezard comparisons | ROUTE NOT USED | No occurrence of Dospinescu, Mezard, Paskunas, CEGGPS. Modularity uses the published statement in Calegari ICM 2022 p. 624; 5794-5804 states Pan's proof inputs (ordinary inputs, local Hu-Tan rings) are not reproved and the GL2-type/Serre reconstructions "are not inputs". | - |
| R1-F20 | Reflection formula signs | RESOLVED IN V17 | 11980-11986: "U_n = (-1)^l eps U_j (mod v). The value sign need not equal the index sign." Soundness 12007-12014 uses the two signs separately. Checked, including the ledger's example b=4, m=2, n=3 (l=1, eps=-1, sign +1, U_3=15=1 mod 14). | - |
| R1-F21 | Power template: natural P,Q,R at every downstream call | EXPOSITION OR CITATION FIX | 12160-12168 explains that the power-value recipe returns the template's polynomial value, with 79 private natural witnesses per block and only the parent root set to zero; 12155 says natural guards are on source variables. No sentence states that the three arguments of each of the 15845 power calls are natural-valued in the natural polynomial, which is what the N^3 equivalence at 12026-12041 needs. Suggested addition after 12168. | I did not inspect the compiler artifacts. The repository blueprint `compiler/natural/formulas/hierarchical-calls.md` treats the natural-argument case formally, which suggests the fact holds; that is inference. |
| R1-F24 | Height chain: R=D (prime catalogue, formal group) not audited | RESOLVED IN V17 | Prop. "Literal cutoff" 12367-12435 proves R=D in full. Checked: prime count per class > X/(2W^4), H_cat <= X^{22W}, log2 N_s < 2^2054; odd-place formal valuation >= 2+8v_p(N_s); dyadic valuation >= 6+16v_2(N_s) with loss 3; M_0 <= N_s^10; c_* < 2^(2^2059) < D. | The literal S03 constants, the bounds 2^(2^8008) < D < 2^(2^9010), and the cited explicit progression estimate (bmor). |
| R1-F27 | PR30 first review: coverage | scope note | Checked only: M1 normalization and degree-sum misprints are fixed (2508, 2812); "no effective N_0" is stated 105-107, 3348. | Everything else in the list. |
| R1-F29 | PR30 follow-up: complete proof not accepted | STILL OPEN | See paragraph below. | - |
| R1-F30 | D210 geometry/modularity: source closure | RESOLVED IN V17 for the two named mathematical points; rest is scope | [L:Q] divides 576: 13089-13102 (checked: Galois group lies in the centralizer of a regular action of a group of order 576). B-linear normalizer isogenies: 13324-13341 (checked). Milne 1986 Prop. 12.9 now recorded as visually read, 4503, used at 2568; Stacks 0A18 cited 2432, 12921. | The listed primary sources (PEL classification, Faltings, Scholze, Shimura twist, Serre 1967, etc.). |
| R1-F31 | V16 foundation: ranges unread | scope note | TZ changed-modulus use is disclosed as a proof adaptation, 2018. | Unread RC/Kato/Gaussian/GI ranges; parity and forward-rank inputs (table 18392-18412). |
| R1-F35 | Analytic lane scope | scope note | BL/BHB final comparisons recorded (44293-44308); n=5 use at 22763-22767. | GI supporting range. |
| R1-F37 | Geometry lane: Buzzard pp. 591-592, Yuan pp. 230-231; M1 assumed | RESOLVED IN V17 | Buzzard pp. 591-592 and Yuan pp. 230-231 are the cited locators with pinned hashes: 2425, 2438, 12838-12843, 13016-13018, bib 44401-44404, 44709-44720 (text only). M1 identity: 2506-2514 and 13353-13360; checked that a_sigma = D(mu_sigma)^(-1/4) with D(c mu) = c^4 D(mu) gives a_sigma a_tau / a_{sigma tau} = 1/|c|. | That an independent reviewer has inspected those pages; M3-M6 beyond the Deligne-Serre note at 5780-5791. |

#### STILL OPEN

**R1-F29.** Three things in this entry survive in Version 17.

1. Remond 2022 final text. V17 says in its own words that the published body of Remond, "Proprietes de la hauteur de Faltings" (Ann. SNS Pisa 23, 2022) was not compared: subsection "Remond publication-version check remains open" 3296-3300, catalogue 4318, 4357, 4424, and 3125, 3174-3178. The dependence is now indirect. The operative argument (3167-3238, and 35749-35775) uses the construction in the published proof of Gaudron-Remond 2023 Lemma 16.2(1) and Theorem 1.9(1); that proof cites Remond 2022 Cor. 1.3 and Remond 2017 Thm 1.6. The old route H3 that used Remond's inequality directly is marked superseded at 3112. I checked the averaging step in 3200-3222 (sum of r heights at most H_J gives one at most H_J/r; isogeny-degree transfer) and found it sound. I did not see GR2023.
2. Acceptance status. V17 itself states that the Part I bridges are author proposals awaiting non-author review and that its dated acceptance statements are not acceptance of this TeX: 186-196, 2042, 2318, 2414, 2634, 3348. Nothing in the manuscript closes "complete assembled-proof acceptance".
3. Serialization. The formula errors F1-F11 are repaired where I looked (2508, 2812, 2830, 2852-2854), but prose artifacts of the same conversion remain in Part I: the pronoun "I" set as math in 13 places (e.g. 3247, 3257, 3298); page numbers set as subscripts, "Li's actual final \(p_{296}\) formula" 2620 and "printed \(p_{5}\)" 2910; "Pan \(v_{2}\) Theorem 1.0.4" 2540; "\(\text{has}72/2=36\)" 2457; "\(\text{AUTHOR}_{{\text{FREEZE}}_{001}}\)" 2318. None changes a formula, but the exhaustive serialization pass the entry asked for has evidently not been done.

#### COULD NOT DETERMINE

**R1-F01.** The original reviewer accepted lines 1-5930 of V13 but not the joins to suppliers outside that slice. In V17 every supplier and consumer named in the entry is present and cross-referenced (lines in the table), so no join is textually missing. I did not verify that each supplier delivers exactly what its consumer uses (same form and depth, same index domain, ordering of choices), and I found no later record of a parent join decision that is a mathematical check rather than source-dependency coverage (`docs/manuscript-revisions/version14/final-coverage/FINAL-PROTOCOL14-REVIEW-002.json` is explicitly coverage only). V17's own notes C05, C07, C13 (3325-3348) describe these as carried at earlier scope. What blocked a verdict is volume: confirming the joins means reading the restricted-converse chain 7669-11826 and appendices 18438-22642 in full.

#### Side observations (not ledger findings)

- `berger2002` (bib 44408-44411) is no longer cited anywhere; the de Rham to potentially semistable step it served (R1-F22) is unnecessary now that the input is Calegari's "geometric" statement (2540, 5794-5796).
- (LR1) at 13314-13317 prints an inequality, while Part I uses divisibility of [E:Q] (2479, 2588, 3049, 3455-3458). Line 3458 notes the strengthening; 13552 needs only the inequality.

### Batch 2

#### Batch 2 (ledger lines 362-644): status of non-closed findings in Version 17

Slice: 39 findings (R2-F1 to R2-F39). Selected for checking: 22. Pure scope notes: 2. Not selected because the ledger records them as clearly closed: 15 (F3, F4, F6, F10, F11, F12, F14, F16, F22, F23, F30, F31, F32, F34, F38).

Line numbers are those of `quartic_v17.tex`. Part I (the 214-variable construction) is lines 83-5135; Part II (the retained Version 16 foundation) is lines 5136-45035.

Counts: RESOLVED IN V17 6; ROUTE NOT USED 13; EXPOSITION OR CITATION FIX 1; STILL OPEN 1; COULD NOT DETERMINE 1.

#### Scope notes (no further work)

- R2-F8: the historical review was not a blind reconstruction and did not reread the Fable audit, PR30 appendices or 1,313 file bodies.
- R2-F13: the C10 review was interactive, not blind; it concerns the CEGGPS route, which V17 does not use (see F15-F29 below).

#### Table

| ID | Topic | Verdict | Basis (V17 lines) | Not verified |
|---|---|---|---|---|
| R2-F1 | Unit-group stars lost in M3 paragraph | RESOLVED IN V17 | Line 2552 now prints `\prod Z_{p}^{*}` twice and `(Z/rZ)^{*}` twice, matching the four stars in `modularity.md:57`. Lines 2506 and 2516 (`Q*`, `Q_{p}^{*}`) also match the source. Spot inventory of starred math in six other Part I sources (height-metric, height-evaluation, height-supplier, geometry-carry, primary-source-bridges, height-averaging): `p_{*}` 2910, `j_{*}` 2708, `R_{*}=B_{*}` 2376 are present; the remaining source stars are Markdown emphasis. | The PDF. The inventory was a pattern search on seven source files, not a full source-to-TeX comparison. |
| R2-F2 | Li Theorem 5 cited for existence | RESOLVED IN V17 | New paragraph 5769-5784 makes Deligne-Serre 1.6-1.9 the supplier and says no existence claim rests on Li's Theorem 5; Part I 2554-2556 gives the same extraction. I followed the argument (primitive constituent of the twisted eigenform, good-prime operators commute with degeneracy maps). The old sentence is still printed at 5785-5789 as "historical", so deleting it would be cleaner. | Deligne-Serre section 1.9 itself was not opened; I relied on recollection of its content. |
| R2-F5 | a_sigma constant versus cocycle law | RESOLVED IN V17 | 2506-2512 and 6454-6475 define a_sigma = D(mu_sigma)^(-1/4) with positive real root. I rechecked: D(c mu)=c^4 D(mu) gives a_sigma a_tau / a_(sigma tau) = 1/|c|, and the identity element gives a_1 = 1. Companion repair (all complete components, full residue degrees) is at 2784 and 3004. | Extension-subscript and coordinate-index repairs (PR30 F3-F5) were not traced individually. |
| R2-F7 | Tao-Ziegler at modulus with a fixed extra factor | STILL OPEN (narrowed) | See paragraph below. Lines 2016-2028, 25159-25179, 24987-24992, 25036. | Whether the adapted proofs go through. |
| R2-F9 | RC/Kato lane: sources not freshly read | RESOLVED IN V17 for the one named citation; otherwise scope note | Milne ADT I.4.10 and I.5.1 are used at 10607-10613. I rechecked the arithmetic: for the 2-dimensional F_2-module over an imaginary quadratic field the Euler characteristic is 4/16, so h0-h1+h2 = -2, and with no real place H^r vanishes for r>2. This agrees with the text. | The Milne statements were recalled, not reread. The unread RC ancestor passages and the other listed sources (open image, Shimura/Faltings, parity, Kolyvagin, Edixhoven, Gross-Zagier) were not examined. |
| R2-F15 | BP Cor. 9.11 and the BM 5.2 central character | ROUTE NOT USED | V17's modularity input is the published prime-five statement cited at 5614-5616, 5793-5801 and 15508-15512 (Calegari ICM p.624; Pan as proof source), with the explicit disclaimer at 5797-5800 that Pan's inputs are not reproved. Searches with zero hits in the whole file: CEGGPS, Caraiani, Colmez, Emerton, Kisin, Paskunas (all spellings), Henniart, "completed cohomology", Jacquet, "locally algebraic", patching, Mezard. "Breuil" occurs only as BCDT (6939, 7711, 44543). | Nothing was checked about the published theorem's own proof. |
| R2-F17 | Finite projectivity of residual projective cover | ROUTE NOT USED | Same searches. | Same. |
| R2-F18 | "Jacquet dimension two" means J_0 | ROUTE NOT USED | Same searches. | Same. |
| R2-F19 | Principal-series self-Ext in SC08 | ROUTE NOT USED | Same searches; "principal series" occurs only in the Waldspurger context (19695, 21527). | Same. |
| R2-F20 | CEGGPS determinant-exponent inconsistency | ROUTE NOT USED | Same searches. | Same. |
| R2-F21 | Final CEGGPS edition never obtained | ROUTE NOT USED | Same searches. | Same. |
| R2-F24 | Auxiliary CEGGPS route conditional; C10 open | ROUTE NOT USED | Same searches. | Same. |
| R2-F25 | Sources depend on the disputed supercuspidal identification | ROUTE NOT USED | Same searches; "supercuspidal" occurs only at 19703, 19744, 21505 (Waldspurger local conditions). | Same. |
| R2-F26 | Source-closure supplier checks left open | ROUTE NOT USED | Same searches; Hu-Tan is mentioned only in the disclaimer 5798-5800. | Same. |
| R2-F27 | Emerton draft det^b versus det^(b+1) | ROUTE NOT USED | Same searches. | Same. |
| R2-F28 | Tame-level multiplicity 6.4.3 to 7.4.2 | ROUTE NOT USED | Same searches. | Same. |
| R2-F29 | Existence of the weak map | ROUTE NOT USED | Same searches ("weak map", "Hecke spectrum": zero hits). | Same. |
| R2-F33 | Four owner conclusions unsupplied | RESOLVED IN V17 (as printed mathematics) | Sign normalization 6454-6484 (rechecked, see F5). All-prime realization 6574-6599 and 13426-13494. All-prime absolute irreducibility 6552-6557 and 13407-13416 (I rechecked: commutant M_2 of r+r plus semisimplicity forces scalar endomorphisms of r, stable under coefficient extension). Comparison/conductor 6600-6604 and 13505-13544 (Carayol). | The 36 unresolved record "obligation fields" and the later records beta004, B005, four-H5-joins002 were not opened. Carayol 1987 was not read. |
| R2-F35 | Residual ledger: what the projections do not cover | ROUTE NOT USED for Yuan Lemma 2.1; otherwise scope note | 13200-13202 and 15514-15517 state that Yuan's coarse Lemma 2.1 and Theorem 2.2 are not used. The restricted converse has a full printed proof (7668-22630). Conductor-one reduction premises are written out with citations at 35236-35285. Full Selmer corank convention at 7673-7675. | I read the conductor-one section once and did not verify it; the restricted-converse proof was not checked. |
| R2-F36 | All-prime irreducibility assumed a quadratic field E | RESOLVED IN V17 | Both constructions use a splitting field and matrix units, with no quadratic E: beta family 6542-6557, b family 13401-13416. Argument rechecked as in F33. | The successor record `all-prime-irreducibility-matrix-units-002` was not opened. |
| R2-F37 | Beta compatibility: coefficient field, ell != p, citation | EXPOSITION OR CITATION FIX | Common finite coefficient extension stated at 6575-6577; restriction to ell != p at 6577 and 6585-6586; arithmetic p-Frobenius at 6578-6581; the p=3 case is covered by "choose ell != p" at 6600. The b family (13450) and Part I (2568) cite Milne 1986 Prop. 12.9, p.125 and keep the division by m (13451) and the factor 1/2 (13462). The beta passage 6585-6586 asserts independence of the Tate prime with no citation: add Milne 1986 Prop. 12.9 there. No "Proposition 10.20" citation remains anywhere. | Milne Prop. 12.9 was not reread. |
| R2-F39 | Finite replays do not give denominator nonvanishing | COULD NOT DETERMINE | See paragraph below. Lines 16973-16997, 17167-17168, 17726-17745, 17879-17892. | 126 of the 127 obligations. |

#### STILL OPEN

**R2-F7 (Tao-Ziegler at the fixed extra factor).** The overstatement itself is repaired: 2018 and 25167-25171 now say that Tao-Ziegler's Theorem 11, Corollary 3, Theorem 13 and Theorem 15 are used through adaptations of their proofs, not as literal applications, because the modulus is W = E times a primorial with E fixed and not squarefree. What is still missing is the adapted proof. The manuscript's entire justification is the seven lines 25171-25179: unit residues kill divisibility at primes dividing W; "at the remaining primes the divisor-sum local factors satisfy the same uniform estimates"; E is absorbed in coefficient bounds. The second clause is asserted, not derived. The fuller derivation is said at 2022 to live in an external review file (`research/version16/review/current/REVIEW.md`), which is not part of the manuscript, and 2028 says the alternative progression-dilation reduction is not adopted and was never written out. Lines 24987-24992 and 25036 still read "applies unchanged ... use the published Tao-Ziegler Theorem 11 and Corollary 3" and "Theorem 15 ... applied to", which is consistent only if read through the adaptation paragraph. I did not check whether the adaptation is correct; I only confirmed that the printed text does not prove it. To close: write the changed-modulus versions of the correlation and polynomial-forms estimates into the manuscript, or give a reduction to the published squarefree case.

#### COULD NOT DETERMINE

**R2-F39 (962-variable checker's 127 quotient-domain obligations).** The limitation says the finite replays prove polynomial identities only and leave denominator nonvanishing to the manuscript. V17 does print domain arguments for the 962-variable predecessor: Lemma "Domains of the point quotients" (16973-16997), the reciprocal-nonvanishing remark (17009-17010), the blanket statement at 17167-17168, the weight-quotient paragraph (17726-17745), and the proof at 17879-17892, which restores "every deleted quotient by its proved nonzero denominator". I checked the point-quotient lemma and it is correct (eta = 0 contradicts the slope equation; d and -d have norm 7 so are not squares in Q(sqrt 2)). I did not enumerate the 127 obligations or match each to a printed argument, so I cannot say all are covered. This concerns a predecessor polynomial in Part II, not the 214-variable polynomial of Part I, whose own domain condition (q nonzero) is stated at 2054. The 4973 and F8 items in the same finding were not examined.

### Batches 3 and 4

#### Ledger lines 645-979 (internal reviews, batches 3 and 4) checked against Version 17

Slice: 45 entries (R3-F1..F20, R4-F1..F25). Selected for checking: 21. Scope notes: 5. Recorded as closed and not re-examined: 19
(R3-F2, F4, F5, F6, F7, F10, F15; R4-F1, F2, F3, F6, F7, F9, F13, F14, F18, F19, F21, F25).

Verdict counts (21 selected): RESOLVED IN V17 13; ROUTE NOT USED 1; EXPOSITION OR CITATION FIX 5; STILL OPEN 0; COULD NOT DETERMINE 2.

All line numbers are in `quartic_v17.tex`. "Checked" means I followed the mathematical step myself; "read" means I confirmed the text is there without verifying it; no published source was opened.

| ID | Topic | Verdict | Basis (V17 lines) | Not verified |
|---|---|---|---|---|
| R3-F1 | G_Q-stability of idempotent factor; End = B assumption | RESOLVED IN V17 | Lemma at 5588-5610 defines rho_5 = t_sigma mu_sigma o sigma on all of G_Q commuting with B, so the matrix-unit factor is G_Q-stable (checked). End^0 = B or M_2(k) and field of definition L: 6355-6383. Absolute irreducibility via Faltings: 5620-5636, 13405-13416. | Faltings 1986 Thm 1 page reference; the Hodge-theoretic dichotomy at 6377-6383 was read, not re-derived. |
| R3-F11 | Silverman reduction kernel without minimal-model hypothesis | EXPOSITION OR CITATION FIX | 9070-9090 (H10): the remaining cocycle is said to lie in "the formal group", citing only IV.3.2(a). No statement that the Weierstrass model is minimal over F and stays minimal over the unramified F', and no citation of VII.2.1-2.2 here (no occurrence of "minimal" in 8860-9500). The qualifier exists elsewhere (7024-7026). Add one sentence plus the VII.2.1-2.2 citation at 9081-9084. | The other undischarged items named in the ledger (class-field reciprocity, eigenquotient, Neron foundations, torsion exponent) beyond what is listed under R4-F22/F23. |
| R3-F12 | beta^4 = 1 on O_F^*: local norm functoriality source | EXPOSITION OR CITATION FIX | 6635-6638: "local reciprocity and the norm map give beta^4=1" with no citation at all (neither the wrong Milne V.3.3 nor a replacement). Mathematics checked: chi restricted to inertia at 2 is the mod-4 character, so chi^2 = 1 on Z_2^*, and beta^4 = chi^2 o N on O_F^*; (U^{e+1})^4 = U^{3e+1} is correct. Add a citation for norm compatibility of the local reciprocity map (the bibliography already has Serre's 1967 Cassels-Frohlich chapter, 44468-44470; whether its section 2.4 states it is from memory, not checked). | The source statement itself. |
| R3-F13 | Final completeness consumed reverse half-chart node N08 | ROUTE NOT USED | Defect was in a dependency record. V17 has no N08 node or dependency graph (searched "N08", "half-chart", "forgetting map"; only 16553 and 28125, neither a dependency claim). | That the project's graph files were updated. |
| R3-F14 | Residue cohomology: all positive degrees vs H^1 | RESOLVED IN V17 | 9083-9086: "A normal basis makes this an induced module, so its positive-degree cohomology vanishes." True by the normal basis theorem; only H^1 is consumed in the successive correction (checked). | Convergence/Lang step at 9076-9088 read only. |
| R3-F16 | Obsolete coefficient bound; no replay rerun | RESOLVED IN V17 | 5184, 27936-27939, 28856-28860 give 2^6495 <= 3^4098 + K_0 < 2^6496 (checked: 4098 log2 3 = 6495.2). The 2^3247 bounds at 25474, 26108, 27038, 27903 belong to other polynomials (3^2048). | No finite replay or coefficient table was rerun. |
| R3-F17 | Kato carryforward: five stronger premises | RESOLVED IN V17 | Hypotheses of Kato 13.4(2) verified in text 18829-18853; unipotent in G_{Q^ab} and absolute irreducibility over Q(mu_{2^infty}) 18876-18896 (checked); both-sign non-torsion 18829-18843 (read); local control 19018-19025 (asserted, read); restricted converse stated 6845, proof 7669-22628. | Kato 13.5(2), Kato 1999 Thm 0.8 statements; the "derived local control" sentence has no proof or citation at 19021. |
| R3-F18 | 299/314 composition is not the announced theorem | RESOLVED IN V17 | Theorem 27922-27940 with proof section ending 28869 ("establish Theorem"); constant chain 28813-28828 checked (e_13 = 2^25). | The body of the proof 27949-28812. |
| R3-F19 | Degree/corollary applications unowned | RESOLVED IN V17 | Degree obstruction 17921-18093 with CTS Prop. 1.3 and integral Hilbert irreducibility (Muller) cited; argument read in full and found coherent. Corollaries 12548-12680 cite Mazur pp. 165-166 and Matiyasevich Basic Theorem with the four-squares conversion. | Source statements; HIT is cited to the introduction of a secondary paper. |
| R3-F20 | Generic-conductor CM congruence (H4) | EXPOSITION OR CITATION FIX | 8980-9000: congruence for arbitrary old conductor is argued in six sentences with no citation except Howard (13), which the text says covers only his subfamily. The detailed section 35236-35285 treats maximal orders and isogenies of degree prime to q only and says so (35285). I checked that the sketch is the standard argument and its conclusion is correct (degree-ell isogeny from a supersingular curve has kernel ker Frobenius; residue field F_{ell^2}). Needs a citation or a short proof of: extension of the ell-isogeny to good models, uniqueness of the order-ell subgroup scheme, transport of the N-level structure, extension of pi. | Not a line-by-line proof; no source consulted. |
| R4-F4 | Brauer reciprocity citation | RESOLVED IN V17 | 6503-6515 has the order-two local argument and cites Milne ADT I.1.6(b) and proof of II.2.1, p. 164. The repeat at 13370-13378 is still uncited (optional cross-reference). | Milne page content. |
| R4-F5 | Milne review: inputs not covered | COULD NOT DETERMINE | See paragraph below. | |
| R4-F10 | Semisimplicity of U_{f,3}; bind absolute irreducibility of r_3 | RESOLVED IN V17 | 13486-13493 uses the finite-length deduction; absolute irreducibility of r_ell for every ell is proved at 13405-13416 (checked). | Classical trace realization of f at ell. |
| R4-F11 | Quasi-isogeny degree imports; End = B obligation | RESOLVED IN V17 | D(u) = deg([m]u)/m^4, independence of m, D(cu) = c^4 D(u): 6457-6468 and 13352-13357 (checked). End = B: as R3-F1. | Rationality/splitting of the cocycle is handled by the sign cochain 6516-6523 (read). |
| R4-F12 | det V_5 = cyclotomic^2 and finiteness of alpha | EXPOSITION OR CITATION FIX | 5742-5749: finiteness of alpha now derived (alpha^2 = 1 on G_F; checked), but "the polarization pairing gives det V_5(A) = epsilon_5^2" has no citation; same at 2606. Add Milne 1986 section 16 (Lemma 16.2(e), Prop. 16.6 per the review). | Source pages. |
| R4-F15 | Anchor constant 3^(2^24) vs 3^(2^25) | RESOLVED IN V17 | Current chain uses C = 3^(2^25) with s in 2*3^(2^24-1)Z consistently: 15540, 15564, 16109, 26390, 26496-26500, 27930-27931. Historical 3^(2^24) at 14267-14343 is the base compiler. | HEIGHT-LUCAS scalar/contact-height inequalities. |
| R4-F17 | RC pending rows 4, 6, 12, 17, 18, 21 | COULD NOT DETERMINE | See paragraph below. | |
| R4-F20 | 2-adic Kato use; statement-vs-proof bindings | RESOLVED IN V17 | 18876-18896 applies Kato 1999 Thm 0.8 under 0.6(ii) and verifies it; 18957-18989 compares the two cohomology conventions; full H^2 is paid for by the local cone at 18991-19010. | Kato 1999 statement. |
| R4-F22 | Unreviewed proposals: odd-theta rows; class-field sources | EXPOSITION OR CITATION FIX | (a) Split-cubic halving criterion used at 22192-22199 without citation; computation for roots 0, ell, -3ell checked. lambda_M Frobenius invariance proved 20119-20128 and 20170-20193 (checked). CM/Atkin-Lehner applications 35236-35285, 21030-21060 (read). (b) No Cox or other ring-class-field reference in V17: add at 8876, 9003-9015 (idelic Pic), 9135-9137 (splitting of (ell)), 9593-9605. Local norm: see R3-F12. | Global Atkin correspondence and support/character compatibility not traced. |
| R4-F23 | Finite Heegner producers at 2 | RESOLVED IN V17 | Torsion annihilator via Serre open image 8914-8928 (checked); Howard used only as corroboration 8998-9000; compatibility of character and Frobenius choices is a proved proposition 9533-9640 (Kummer-relation consistency read). | Later bounded-model and determinant sections (10472-11870); uniformity in ell is not asserted. |
| R4-F24 | Picard quotient J_1(N) -> A | RESOLVED IN V17 | 6953-6976 now refers to section 35225-35233, which gives finite flatness, the determinant norm, relative Picard sheaves and "no rational point required" explicitly. | Silverman erratum; Kato Cor. 14.3 application at 6977-6981. |

Scope notes (no further work): R3-F3 (pending-node graph not closed); R3-F8 (import list not certified exhaustive); R3-F9 (D.4-D.6 disposition, LINKED063-067); R4-F8 (72 unresolved record fields, source ancestry); R4-F16 (33 pending source bindings).

#### COULD NOT DETERMINE

**R4-F5.** The review accepted the isogeny calibration only conditionally and left five inputs unreviewed. In V17 each is present with a citation: Edixhoven component groups 10198-10206; forward rank lemma 6933-6981 (Kolyvagin Thm 1, Kato Cor. 14.3); Poonen-Stoll 6923-6925 (the parity deduction in that lemma was checked); real-place complex 19400-19415; Nekovar support and duality statements 9475-9520, 9866. I could not check that the cited theorems say what the text uses, since the sources were not available, so their status is unchanged from the review: stated and cited, not independently confirmed.

**R4-F17.** Rows without any acceptance were 12, 17, 21 (and 4, 6 with only an author proposal). Row 12 (Weil pairing in the conjugate coefficient construction) is at 8794-8838 and I checked the equivariance computation; it is correct. Row 17/18 (integral Shapiro and transfer) is at 9236-9282 with an explicit cochain formula and Nekovar 8.1.1-8.1.6; read, not verified. Row 21 (open image, cyclotomic determinant) recurs at 8914, 9631-9660, 20057; read. Rows 4 and 6: see R4-F22. Nothing wrong was found, but apart from row 12 these are confirmations that text exists, not verifications.

### Batch 5

#### Batch 5 (ledger lines 980-1209): status in Version 17

Slice: 32 entries (R5-F1 to R5-F32). Selected as not clearly closed: 15 (F1, F4, F5, F6, F7, F8, F10, F12, F13, F21, F22, F28, F30, F31, F32).
Not selected (recorded as accepted/repaired/not consumed): F2, F3, F9, F11, F14, F15, F16, F17, F18, F19, F20, F23, F24, F25, F26, F27, F29.

Key structural fact, read directly in V17: the only live modularity input is the published statement in Calegari, ICM 2022, p. 624 (lines 2540, 5613-5616, 5793-5801, 15508-15512). Pan's paper is cited as proof ancestry only (4600, 44412-44416). Zero occurrences in V17 of: Thorne, Emerton, Saito, Henniart, Dospinescu, Paskunas, Colmez, CEGGPS/Caraiani, Kisin, Khare, Wintenberger, Skinner, Kalyanswamy, Shotton, Allen, Taylor-Wiles, DDT/Darmon, Kollar. "Hu--Tan" occurs once (5799, a disclaimer). "Breuil" occurs only as BCDT (6939, 7711, 44543). Line 5800-5801: the GL2-type and Serre weight-transfer reconstructions "are not inputs to the present lemma".

| ID | Topic | Verdict | Basis (V17 lines) | Not verified |
|---|---|---|---|---|
| R5-F1 | Unary theta / Chebotarev audit: Kummer element, source note, cap R>=2 | RESOLVED IN V17 | Unary derivation with imprimitive lambda, level 4C^2 J, cusp vanishing: 28870-28909, with the suggested source note (Weil I.19-20, Ramsey (1.1)) at 28871. Cap "choose R>=2": 21278-21284. Kummer element for the moving theta stage is constructed at 20045-20110 (summary 8493-8520). I checked the cocycle steps myself: (z-1)c(g)=(g-1)c(z) from commuting a central scalar; c(sigma^2)=(1+C)(v+d_tau)=(1+C)v since (1+C)d_tau=c(tau^2)=0; b c(sigma^2)=2^(a+1). | Existence/local compatibility of modular Galois representations (Carayol/Casselman use at 21484-21564), minimum-depth, graph and Selmer arguments: scope note, not read. No Serre 1981 section 2.1 locator for finite Chebotarev was found in V17 (optional citation). |
| R5-F4 | O2: Saito p-place proof / Henniart not read | ROUTE NOT USED | No hit for Emerton, Saito, Henniart, Colmez, Paskunas. | Transitive role inside Pan's proof (see F7/F8). |
| R5-F5 | Thorne 2015 Prop 3.15(1) false (ANT 2020) | EXPOSITION OR CITATION FIX | V17 does not cite Thorne or ANT, and does not reprove Pan (2540, 5797-5801). The project repair `pan-local-rings-project` is a bibliography item (44788-44793) that is never cited in the text. Add to the scope paragraph 5793-5801 one sentence: Pan Lemma 4.2.10 / Prop 4.2.4 import Thorne 2015 Prop 3.15; 3.15(1) is corrected in Allen-Newton-Thorne 2020 section 3.1; Pan's argument uses reductions/Taylor's componentwise statement; cite the supplement. | I did not check the supplement's mathematics, nor that Pan's JAMS final text matches arXiv v2 at this point. |
| R5-F6 | Pan 4.2.10(2): O-flatness not given by Thorne 3.15/3.16 | EXPOSITION OR CITATION FIX | Same as F5: repair lives in the uncited bibitem 44788-44793 (and 44781, 44795 also uncited). Same sentence at 5793-5801 should cite it. | The rank-one determinantal flatness proof was not re-read. |
| R5-F7 | Pan route: residual-nontrivial branch, editions, Thorne 1.3/1.5/1.6 unaudited | STILL OPEN (acknowledged) | 2540: "Final Pan JAMS body retrieval returned 403. We do not claim to have compared that body, or to have recursively re-audited its proof." 4713, 4719, 2634 repeat this. | Whether Calegari p. 624 is worded exactly as V17 paraphrases it (I did not open the source). |
| R5-F8 | Five unverified final-source families | STILL OPEN in part | Pan final, Kisin 2-adic/KW, Thorne 2015: still unverified, now only as ancestry of the Calegari/Pan theorem (2540, 4600, 4713-4719). Kollar: RESOLVED, replaced by Colliot-Thelene-Salberger 1989 Prop 1.3 (17951-17962, 44263-44274). Buzzard: RESOLVED at source level, final Duke text hash ed34a072 cited at 2438, used at 5934-5946, 13016-13019; later record B11-BUZZARD-TWO-REVIEW.json (2026-11-09) accepts both applications. "2002 corrections" not mentioned in V17. | Buzzard: I confirmed the hash and the later record, not the theorem text. CTS 1989 statement not opened. |
| R5-F10 | Paskunas Image Thm 12.7 depends on disputed Emerton input | ROUTE NOT USED | No hit for Paskunas, Emerton, Breuil-Mezard. | - |
| R5-F12 | Hu-Tan application not accepted; Dospinescu final not obtained | ROUTE NOT USED | Only mention is the disclaimer at 5798-5800. | - |
| R5-F13 | RED bridge accepted only against Dospinescu author version | ROUTE NOT USED | No hit for Dospinescu, Ext_alg. | - |
| R5-F21 | A001 moduli: degree-four isogeny, Igusa tuple, B11 index, degree 324 | RESOLVED IN V17 | Third mark's discriminant -24 comes from the fixed mu, and 5881-5883 says BG 3.7/3.8, the numerical CM evaluation and the conic descent are not used. Igusa tuple derived at 5849-5880; I recomputed the three ratios at x^2+12x+144=0 (x^3=1728): -16/27, 1, 11/27, and the rescaling to [j, j^2, j^3, j^3(j+1)]. Index bound 4*81=324 at 5884-5926; identification of Y_3 with the canonical curve 6207-6240. Universal abelian scheme comes from the fine model, not the coarse P^1 (5933-5946, 6291-6292). | Lin-Yang Examples 29-30 and eq. (13)-(14) inputs; the integral-model/descent section v15:marking-descent; the final passage from s-invariants to J_2..J_10 (5872-5877). |
| R5-F22 | CM reciprocity: Frobenius convention unidentified | EXPOSITION OR CITATION FIX | 35244-35248: formula quoted from Silverman C.11.4 with unspecified Frob; III.1.4(b),(c) locators and tangent-faithfulness now explicit (requested items present). Inversion invariance stated at 35248 and 35277 ("Global inversion of Artin indices does not change a quadratic character"), one place throughout. Missing: a sentence at 35244 saying the Frobenius is in Silverman's printed convention, not identified with arithmetic Frobenius, and that the consumer is unaffected because chi is quadratic and one global inversion is applied. | That the consumer's chi is quadratic in every use (read only 35277-35279). |
| R5-F28 | Theta_Q finiteness; signed-modulus "AC character" use not approved | ROUTE NOT USED | No Taylor-Wiles/Theta_Q text. Kopp-Lagarias is used only for Z[i] ray groups of finite modulus, no real places (25272-25284), Thms 1.1, 1.3, 6.5, 7.2. | I could not identify an "AC character" consumer in V17; the finite-order twist in M3 is proved finite before reciprocity is applied (2550-2552), which I checked. |
| R5-F30 | Khare base cases: solvable-image branch | ROUTE NOT USED | No hit for Khare, Wintenberger; 5800-5801. | - |
| R5-F31 | Khare Lemma 5.1(i)/(ii); 5.3, 5.4 not accepted | ROUTE NOT USED | Same. | - |
| R5-F32 | Finite-flat weight-2 criterion; second family not accepted | ROUTE NOT USED | Same; "finite flat" hits in V17 are unrelated ([n] on elliptic schemes, Picard norm). | - |

Scope notes (one line each, no further work): F18 retained-not-re-accepted list for the conductor-one assembly; F3 conventions confirmed; F15 C10 conditional interface (route not used in V17). For the closed entries F16/F17 I incidentally confirmed the repaired wording is in V17 (20205-20222: right-Hom convention, "coarse-point rationality").

#### STILL OPEN items

**R5-F7 / R5-F8 (Pan and its ancestors).** V17's modularity lemma (5613-5616; Part I section M2, line 2540) applies the Calegari p. 624 statement of Pan's theorem as a published black box and verifies its hypotheses for r_5 (irreducible, geometric, weights {0,-1}, odd, p=5) at 2534-2540. V17 states in terms that the final JAMS body of Pan was not obtained (403), was not compared with arXiv v2, and its proof was not re-audited (2540, 4713, 4719), and that incorporation and acceptance of this bridge are "pending a nonauthor reviewer" (2634). So the F7 items (residual-nontrivial branch, Thorne Lemmas 1.3/1.5/1.6, editions) and the F8 families Pan / Kisin 2-adic and Khare-Wintenberger / Thorne 2015 remain unverified transitive inputs of a cited published theorem. This is an acknowledged source limitation, not a gap in an argument V17 itself writes out. The known Thorne 3.15(1) correction (F5/F6) sits inside that ancestry; the project's repair is listed in the bibliography but never cited. The Kollar and Buzzard families of F8 are closed as described in the table.

### Batch 6

#### Batch 6 (ledger lines 1210-1521): status in Version 17

Slice: 43 entries (R6-F1 to R6-F43). Selected as not clearly closed: 28.
Not selected (ledger records repaired/replaced and accepted): F3, F6, F7, F9, F10, F12, F15, F17, F19, F27, F28, F29, F31, F36, F42.

Verdict counts: ROUTE NOT USED 15; RESOLVED IN V17 12; EXPOSITION OR CITATION FIX 1; STILL OPEN 0; COULD NOT DETERMINE 0.

#### Global observation behind the 15 "ROUTE NOT USED" verdicts

V17 contains zero occurrences of Khare, Wintenberger, Savitt, Kisin, Nagura, Saito, Skinner, DFG/Diamond--Flach, Gee--Savitt, Thorne, Arthur, Clozel, "lifting ring", Lichtenbaum, Shotton (Grep over the whole file). "Langlands" occurs once (title of Calegari's ICM article, line 44756); "Raynaud" once (Silverberg--Zarhin criterion, line 6626, unrelated); "Chebyshev" twice (elementary prime bound, lines 22829/22859, unrelated to Khare's prime selection); every "base change" hit is geometric.
The only modularity input is the published prime-five statement in Calegari ICM2022 p. 624 (Lemma `lem:qm-modularity-descent`, lines 5589-5791; Part I M2, line 2540). Lines 5793-5804 and 15507-15513 state that Pan is its proof source, that not every input to Pan's proof is reproved, and that "the separate GL2-type and Serre weight-transfer reconstructions are not inputs to the present lemma". The bibitems `pan-local-rings-project` (44788) and `pan-utility-project` (44795) are never cited in the body.
I verified the absence by search and by reading lines 5605-5625, 5788-5806, 15500-15516, 2536-2542, 4585-4602. I did not re-audit Calegari/Pan.

#### Table

| ID | Topic | Verdict | Basis (V17 lines) | Not verified |
|---|---|---|---|---|
| F1 | Weight-two pair: discriminant-one input, KWII p.583 Khare ancestry | ROUTE NOT USED | No Khare/KW/Minkowski text; modularity via Calegari 5614-5616, 5793-5804 | The retained inputs themselves |
| F2 | Seven of nine Khare caller obligations; Duke final text | ROUTE NOT USED | same | -- |
| F4 | DFG premotivic member; Saito 1997 antecedent unchecked | ROUTE NOT USED | no DFG/Saito in V17 | -- |
| F5 | Nebentype/duality order; compiler non-acceptance | ROUTE NOT USED | same; V17's own nebentypus handling is at 5681-5720, 15146-15229 (different argument) | -- |
| F8 | Prime-conductor corollary dependency cycle | ROUTE NOT USED | no Khare Cor. 1.2 / level-one theorem use | -- |
| F11 | Savitt edition; 6.12(4) wrong | ROUTE NOT USED | Savitt: 0 hits | -- |
| F13 | Serre finite-flat weight criterion over general finite field | ROUTE NOT USED | no such step; only Raynaud hit is 6626 | -- |
| F14 | Khare W32 row j=16 (included because Duke text unchecked) | ROUTE NOT USED | no weight table in V17 | -- |
| F16 | Corrected selection not transported to records | ROUTE NOT USED | no j=16, Nagura or Ellison text; Chebyshev hits 22829/22859 are an unrelated estimate | Project record files |
| F18 | Tame ordinary: scalar type | ROUTE NOT USED | no Savitt 2.17 consumer | -- |
| F20 | Multivariable factorization for E.11/E.13 | RESOLVED IN V17 | Thm MF-D4 31214-31238; Thm MF-E11/E13 31240-31255 (covers polytope indicator); proof 31625-31670; Assembly 29117-29120; D.6 denominator note 31676 | Read statement and 31625-31670; did not check Lemma `6:lem:integral` or eqs (10)-(15), 31258-31623 |
| F21 | E.8-E.10 factorial and symmetry after arbitrary test | RESOLVED IN V17 | 33886-33941: symmetric product (13), domain argument for nonvanishing, eq (15), division by C^2 first; s-division for (13.4) at 33943-33964 | Checked the argument as written; did not check Lemma `11:lem:raw` (33762-33884) in detail |
| F22 | (13.14)-(13.17) shift index and constant | RESOLVED IN V17 | independent shifts h_j in (17), coefficient (18), 34410-34436; source note 34566-34570 | I re-derived (13),(15),(16),(18): coefficient (-1)^(s-1) s! confirmed |
| F23 | Thm 7.4 strict hypothesis vs Thm 7.1 output | RESOLVED IN V17 | Target theorem assumes "at most s-2", 34178-34199; 34561-34565; Assembly 29090-29093 | -- |
| F24 | Lemma 13.4 slot swap, sign | RESOLVED IN V17 | (15)-(16) keep slot order, 34384-34399; 34566-34569 | algebra re-derived by me |
| F25 | Prop 8.4 premise, three C-S steps, I_6 box, beta, orthants | RESOLVED IN V17 | 34215-34219, 34232-34302 (8.4, lower factors), 34304-34357 (C-S, I_6 with n-independent cutoff), 34396-34407 (beta), 34471-34487 (orthant reflection); Prop 8.4 supplier noted 29096-29116 | Followed the chain; did not recheck Prop 8.4 supplier section 34008-34157 or Prop 5.6 |
| F26 | Initial strong selection scope; A.12 display; Mal'cev countability | RESOLVED IN V17 (scope stated) | 29031-29038 (no weak-to-strong upgrade claimed); selection 29335-29382; countability argument 29384-29399 | Source hashes; visual check of GTZ A.12 display; Mal'cev input is cited, not proved |
| F30 | lem:Pi connectedness; finite-evaluation embedding | RESOLVED IN V17 | 34676-34772; connectedness invoked 34685; embedding 34732-34741; "no class(P_0)<=s" 34741 | Read the proof; record shows embedding was separately approved by SourceReview |
| F32 | Section 12 filtration index range | RESOLVED IN V17 | 33022 ("H_{a,j}=1 for every a>1 and every j>=0"), display 33024-33029 | -- |
| F33 | GTZ Section 12 defects (pigeonhole, H_(0,1), P_m vs T, unit norm) | RESOLVED IN V17 | extension lemma 32907-32924; test choice 32926-32949; adverse example 32951-32960; audit items 33259-33287 | Did not check eq:completion/fixed-chart construction 33127-33210 line by line; other copies of near-zero normalization: Grep for "near zero/around zero" finds only 33284 |
| F34 | Only rank drop for R>1; LP04 not independently reviewed | RESOLVED IN V17 (mathematics) | 33247-33252, 33291-33293; one-step interface 33427-33458; iteration and (m,0) endpoint 33507-33539 | Whether LP04 received a non-author review (not visible in manuscript); LP04 section 32271-32805 not read |
| F35 | Strong convention attributed to GTZ Def 6.19 | EXPOSITION OR CITATION FIX | V17 never cites Def 6.19. 29823-29827 and 30069-30076 state the all-limit reading as the convention "used in this proof", citing A.2-A.3; 29031-29038 says witnesses are represented families. Suggest one sentence at 29823 and 30069 saying this is stronger than the literal published Definition 6.19 and is a hypothesis met by the constructed witnesses | SOURCE-USES.json record |
| F37 | Lin--Yang D6 normalization; disputed Baba--Granath statements | RESOLVED IN V17 (limits disclosed) | 5823-5830 (BG form corrected), 5849-5876, 5877-5883 (BG Props 3.7-3.8, CM evaluation, conic descent not used), 6295-6302; no use of BG Thm 3.10 | I rechecked the arithmetic at 5858-5868 (x^3=1728; ratios -16/27, 1, 11/27; c_i=1). The three global identities and LY eta/CM values remain retained published inputs |
| F38 | Thorne Prop 3.15(1) defect | ROUTE NOT USED | see global observation | Final Pan/Thorne versions |
| F39 | Flatness of unreduced fixed-determinant ring | ROUTE NOT USED | direct proof not in V17; supplier bibitem 44788 uncited | -- |
| F40 | Pan comparison is a degree-two etale cover | ROUTE NOT USED | same | -- |
| F41 | Kisin Prop 9.5 versal/W(k); final versions | ROUTE NOT USED | bibitem 44795 uncited | -- |
| F43 | H-D4: Langlands edition, ramified local compatibility (H-D5) | ROUTE NOT USED | no cyclic base change / Hilbert-form attachment in V17 | -- |

Scope notes (one line each, no further work): none beyond the scope clauses already folded into F26, F34, F37 above.

#### STILL OPEN / COULD NOT DETERMINE

None.

#### Remarks that are not verdicts

1. F38-F41: V17 treats Calegari p. 624 as a published theorem and explicitly declines to certify Pan's inputs (5797-5801; 2540 notes the JAMS body was not compared). The project's repairs of gaps in Pan's proof (flatness, etale-cover comparison) exist only in supplements listed in the bibliography but never cited. If the authors want those repairs on record, a citation in the scope paragraph at 5793-5804 would do it. This is a policy choice, not a defect in V17's stated argument.
2. F21-F25: the ledger status was "independent review pending". The arguments are now in V17 and I checked the sign/coefficient algebra, but the manuscript cannot show whether a non-author review occurred. V17 itself says (34574-34576) that related uses of the source discrepancies "must be checked independently before a complete correction claim".
3. The record path given in the task needed `C:/...` rather than `/c/...` when `MSYS_NO_PATHCONV=1` is set.

### Batches 7 to 9

#### Batches 7, 8, 9 (ledger lines 1522-2045) against Version 17

Slice size: 70 entries (batch 7: 21, batch 8: 20, batch 9: 29).
Selected: 42. Of these, 31 were checked against the manuscript and 11 are scope notes.
The other 28 are recorded in the ledger as repaired and accepted, and were not re-examined.

Layout fact that drives most verdicts: Version 17 is Part I (the 214-variable construction, lines 83-5135) followed by the whole Version 16 body (from line 5136). The 299/314 quartic that batches 7-9 mostly concern is still in the manuscript as Section `sec:v14`, lines 27916-28868, and is cited by Theorem `thm:v15-decimal` (line 5181). So findings about the 299/314 chain are live text, not history.

"Hand-checked" below means I redid the algebra or valuation arithmetic myself. "Text only" means I confirmed what the manuscript now says without checking the proof.

#### Table

| ID | Topic | Verdict | Basis (V17 lines) | Not verified |
|---|---|---|---|---|
| R7-F1 | 156-power common scale: residue classes collide | RESOLVED IN V17 | Uses the reciprocal variant: exponents 160/40/80 and guard gamma^16 E^8 (28216-28228). Class table 28244-28257. Hand-checked: in all three groups the valuation classes mod 16 are pairwise disjoint and nonzero for every odd alpha and every integer v(gamma). Also hand-checked the soundness bounds 28270-28288 and the completeness valuations 159, 3, 83, 76, 8 at 28541-28551. | The ledger records the guard as gamma^16 E^12; V17 has E^8. I checked the V17 form only. |
| R7-F2 | Unguarded common inverse 1/(R0 R1 R2) | ROUTE NOT USED | Each detector keeps its own inverse E_j R_j = 1 (28163-28166). Searched for a common inverse product; none. | - |
| R7-F3 | Cheaper pole guard B_old C^2 / R_j^2 | ROUTE NOT USED | Pole rows are N(W_j) = 2 Re(W_j) z_j and B_j(R_j+E_j+2) = z_j^2 (28170-28173). Low terms stay in G_0..G_2 (28225-28227). | - |
| R7-F4 | Common scale accepted at source level only (existence of gamma, gate binding, H bootstrap) | RESOLVED IN V17 | Existence of gamma: 28599-28703, with gamma = 1/u on the anchor quadric. Hand-checked the three local points at 2, 3, 17 (28638-28654) solve the quadric and the radicands are 1 mod 8, 3, 17. H bootstrap: 28439-28499. Completeness order of choices: 28589-28597. | Binding of the literal gates to R_j is one sentence (28168) and rests on the coefficient artifact. Weak-approximation paragraph 28668-28703 read, not checked line by line. |
| R7-F5 | Dropping the root square-root coordinate a | ROUTE NOT USED | a_i^2 = c_i is retained (28047-28060, 28372-28374), so roots stay in 2E(K) = ZP. | - |
| R7-F6 | Removing b: needs a real ordinate and a != 0 on every branch | RESOLVED IN V17 | Oriented difference U-V = (c, y_R) on all branches (28350-28364). Division-free curve identity 28366-28371, hand-checked by expansion, as were 28335-28336. c_i != 0 from the product chain (28376-28386). Scalar root keeps b_2 plus orientation row (28392-28400). | The c_i != 0 step cites literal coordinates v337-v394 and a "retained inverse equation" not printed in this section. |
| R7-F7 | Binary anchor <1,1> loses the representation lemma | ROUTE NOT USED | Anchor is the ternary indefinite form u^2 + 6v^2 - 2w^2 (28101-28104, 28604). No positive or binary anchor found. | - |
| R7-F8 | Using another alternate logarithm as denominator | ROUTE NOT USED | V_0 with index h_0 - 1 is retained (28456-28471). | - |
| R7-F9 | Square-root shortcut for the logarithm gate | ROUTE NOT USED | Rational approximants N(w)/Q(w) with their denominators are retained (28501-28519). | - |
| R7-F11 | Opposite-point branch f = F; coefficient 186624 C^2 | RESOLVED IN V17 | Branch closed at 28357-28362 (hand-checked: h = 0 needs f = 0 or D f^2 = 1, both contradict 3 D f^2 = 1). Coefficient 186624 * 3^(2^26) with no +64 at 27930 and 28807. | Coefficient value is an artifact property. |
| R7-F12 | 2^3247 bound false for the 314 lift | RESOLVED IN V17 | 314 is stated below 2^6496 at 5184, 27937-27944, 28853-28861. Abstract says below 2^6500 (5150). The 2^3247 statements at 25474, 26108, 27038, 27075, 27903 are for other polynomials. | - |
| R7-F13 | Undeclared exponent k in two-scales lemma | RESOLVED IN V17 | "Let k in Z_{>0}" at 36266. | The four large numerical comparisons the review skipped. |
| R7-F14 | epsilon versus epsilon^2 | RESOLVED IN V17 | 35869-35873 names epsilon^2 and concludes ord(epsilon) <= 2[L':Q]. | - |
| R7-F16 | Surface-height lemma checked only against author version of Remond 2022 | ROUTE NOT USED | Lemma `v15:height:lem:surface` now takes its product construction from Gaudron-Remond 2023 Lemma 16.2(1) and the CMH 2014 paper (35749-35783). Remond 2022 appears only as a dependency of that published proof (35768-35771). | Final published text of Remond 2022 is still unread; V17 says so at 3022 and 3174-3178. |
| R7-F19 | Scalar-Frobenius model unsourced | RESOLVED IN V17 | Ribet 1990 Prop. 3.3, Rem. 3.5(a),(b), Prop. 3.6 installed, right-module Hom(E_0,E) convention, coarse-point rationality only (20200-20222). Later uses refer to coarse points over F_{l0^2} (20987, 21052). | Ribet's text not opened by me. |
| R7-F20 | 330 candidate needs Pi^39 | ROUTE NOT USED | Completeness uses depth-19 preparation (28535-28539). No Pi^39 anywhere. | - |
| R7-F21 | Deleting the g_0 inverse guard | ROUTE NOT USED | g_0 tau = 1 retained (28062-28066). | - |
| R8-F2 | 156-power construction stays rejected | ROUTE NOT USED | Same as R7-F1. | - |
| R8-F6 | Middle ordinary lift misses the 3247-bit cap | RESOLVED IN V17 | V17 selects the 14-constant chain and states 3^4098 + K_0 < 2^6496 (28815-28861). No middle lift is claimed. | - |
| R8-F9 | Constant-gate lower bounds only in a restricted model | ROUTE NOT USED | No minimality claim for constant coordinates; 28815 says only "can be represented with fourteen". | - |
| R8-F15 | Original candidate 392 not accepted | ROUTE NOT USED | f != 0 comes from the three field equations (27998-27999), which is the 392t route. | - |
| R9-F5 | Auxiliary E(K) extension conditional on oriented group law | RESOLVED IN V17 | Same passages as R7-F6, plus the scalar orientation row and its stated purpose (28392-28400). | Same as R7-F6. |
| R9-F9 | GR 2023 replacement for the surface lemma not yet installed | RESOLVED IN V17 | Installed at 35749-35783. | Source content. |
| R9-F14 | Limits of the Version 16 reviews | EXPOSITION OR CITATION FIX | Line 35770 refers to "his 2017 results" with no bibliography entry; add Remond 2017 (Theorem 1.6) and the locator. Rest is a scope note. | Kato pp. 314-318, Ribet pp. 440-443, final Remond editions, PDF build. |
| R9-F17 | Bridge: scope and items left to integration | RESOLVED IN V17 | Scope is the fixed Gaussian ray field (24488, 24544, 25078-25085, 25257). `v6bienvenu` is in the bibliography (44259); Green-Tao is cited as `greentao` (24567). Dodos-Kanellopoulos is not cited anywhere. | Text only. |
| R9-F20 | Factorization review: obligations left to others | RESOLVED IN V17 | The named obligations are present as proved statements: Hecke Siegel-Walfisz lemma (23135-23200), Type I/II section with no Frei-Tinkova theorem assumed (23608-23619), conjugation-invariant ray conditions (24244, 24488), centered estimate (25255-25270). | Text only. I did not check these proofs. |
| R9-F25 | Kollar checked in preprint only | ROUTE NOT USED | Kollar is not cited. The cubic step uses Colliot-Thelene-Salberger 1989 Prop. 1.3 (17951-17962). | - |
| R9-F26 | Order-39 alternative | ROUTE NOT USED | Order 40 and C = 3^(2^25) (27931, 28489). | - |
| R9-F27 | Smaller ordinary companions exceed the old bound | RESOLVED IN V17 | Same as R7-F12; 27943-27944 says the bound differs from P_411. | - |
| R9-F28 | Version 6 elimination search | ROUTE NOT USED | No conic parametrization or 1,251/1,272 counts in V17. | - |
| R9-F29 | Positive anchor 365 | ROUTE NOT USED | No form U^2+V^2+6W^2 and no constant 8450. | - |

#### Scope notes (no further work)

- R7-F15: reviewer abstained from FINAL233 transfer and did not open Remond / Gaudron-Remond.
- R7-F17: final-assembly reviewer's ancestry; thresholds ineffective.
- R7-F18: centralizer review covers the algebra step only.
- R8-F4: shared314 arithmetic review does not cover the emitted system.
- R8-F19: inherited arithmetic (Mordell-Weil, contact height, pole theorem and others) not re-proved.
- R8-F20: inventory reviews R4-R6 are structural only.
- R9-F2: 354/348 finite checks were replays.
- R9-F4: 299 versus 301 is projection equivalence only (V17 says the same at 28737-28739).
- R9-F8: shared314 construction review does not cover the arithmetic.
- R9-F23: norm-transfer review does not prove product-orbit equidistribution or Type I/II.
- R9-F24: Mitsui Lemma 15 proof omitted in the source; fixed-field scope.

#### STILL OPEN / COULD NOT DETERMINE

None in this slice.

Two residual items that are not gaps in V17's argument but are unfinished checks: the final published text of Remond 2022 has not been read (V17 lines 3022, 3174-3178), and the 299/314 statements about literal coordinates and coefficients (28168, 28376-28386, 28800-28811) depend on artifacts I could not inspect from the manuscript.
