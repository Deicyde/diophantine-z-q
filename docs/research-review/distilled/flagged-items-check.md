# Check of the flagged items against Version 17

Done 2026-11-13. Each item on the "Check these first" list in README.md was checked by reading the cited passages of `manuscripts/quartic_v17.tex` and the source notes or later records. The first item was read by Claude directly; the others by three reader agents. Line numbers refer to `quartic_v17.tex`.

**Result: none of the thirteen flagged items is a real gap in Version 17, and neither is any of the 20 further proof notes checked in the second pass below.** Seven are compressed statements of standard arguments or are printed in the manuscript already, four belong to routes Version 17 does not use, and the rest were resolved by later records. The check produced a list of exposition and citation fixes instead.

## Verdicts

| Item | Verdict | Basis |
|---|---|---|
| Heegner kernel specialization (near 8989) | Exposition only | Extension of an isogeny between elliptic schemes and uniqueness of the order-ℓ subgroup of a supersingular curve are textbook facts; the congruence is the classical one and Howard is cited. |
| Atkin–Lehner identification (21030, 35277) | Exposition only | Line 35277 states that the prime-power Atkin–Lehner quotients have degree prime to q and reduce compatibly. The earlier flag misread the good-model argument as needing degree prime to N. |
| `local-twist-factors-002` | Exposition only, partly printed | Core argument is at 19009–19012; the summary at 18818–18826 needs only standard facts about ramified quadratic twists. |
| `qm-idempotent-image-v1` | Exposition only; the note's other applications are not used | Lines 13745–13752 and 6389–6391 use textbook facts about images of idempotents. The Weil-restriction applications do not occur in Version 17. |
| `real-kummer-lattice-v1` | Exposition only | Lines 19400–19418 give the reason for the integral splitting; the rest is a short computation and local Tate duality. |
| `shared314` depth bootstrap | Printed in full | 28478–28488 with inputs at 28270–28290. The reader re-derived the inputs and found the logic sound; one step (transfer of integrality across conjugated alternates) was not independently traced. |
| `pan-local-rings-v1`, Thorne 2015 | Remark about the literature | Version 17 applies only the published statement (Calegari, ICM 2022, p. 624) at 5588–5793 and says it does not reprove Pan's inputs (5795–5802). |
| `general-field-tw-v1` | Route not used | No Khare–Wintenberger, Kisin or Taylor–Wiles argument appears in Version 17. |
| `yuan-final-source-v1` | Handled; remark about the literature | Version 17 uses only Yuan §2.1 and Theorem 1.1 (12842, 13220) and expressly not Lemma 2.1 (13200). A source review in the records found Theorem 1.1 does not depend on it. |
| Emerton, Paškūnas, CEGGPS findings | Route not used | None of these sources is cited or applied in Version 17. |
| All-prime irreducibility | Handled; corrected argument is printed | 13400–13416 and 5604–5636 use matrix units and Faltings, with no quadratic subfield assumed. |
| Milne citation, local norm step | Resolved later | Version 17 no longer cites Milne here (6635–6638). The fact is standard local class field theory, and a later record gives a derivation that was accepted. |
| Herbrand conversion, dyadic conductor | Resolved later | Repaired paragraph at 6639–6654; each step checked. |
| Baba–Granath, Lin–Yang | Resolved for what is used | 5824–5833 states the printed form is six times the principal one and uses the corrected form. The disputed degree-four material is expressly not used (5882). |
| PR 30 pending items | Resolved at stated scope | Final queues for the 214-variable family are empty; the last reviews accept the assembly "at stated scope". |

## Fixes worth making in the next manuscript version

- Add a sentence and a citation at 8989 (finite flat extension; unique order-ℓ subgroup) and at 35277 (moduli description of W_n).
- Add a citation for local reciprocity and norms at 6635–6638, for example Serre's chapter in Cassels–Fröhlich, which is already in the bibliography.
- At 5797, say that the project found and repaired an unsupplied flatness step in Pan's proof, and cite the supplement. The three `pan-*-project` bibliography entries (44781–44797) are never cited.
- Record at 13200 why Yuan's Lemma 2.1 is avoided.
- Remove the unneeded 4D² clause near 6639–6654.

## What the records still qualify

These are limits stated by the final review records themselves, not new findings:

- Published theorems are not reproved. Pan is cited from arXiv version 2 because the journal text could not be accessed.
- For the 214-variable family, not all history files were freshly read, and 21 of 703 PDF pages were visually inspected.
- The defining threshold is ineffective.
- Alternate-route objections (TYZ, Route K) are preserved without being closed.
- Kato 1999 and Ribet 1990 were not read by the Fable audit.
- Every review is agent-authored, and none claims to be blind.

## Second pass: the remaining proofs

Done later on 2026-11-13. The other proof notes marked "statement used, argument not reproduced" or "not found by search" were checked the same way: 20 distinct notes (24 entries counting duplicate copies), by three reader agents. **None is a real gap.**

| Note | Verdict | Manuscript lines | Suggested addition |
|---|---|---|---|
| `atkin-cusp-input-001` | Exposition only | 8970–8979 | Cite Atkin–Lehner 1970, Lemma 8 |
| `cj-level-normalizer-001` | Exposition only | 21030–21038, 21058–21060 | See the note on line 21036 below |
| `global-atkin-root-sign-001` | Exposition only, citation missing | 20335 | Cite Atkin–Lehner and Hecke's functional equation |
| `heegner-finite-field-current` | Exposition only | 9081–9086 | None |
| `polarization-pairing-input-001` | Exposition only, citation missing | 5743–5745 | Cite Milne 1986, §16 (already in the bibliography) |
| `rooted-forest-network-input-001` | Exposition only | 22337–22357 | Cite Chaiken 1982 for the all-minors matrix-tree theorem |
| `beta-local-norm-published-current` | Exposition only | 6635–6638 | Cite norm functoriality of local reciprocity |
| `cyclotomic-zero-local-001` | Exposition only | 18840–18843 | Optional: name Weierstrass preparation |
| `dual-exponential-trace-001` | Exposition only | 18740–18746 | Optional: "by the projection formula" |
| `quadratic-gauss-local-001` | Exposition only | 18809–18815 | Cite a textbook for the Gauss sum identity |
| `finite-kummer-current` | Exposition only | 9578–9596 | Cite the Kummer pairing |
| `generic-kummer-current` | Exposition only | 9091–9095 | Optional citation for the Kummer sequence |
| `finite-field-halving-inputs-001` | Exposition only | 22192–22202, 25374 | Cite the 2-descent halving criterion |
| `elementary-inputs-current` | Exposition only, with one weak citation | 5366–5476 | **Replace the lecture-notes citation at 5399** |
| `qroot2-class-units-current` | Exposition only | 5452–5454 | None |
| `ceggps-connections-v1/o3` | Route not used | 5795–5802 | None |
| `research-additions-005/o2_proposal` | Route not used | — | None |
| `research-additions-005/retained_local_proof` | Route not used | — | None |
| `qm-centralizer-v1` | Route not used | 5588–5793 replaces it | None |
| `qm-cohomology-v1` | Route not used | 2620, 15197–15203 replace it | None |

Three things from this pass deserve attention:

- **A citation to unpublished lecture notes.** The division-polynomial formulas at 5386–5412 are correct, but the only source cited is Sutherland's MIT lecture notes (line 5399). The project's rule is to cite published results. A note in the records proposed a published replacement that never reached the manuscript.
- **An uncited identification at line 21036.** "The actual parametrization transforms by w_{p^e}" relies on identifying right multiplication by the local normalizer with the geometric Atkin–Lehner operator on supersingular points. This is standard (Ribet's dictionary), but the manuscript gives neither argument nor citation. Ribet 1990 is also one of the two sources no outside auditor has read.
- **Unaudited neighbours.** The symbol rules at 22328–22341 that the rooted-forest formula feeds into are internal to the manuscript and were not audited. Three of the local steps sit inside the Kato-based argument; the readers checked those steps only, not whether Kato's theorems apply at p=2.

Theorem and section numbers in the suggested citations were given from memory by the readers. Confirm each against the book before inserting it.

## Limits of this check

- Together the two passes cover every proof note not already found in the manuscript. The 46 notes the first search marked as present were not re-read, and the remaining internal findings recorded as open (roughly 50) were not checked.
- The readers are Claude agents reading specialized arithmetic geometry. Their verdicts are informed readings, not expert review.
- "Resolved at stated scope" repeats what the project's own records say; the reader did not trace all 33 pending rows individually.
