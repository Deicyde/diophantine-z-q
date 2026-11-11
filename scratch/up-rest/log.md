# up-rest log

## Step 1: orientation (v16 package)
- No earlier log; fresh run from 520e27e5.
- ~/upstream research/version16/RELEASE-NOTES.md, README.md, protocol/CURRENT-CORRECTIONS.md read.
  Three changes: (1) horizontal normalization before finite covers; (2) Gaudron-Remond CMH 89 (2014) 343-403 cited for two Faltings-height statements; (3) Tao-Ziegler fixed-extra-factor E use = adaptation of proofs. Precision amendment: divisor-sum local factors satisfy same uniform estimates (not identical values). Theorem statements and polynomial data "unchanged from Version 15" (RELEASE-NOTES.md l.7).
- quartic_v16.tex l.58-63 abstract: 292890231905 variables, degree < 2^^7, coefficients < 2^^8 (same numbers as N5 Thm 1.1). Also 314-variable quartic and 222-variable family.
- Sizes: v13 22087, v14 24347, v15 39896, v16 39932 lines.

## Step 2: N5 Thm 1.1 vs v16; polynomial data; 22P placement
- thm:target: N5 l.60-77 vs v16 l.113-130: identical up to CRLF (diff -w empty). VERIFIED.
  Same label in v13 l.87, v14 l.87, v15 l.113.
- construction/: all 28 files byte-identical between fork and ~/upstream (sha256), except README.md
  (upstream retitles it "Original large construction"). ordinary-integer-definition.json sha256 4d639d4c...af6 in fork, upstream, and v15 snapshot v15-018. VERIFIED.
- scratch/up-rest/n5_in_v.py (difflib, rstrip lines): N5 11259 lines, 10846 appear in order in v16; 95 changed blocks listed in scratch/up-rest/n5_vs_v16.txt.
  Big changes: N5 400-478 (Thm 4.1 six-contact) -> v16 501-1141 (H domain, not mine); quartic material inserted v16 7587-13004 and 17540-39138.
- 22P (prop:fixed-prime-pattern): N5 l.1267; v13 l.1385, v14 l.2052, v15/v16 l.2076. Body verbatim except GI source of the Green-Tao linear-equations input:
  N5 l.1408 "[Theorem 1.3]{gtz}" + l.1416-1418 (arXiv v5 + erratum); v13 l.1526 same as N5; v14 l.2193 "[Assembly, Sections 1 and 6]{local-gi}" (external 106-page supplement, research/version14/proofs/local-gi-v1); v15/v16 l.2217-2228 "Section~\ref{v15:gi-full}" = Part "The polynomial inverse theorem and its local joins" (v16 l.23831-30184).
- Tao-Ziegler adaptation: v16 subsec "Fixed Artin conditions in quadratic patterns" l.19989-20170, inside sec "Simultaneous primes with coprime adjacent norms" l.17544 (thm:v5-simultaneous-primes l.17565). Cited at v16 l.11798, 12269, 12354 (962-var quartic), 20433 (v9 quartics), 31156-32268 (222 family). Not cited in the large-construction sections (v16 l.76-7586, 13005-17543).
- Slope predicate N5 1172-1174 / 1194-1198 vs v16 1951-1958 / 1978-2007: v16 spells out A_i - sigma(A'_i) (primed ratio conjugated) and writes out the valuation deduction; polynomial file unchanged, so expository.

## Step 3: locating Version 16's edits (research/version16/EDITS.json, exact-newline search in quartic_v16.tex)
- horizontal-normalization: v16 l.26821-26842; finite-cover-fixed-lifts: v16 l.26908-26915. Both inside Part v15:gi-full (l.23831-30184, polynomial inverse theorem).
- gr-lower-bound v16 l.30664, gr-isogeny-height v16 l.30677: subsec "An abelian surface occurring as an isogeny factor" (l.30630) of Part "The 222-variable family" (l.30185). Key gr2014 -> gr-periods2014 (CMH 89 (2014) 343-403, bib l.39342).
  Six-contact proof (v16 counterpart of N5 Thm 4.1) still cites Duke gr2014 Thm 1.4 / Section 9 at v16 l.1322, 1599, 1616 = N5 l.615, 878, 895. Bib entries N5 l.11063 = v16 l.39347 identical.
  Fork notes cite only Duke Thm 1.4/§9 (h-trust.md:672, h-cm.md, h-v14.md:229,257,258). No fork note cites Duke for §2.3/Cor 8.4 (grep). Not affected.
- tao-ziegler-proof-adaptation: v16 l.20060-20072 in subsec "Fixed Artin conditions in quadratic patterns" (l.19989), section of thm:v5-simultaneous-primes. Not cited by large construction (grep of v5 labels/v5tz in v16 l.1-7586, 13005-17543: none).
- TZ-PRECISION-AMENDMENT.json: one occurrence, "divisor-sum local factors are unchanged" -> "satisfy the same uniform estimates"; decision: changes no theorem, estimate, parameter order.
- v15:gi-full (GI) is cited by the large construction: v16 l.2217 (22P), 9565, 10406 (quartic sec), 13326 (dependency table). So the horizontal normalization correction sits under 22P's GI input in upstream's own large-construction proof.
