# Direct reads, reused evidence, and unread ranges

All manuscript locators refer to frozen V16 SHA256aeb2b6a42a03943d7f8c46682389c8da693d2903ba92ccc164bbbd236451de74. The files and excerpt hashes are bound in BINDINGS.json and the initial/reconciled tables.

## Current mathematical source

| Source/range | Review status |
|---|---|
| V16 17544–20356 | Entire Gaussian appendix directly read; project derivations and theorem applications reviewed. |
| V16 23833–24419 | GI statement and assembly directly read; internal component proof suppliers retained with their exact prior scope. |
| V16 24420–30095 | Not directly read in full. No fresh acceptance of component proofs; native supplier reuse explicitly distinguished. The initial range contains5676 lines, not a new coverage claim. |
| V16 31958–32067 | Weighted prime selection and strip consumer directly read. |
| V16 2194–2235,9530–9580,10378–10425 | Later direct reads to check all identified GI-consuming interfaces; surrounding original arithmetic proofs not reviewed by this lane. |
| current214 uniform-existence.md (84lines) | Read; analytic focusP15–P18 and their parameter order. New height/pole/CRT arithmetic assigned elsewhere. |
| current214 existence.md (92lines) | Read for completeness and inherited supplier qualifications; no separate acceptance of all algebraic/height reasoning. |
| current214 source-carry.md (40lines) | Read after initial freeze; analytic focusC09–C12 and exact-source limitations. |
| current214 PROOF.md | Prime-related excerpts and composition only; not a full independent review of this file. |

## Primary statements and definitions actually inspected

Published theorem proofs are a trust boundary; they are not recursively reproved. Where a project adapts a proof, the internal adaptation was checked against the published construction/estimates.

| Source | Direct scope | Qualifications |
|---|---|---|
| GTZ, Annals176(2012),1231–1372 | Normalized interval norm p1232; Conj1.2 p1233; Thm1.3 p1235 | Exact finite-family linear GI compatibility. Rest of published proof not re-reviewed. |
| GTZ author erratum,2024 | All6pages | Author-hosted correction, not claimed a journal publication. Main theorem unchanged; internal erroneous proposition and filtration corrections explicitly recorded. |
| GT orbits, Annals175(2012),465–540 | Definitions of filtration/equidistribution, horizontal-character modulus and smoothness norm; Thms1.19,2.9; Lemmas4.5,6.7; AppendixA metric/rationality statements A5,A9,A13,A17 | One-variable suppliers for this analytic lane. Supporting Appendix proofs only selectively read; no full article-proof claim. |
| GT orbits erratum, Annals179(2014),1175–1183 | Introduction/application limits pp1175–1176 and minor corrections pp1182–1183; equal-side result identified | No new proof of the full multiparameter theorem. One-variable suppliers expressly unaffected. |
| GT Möbius/nilsequences, Annals175(2012),541–566 | Conjugated quotient claim and its proof p547 | Rational bounded conjugator and actual subgroup/lattice assumptions checked. |
| GT linear equations, Annals171(2010),1753–1850 | Definitions6.1–6.3; Prop6.4; Prop7.1; Prop10.1; ThmD.3 and remarks; divisor-sum construction and normalized convex-body estimate pp1839–1840; normal-form interface | Internal majorant/normal-form adaptation independently read. No fresh reproof of published dense-model/GN machinery. |
| Tao–Ziegler, Polynomial patterns in the primes, ForumMathSigma5(2017),e30 | Thm9 p21; Thm11 pp28–29; Cor3 p38; Prop6 local-cube discussion pp39–40; Thm13/eq57 p41; Thm15 and proof pp57–58; divisor-sum/model construction relevant to fixed-E | Local file is named TZ2018.pdf, but inspected publication is2017. Theorem15's cited old polynomial-forms proofs are not recursively reproved. |
| Bienvenu, ActaArith179(2017),79–100 | Thm1.1 pp79–80 and finite-complexity conventions | Final publisher PDF directly read. Initial unrelated IMPAN retrieval explicitly excluded. |
| Mitsui, Japanese Journal of Mathematics26(1956),1–42 | Section1 character convention p2, imprimitive discussion pp2–3, uniformity and Lemmas14–15 pp11–12 | Journal scan viaJ-STAGE. p2 visually inspected; formulas/navigation otherwise checked against scan text. Not all42pages read. |
| Williams, JNumberTheory6(1974),353–359 | Intro/formula1.1 p353, nonzero factors, Theorem1 p356 and nearby proof | Author-hosted journal scan; p356 visually inspected. Fixed moduli only. |
| Kopp–Lagarias, EssentialNumberTheory4(2025) | Thms1.1,1.3,6.5,7.2 and Remark7.3; arithmetic Frobenius and natural ray maps | Actual maximal-order specialization and all downstream finite fibre arguments checked. Other general-order theory not reviewed. |
| Browning–Heath-Brown, ForumMath33(2021),147–165 | Accepted text Lemma2.1; Lemma4.1 and proof; following successive-minimum/basis/inverse arguments | Actual final comparison reused from later pinned final-source-bhb report; no fresh finalPDF access. |
| Browning–Loughran, TransAMS371(2019),5757–5785 | Institutional accepted Theorem4.1 and definitions authorpp16–17 through browser; actual historical final comparison and application argument read | FinalPDF403. Accepted extraction has inequality-glyph ambiguity; final visual comparison establishesn>=5 and exactuniformity. No claim fresh visual read. |

The Mitsui row deliberately spells out the correct journal title; no inference is made from an abbreviated guessed title. Primary URLs, PDF raw hashes, and versions are in PRIMARY_SOURCE_MANIFEST.json.

## Historical evidence inspected

- V16 coverage REVIEW.md: actual source-first/change/reuse account, corrected horizontal identity, fixed-E proof and precision wording, exact assembled scope and limitations.
- V16 record-repair-001 REVIEW.md, REVIEW.json and ASSEMBLY-REVIEW.json: exact current pins and mathematical invariance of the deduplication repair. PROTOCOL14-COVERAGE-REVIEW.json structure/selected bindings inspected; not every1170 decision reread.
- CurrentDOSSIER and selected CONNECTIONS: extracted66 rows. Read source/supplier/needed-interface and actual relevant derivation locations.59 belong to the analytic section including the fixed-E correction; incidental neighbouring rows are not silently accepted.
- V14 Gaussian source-card Markdown: relevant analytic cards inspected, with no substitution of paraphrase for available primary statements.
- BL/BHB earlier published-version review and retrieval record; later BHB FINAL-COMPARISON and final-statement disposition. Older open BHB qualification is distinguished from later actual published comparison.

No claim is made to have freshly inspected all earlier V15/source-profile review files or all internal GI antecedent proofs. Their accepted exact supplier scopes remain dependencies, whose authenticity/eligibility must be established by controller evidence. Sparse checkout omissions were not classified as repository omissions.

## Bounded correction search

Current primary-author/publisher searches included the GTZ2024 author erratum, the2014 Annals orbits erratum, TZ polynomial-pattern correction terms, Browning's publication page/geometric-sieve correction terms, and Williams's author bibliography. The known corrections above were considered. No statement that no other correction exists is made. No subsequent stronger theorem is silently substituted for a source used in the current argument.

## Final extension: current receiving bridge

Directly read after inventory reconciliation: FOUNDATION_TRANSITION.md complete; the nine mathematical obligation arguments and GI/TZ transition entries of FOUNDATION_APPLICATION.json; V16 correction26819–26929; V16 review/current/REVIEW.md and TZ-PRECISION-ADDENDUM.md complete; assembled214 TeX1996–2029,2295–2297,3338–3342. Thus the GI-support range24420–30095 remains not fully read, **except that26819–26929 now has a direct scoped correction read**. The20 analytic transition source/TeX passage checks all pass. Current214 contracts uniform-existence.json and source-carry.json were inspected for the nine obligation arguments, and source-carry-sources.json for CARRY-GI/CARRY-GAUSSIAN; these historicalV15 locators are superseded as receiving-source choices by the explicit current foundation transition.
