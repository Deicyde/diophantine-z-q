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

## Step 4: compiler/bridge/size sections; upstream Lean
- n5_vs_v16.txt has no changed block inside N5 l.5745-6442 (sec:compiler, sec:bridge, sec:size): those sections are verbatim in v16. Changes nearest: N5 4364 (V 5346-5347), N5 6474/6477/6494 (corollaries section, V 7457-7483). VERIFIED.
- Primary-applications table: N5 l.6812 "Primes {greentao,moebius,gtz,bmor}" -> v16 l.13326 "{greentao,moebius,bmor} and Section v15:gi-full"; Height row N5 l.6808 pan2022 -> v16 l.13321 calegari-icm2022 (H domain). bmor bib v16 l.39400 (BMOR 2018 Thm 1.2) still the CAT source.
- RC section N5 1765-1767, 1779-1784 -> v16 2582-2600, 2612-2677: non-CM proof and modularity citation expanded (Silverman C.13.6, Shimura factors, Faltings isogeny). Expository; RC is off the fork's path (Route K + CR3).
- Upstream lean/ (d76bcde): 60 files; sha256 identical to fork's lean/ except README.md (upstream adds that Frozen target is for the original 292,890,231,905-variable polynomial, not the quartic). lean/Frozen/BoundedIntegerPolynomial.lean identical => ZInQKernel/Target.lean FrozenTarget unchanged. No quartic frozen target upstream. VERIFIED.

## Step 5: RC-domain changes; theorem-application audit
- Remaining N5->v16 changes in N5 l.1760-5745 (RC, Sections 5-8) and appendices (N5 6825-10935): RC citations repaired/replaced: N5 1793-1794 dd Thm 1.8 -> v16 2686-2689 ddselmer Thm 1.4; N5 1886 -> v16 2781-2785 adds Kato 1999 Thm 0.8 at 2; N5 2523 Cornut-Jetchev -> v16 3448-3449 internal Section v15:cm-oriented; N5 9195-9274 (62 lines CJ specialization) -> v16 15853-15874; N5 2638 -> v16 3564-3568 (filter clarification); N5 3991-3993 -> v16 4955-4956; N5 4364 -> v16 5346-5347. All on RC/PC path, which the fork does not use (Route K + CR3). VERIFIED (read).
- Corollaries N5 6474/6494 -> v16 7457-7483 (Mazur Conjectures 2/3 wording); sources N5 6608-6613 -> v16 13022-13027. Off path.
- docs/theorem-application-audit: upstream 108 files vs fork 107; only differences: upstream adds source/audited-baseline.tex (sha256 cb1148cd... = fork's diophantine_zq.tex exactly), README/INVENTORY/SOURCES repoint links to it and add header "Historical inventory ... binds only source/audited-baseline.tex" (pointer to ../../quartic_12504.tex), coverage.json manuscript_path changed. No new applications, findings or open items. VERIFIED.

## Step 6: MW, catalogue, assembly, H statement; TZ paper; route AP vs quartic prime input
- MW over Q(sqrt2): N5 273-275 -> v16 369-371 (class number one now via norm-Euclidean; units listed). N5 l.295 rank-one step unchanged. Fork proves MW in Lean (ZInQ.mordellWeilE): unaffected.
- Catalogue: N5 238-241 (first 22 primes above 324), 1340-1341, 6273, 6694-6695 all in matched blocks (verbatim in v16). bmor (BMOR 2018 Thm 1.2) still cited (v16 l.13326, bib 39400). CAT8 unaffected.
- lem:assembly N5 l.110, v16 l.204; N5 l.86-138 changed only at 86 (Mazur citation) and 138 (link to SUPPORTING-NOTES). Assembly unchanged.
- thm:height statement N5 403-418 = v16 706-721 (diff -w empty); H6 constants N5 389-397 = v16 491-499; v16 l.500-502 says modularity now via "published prime-five modularity theorem" (proof change, H domain; table row v16 l.13321 calegari-icm2022 replaces pan2022).
- v5tz = Tao-Ziegler, Polynomial patterns in the primes, Forum Math Pi 6 (2018) e1 (bib v16 l.39215-39219), Thms 9, 11, 13, 15, Cor 3. Fork's GreenTaoDense docstring (ZInQKernel/Hypotheses/GreenTao.lean:36-50) cites Tao-Ziegler Acta 201 (2008) only as background; statement proved in Lean (ZInQKernel/External/GreenTaoDense.lean:28). No dependence on v5tz.
- v16 TZ paragraph l.20060-20078: W = E * prod_{p<=v} p with fixed E; unit residue kills small-prime divisibility; "same uniform estimates" (precision amendment). Applies only to thm:v5-simultaneous-primes (quartic prime input: p_j = u + c_j w^2, Gaussian generator congruences mod 16, 7, M, cross-coprimality of d_eps(pi_j), d_eta(pi_h)), v16 l.17565-17590. Sun 86 unknowns arXiv:2610.20691v2 is the strategy source (bib l.39185).
- GI Part intro v16 l.23831-23875: target GI(k) as a finite family of nilmanifolds, constants dependent only on k, delta. Upstream's rationale for replacing GTZ Thm 1.3 by a local proof not located (searched v14/v15 READMEs, release notes).

## Step 7: v13/v14/v15 alignments (scratch/up-rest/n5_vs_v13.txt, _v14, _v15)
- Matched N5 lines: v13 11232, v14 10851, v15 10847, v16 10846.
- In fork-relevant N5 ranges (52-376 spec/model, 1123-1760 mult/22P, 5745-6442 compiler/size):
  v13 only 86, 1172-1174, 1194-1198; v14 adds 138, 273-275, 1265, 1408, 1416-1418; v15 adds 163-164; v16 = v15 (same N5 block list except 11253 = AI credit "Fable 5.1 and 5.2").
- v15-only blocks vs v14: N5 163-164, 8102 (-> v15:theta-transport), 9623 (-> v15:unary-poisson), i.e. v15 internalizes supplements as sections: v15:gi-full (Part, v16 23831), v15:cm-oriented (30163; replaces v14's external cj-conductor-one-project, v14 l.3424), v15:picard-norm (30124), v15:tate-polarized (30096), v15:marking-descent (30109), v15:unary-poisson (23770), v15:theta-transport (23810).
- Fork's earlier note docs/research/v14-routes.md already covers v13->v14 (statements byte-identical; GI source -> local-gi; RC repairs; quartic prime input harder than GreenTaoDense+GoodPrimeDensity).

## Step 8: v15 -> v16 reconstruction (scratch/up-rest/v15_to_v16.py)
- Applying EDITS.json (8 edits, each old string unique) to research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex gives EDITS.sha256; then EDITORIAL-AMENDMENT.json edits and TZ-PRECISION-AMENDMENT.json give a file byte-identical to manuscripts/quartic_v16.tex. So v15 -> v16 changes are exactly those. VERIFIED.
- v16 FINDINGS.json: 4 findings (horizontal-normalization: "missing at finite-cover site"; GR-citations: "wrong Gaudron-Remond paper"; TZ-extra-factor: wording implied direct application, "no mathematical replacement"; Bogolyubov-number: withdrawn). unclosed_audit_scope: Kato 1999 pp.314-318, Ribet 1990 pp.440-443 unread (both RC path: v16 l.2781-2785, 15105-15116); full changed-modulus TZ re-derivation not done by Fable.
- Fork trust notes: cr3-trust.md and h-trust.md cite neither Kato 1999 nor Ribet 1990 (grep). 
