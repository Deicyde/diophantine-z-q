# Upstream Versions 13–16 and the fork's other inputs: 22P, CAT, MW, compiler, size, Lean, audit

Status: research note, 2026-11-11 (task up-rest). Every claim is marked:
**VERIFIED** (read in the source, with version and line numbers, or checked by a script in
`scratch/up-rest/`), **STANDARD** (published theorem, reference given) or **SPECULATIVE**.
The step-by-step record is `scratch/up-rest/log.md`.

Sources. N5 = `diophantine_zq.tex` (11/5, sha256 `cb1148cd…`). Upstream (read-only clone, branch
`codex/version16-fable-corrections`, commit d76bcde, 2026-11-11):
`manuscripts/quartic_v13.tex`, `quartic_v14.tex`, `quartic_v16.tex`, and Version 15 at
`research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex`. "V16 L" etc. are line
numbers of those files (the files use CRLF; line counts are unaffected). The H domain (Theorem 4.1's
proof) and the CR₃/RC domain are covered by other tasks; this note touches them only where
Version 16's corrections or the verdict require it. It continues `v14-routes.md`, which compared
N5, Version 13 and Version 14; what that note established is not repeated here.

## Verdict

1. **Nothing in Versions 13–16 breaks or weakens a fork statement (VERIFIED).**
   - Theorem 1.1 (`thm:target`) is the same text in N5 L60-77, V13 L87, V14 L87, V15 L113 and
     V16 L113-130 (`diff -w` of N5 L60-77 against V16 L113-130 is empty; the only byte
     difference is CRLF).
   - The polynomial data are the same: all 28 files of `construction/` are byte-identical
     between the fork and upstream, except `README.md`, which upstream retitles "Original large
     construction". `ordinary-integer-definition.json` has sha256 `4d639d4c…af6` in the fork, in
     upstream `construction/` and in the V15 snapshot `v15-018`.
   - Upstream's `lean/` (60 files) is byte-identical to the fork's `lean/` except `README.md`.
     In particular `lean/Frozen/BoundedIntegerPolynomial.lean` is unchanged, so
     `ZInQ.FrozenTarget` (`ZInQKernel/Target.lean`) still states upstream's frozen theorem.
   - Version 16 is exactly Version 15 plus the eight recorded edits, the editorial amendment
     and the precision amendment: `scratch/up-rest/v15_to_v16.py` applies
     `research/version16/EDITS.json`, `EDITORIAL-AMENDMENT.json` and
     `TZ-PRECISION-AMENDMENT.json` to the V15 source and reproduces `quartic_v16.tex` byte for
     byte.
2. **None of Version 16's three corrections touches anything the fork formalizes or assumes
   (VERIFIED, §3).** The horizontal normalization (V16 L26821-26842, L26908-26915) is inside
   the polynomial inverse theorem part `v15:gi-full`. The Gaudron–Rémond citations
   (V16 L30664, L30677) are in the 222-variable family's height argument. The Tao–Ziegler
   adaptation (V16 L20060-20078) is in the quartics' simultaneous-prime appendix. The precision
   amendment changes one sentence of that same paragraph.
3. **Route AP still applies to the large construction (VERIFIED, §1).** Proposition 6.2 and
   the slope predicate it serves are unchanged in Versions 13–16. Upstream keeps 22P and changes
   only where its inverse-theorem input comes from: N5 and V13 cite GTZ Theorem 1.3; V14 cites
   an external supplement; V15 and V16 cite the in-manuscript part `v15:gi-full`. Version 16's
   first correction repairs a step in that part ("missing at finite-cover site",
   `research/version16/FINDINGS.json`). So until 11-11 upstream's own justification of 22P had
   a gap that the fork never depended on: route AP uses no inverse theorem.
4. **What to adopt: nothing is required.** Two optional record updates (§5): a status line in
   the 22P passages, and a pointer for the H trust statement to the supplements that Version 15
   moved into the manuscript.

## 1. 22P and route AP

**The large construction keeps 22P verbatim (VERIFIED).**
- `prop:fixed-prime-pattern` sits at N5 L1267, V13 L1385, V14 L2052, and V15/V16 L2076.
- `scratch/up-rest/n5_in_v.py` aligns N5 against each version line by line (difflib on
  right-stripped lines). Of N5's 11,259 lines, 11,232 / 10,851 / 10,847 / 10,846 appear in
  order in V13 / V14 / V15 / V16. The changed blocks are listed in
  `scratch/up-rest/n5_vs_v1{3,4,5,6}.txt`.
- In N5's multiplication-and-22P range (L1123-1760), V16 changes only:
  - L1172-1174 → V16 L1951-1958: the conjugation σ applied to the primed ratio, A_i − σ(A′_i),
    is spelled out;
  - L1194-1198 → V16 L1978-2007: the valuation deduction at a positive odd contact prime is
    written out;
  - L1265 → V16 L2074: a TeX comment (bibliography keys);
  - L1408 and L1416-1418 → V16 L2217 and L2225-2228: the source of GI(20).
- The polynomial file is unchanged, so the first two are expository. The fork's Lean proves its
  own construction in any case, so a text clarification cannot change a Lean statement.

**The GI(20) source across versions (VERIFIED).**
| version | proof of Prop. 6.2: GI(20) supplied by | line |
| --- | --- | --- |
| N5, V13 | GTZ Theorem 1.3 (arXiv v5 with erratum) | N5 L1408, L1416-1418; V13 L1526 |
| V14 | external `local-gi` supplement, "Assembly, Sections 1 and 6" | V14 L2193 |
| V15, V16 | in-manuscript Part "The polynomial inverse theorem and its local joins" (`v15:gi-full`, V16 L23831-30184) | V16 L2217, L2225-2228 |

The part states its target GI(k) as a finite family of nilmanifolds, with constants depending
only on k and δ (V16 L23847-23859). The primary-application table changes from
"greentao, moebius, gtz, bmor" (N5 L6812) to "greentao, moebius, bmor and Section v15:gi-full"
(V16 L13326). I did not find upstream's stated reason for replacing GTZ Theorem 1.3 by a local
proof (searched the V14/V15 READMEs and release notes).

**Route AP is unaffected and still applies (VERIFIED for the inputs; the route itself is proved
in Lean).** Route AP (`nt-22p.md`) needs:
- the unchanged polynomial (VERIFIED above);
- the unchanged slope predicate (N5 L1177-1235; V16 changes only exposition, above);
- `GreenTaoDense`, a Lean theorem (`ZInQKernel/External/GreenTaoDense.lean:28`);
- `GoodPrimeDensity`, a Lean theorem (`ZInQ.Density.goodPrimeDensity`).

None of these uses GI, the Möbius–nilsequence theorem or the linear-equations asymptotic. The
docstring of `GreenTaoDense` (`ZInQKernel/Hypotheses/GreenTao.lean:36-50`) cites Tao–Ziegler,
Acta Math. 201 (2008), only as background. That is a different paper from the Tao–Ziegler paper
that Version 16 adapts, `v5tz` = *Polynomial patterns in the primes*, Forum Math. Pi 6 (2018)
(V16 L39215-39219).

**The quartics replace 22P by a different prime input (VERIFIED).**
- That input is `thm:v5-simultaneous-primes` (V16 L17565-17590, section V16 L17544,
  strategy from Sun, arXiv:2610.20691v2, bibliography V16 L39185).
- It asks for primes p_j = u + c_j w² with Gaussian generators in fixed classes mod 16, 7 and
  M, and with odd coprimality between the adjacent norms d_±(π_j) **across different j**.
- It is cited only by the quartic sections: V16 L11798, L12269, L12354, L20433 and
  L31156-32268. A grep for the `v5` labels and for `v5tz` in V16 L1-7586 and L13005-17543
  (the large construction and its appendices) finds nothing.
- As `v14-routes.md` §5.4 already assessed (SPECULATIVE): Tao–Ziegler 2008 handles the
  polynomial shape and the per-prime conditions, but not the cross-j coprimality. So route AP
  does not transfer to the quartics as is. This does not matter for the fork, whose target is
  the large polynomial.

## 2. CAT, Mordell–Weil over ℚ(√2), compiler, assembly, size bounds

All VERIFIED from the alignment (`n5_vs_v16.txt`) and direct reading:
- **Compiler, bridge, size** (N5 L5745-6442: `sec:compiler`, `sec:bridge`, `sec:size`). Not
  one changed block in V16; the sections are verbatim. The same holds in V13–V15.
- **Catalogue (CAT).**
  - The catalogue definition (N5 L238-241), the Dirichlet step in Prop. 6.2 (N5 L1340-1341),
    the catalogue product in the size section (N5 L6273) and the literal specification
    (N5 L6694-6695) are all verbatim in V16.
  - The source is still Bennett–Martin–O'Bryant–Rechnitzer, Illinois J. Math. 62 (2018),
    Theorem 1.2 (V16 L39400-39403).
  - The fork's `ZInQ.catalogueBound8` proves the weaker CAT₈ that its proof needs, so it is
    unaffected.
- **Mordell–Weil over ℚ(√2).**
  - N5 L273-275 → V16 L369-371 (since V14): class number one is now justified by norm-Euclidean
    instead of the Minkowski bound, and the units are listed.
  - The rank-one step (N5 L295) is unchanged.
  - The fork's `ZInQ.mordellWeilE` is a Lean proof, so it is unaffected.
- **Assembly** (`lem:assembly`, N5 L110 = V16 L204). In N5 L86-138 only L86 (a Mazur citation,
  V16 L139-142) and L138 (a link to `research/version14/SUPPORTING-NOTES.md`, V16 L232) change.
- **Theorem 4.1's statement**, which the fork's H instantiates, is unchanged: N5 L403-418 =
  V16 L706-721 (`diff -w` empty), and the constants of `H₆(S;R)` are equal (N5 L389-397 =
  V16 L491-499). The proof changed, which is the H task's domain. V16 L500-502 names "the
  published prime-five modularity theorem", and the application table changes from `pan2022`
  to `calegari-icm2022` (N5 L6808 → V16 L13321).

## 3. Version 16's three corrections and the precision amendment

The corrections are located by an exact search of `EDITS.json`'s replacement strings in
`quartic_v16.tex` (VERIFIED). The findings are quoted from `research/version16/FINDINGS.json`.

| correction | what it corrects | V16 lines | consumer | fork |
| --- | --- | --- | --- | --- |
| horizontal normalization | the lattice-valued binomial correction of the orbit, needed to make the horizontal Taylor identities exact before rational/small coordinates are removed, was "missing at finite-cover site" (it already appeared later in V15). Fixed real lifts are divided by M on passing to the finite covering lattice | L26821-26842, L26908-26915 | `v15:gi-full`, hence GI(20) for Prop. 6.2 (V16 L2217), the quartic prime-pattern arguments (V16 L9565, L10406, L19476-19704) | not used: route AP needs no inverse theorem |
| Gaudron–Rémond citations | two inequalities (a stable Faltings-height lower bound; the ½ log D height change under an isogeny) cited the Duke paper; they are in *Théorème des périodes et degrés minimaux d'isogénies*, CMH 89 (2014) 343–403, §2.3 and Cor. 8.4 (new bibliography entry V16 L39342-39346) | L30664, L30677 | subsection "An abelian surface occurring as an isogeny factor" (V16 L30630) of the 222-variable family's height argument | not used. The six-contact proof keeps Duke Theorem 1.4 and §9 (V16 L1322, L1599, L1616 = N5 L615, L878, L895, same bibliography entry N5 L11063 = V16 L39347), and the fork's notes cite only those (`h-trust.md:672`, `h-v14.md:229,257,258`) |
| Tao–Ziegler adaptation | wording "implied direct published theorem application". The modulus is W = E·∏_{p≤v} p with a fixed extra factor E, so the modulus-dependent results (Thm. 11, Cor. 3, Thm. 13, Thm. 15) are used through adapted proofs; Thm. 9 is modulus-free. "No mathematical replacement made" | L20060-20078 | `thm:v5-simultaneous-primes` (quartics only) | not used |
| precision amendment | one sentence: the divisor-sum local factors "satisfy the same uniform estimates" instead of being "unchanged" | in L20060-20078 | same | not used |

The withdrawn Bogolyubov-numbering objection changes nothing. Fable's unclosed scope (Kato 1999
pp. 314–318 and Ribet 1990 pp. 440–443 unread; the full changed-modulus Tao–Ziegler proof not
re-derived) lies on the RC path (V16 L2781-2785, L15105-15116) and on the quartic prime input.
Neither `cr3-trust.md` nor `h-trust.md` cites Kato 1999 or Ribet 1990 (grep).

**The fork's Lean and notes need no change** (VERIFIED for the Lean and the statements above;
whether to add the optional record lines of §5 is a judgment call).

## 4. Upstream's Lean and theorem-application audit

- **Lean (VERIFIED).**
  - Upstream `lean/` equals the fork's copy (sha256 of all 60 files) except `README.md`. That
    file adds that the frozen target is for the original 292,890,231,905-variable polynomial and
    that no quartic frozen target exists.
  - It contains only finite lemmas (axioms recorded in `lean/AXIOMS.json`: subsets of propext,
    Classical.choice and Quot.sound) and the single `sorry` in `Frozen/`.
  - It assumes nothing beyond that, so nothing there supersedes or contradicts the fork's
    hypotheses H and CR₃.
- **Theorem-application audit (VERIFIED).**
  - Upstream's `docs/theorem-application-audit/` has 108 files to the fork's 107.
  - The added file `source/audited-baseline.tex` has the same sha256 as the fork's
    `diophantine_zq.tex`. `README.md`, `INVENTORY.md` and `SOURCES.md` now point there.
  - A header now marks the inventory "historical", binding only that baseline.
    `coverage.json` changes only its `manuscript_path`.
  - No application, finding or open item is added or changed: OPEN_ITEMS still reports none
    open in the 82 families, and FINDINGS F001–F008 are unchanged.
  - Later application records are per version and cover changed sites only. Version 16's
    `research/version16/APPLICATIONS.json` has three entries, the three corrections of §3.
  - So the audit the fork already carries is still upstream's audit of N5. Nothing in it
    contradicts SixContactMin or CertifiedRank.

## 5. Recommendations

1. **No change to Lean statements, `FrozenTarget`, or the hypotheses (VERIFIED basis, §§1-4).**
2. **Optional record line (SPECULATIVE value).** Wherever the fork describes upstream's
   justification of 22P (KERNEL_PLAN's 22P row, `nt-22p.md`, `v14-routes.md` §2.4), its
   owners could add that:
   - from Version 15 upstream proves GI(20) in the manuscript (`v15:gi-full`);
   - Version 16 corrected a missing normalization step there (V16 L26821-26915).

   This is one more reason the narrowest variant does not take 22P.
3. **For the H trust statement (pointer only, not this task's scope).** Version 15 moved
   several supplements into the manuscript as sections: `v15:tate-polarized` (V16 L30096),
   `v15:marking-descent` (L30109), `v15:picard-norm` (L30124), `v15:cm-reduction` (L30134),
   `v15:cm-oriented` (L30163, replacing V14's external `cj-conductor-one-project`, V14 L3424),
   `v15:unary-poisson` (L23770) and `v15:theta-transport` (L23810). The ones on the
   six-contact path may be worth citing at their V16 lines in `h-trust.md`.
4. **For later versions.** `scratch/up-rest/n5_in_v.py` (N5 alignment) and
   `scratch/up-rest/v15_to_v16.py` (edit-record replay) can be rerun on a Version 17 in a few
   minutes.
