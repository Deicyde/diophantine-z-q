# up-map: upstream manuscript versions after N5

This note maps the versions of upstream's manuscript after N5 for the sibling tasks up-h, up-cr3
and up-rest. "Upstream" means the read-only clone `~/upstream` (branch
`codex/version16-fable-corrections`, commit d76bcde, 11-11). The 214-variable proposal is in
`~/upstream-p214` (branch `proposal/quartic-214-protocol-d`, commit 110cf72, 11-11). N5 is
`diophantine_zq.tex` in this repository.

Tags. **VERIFIED**: read in the source, cited by version, file and line, or checked by a script
under `scratch/up-map/`. **STANDARD**: a published theorem, cited by reference. **SPECULATIVE**:
an inference that has not been checked. Line numbers in upstream TeX files are physical lines
(V14–V16 use CRLF line endings; compare them with `diff --strip-trailing-cr`).
`scratch/up-map/log.md` records every step.

Scripts (all in `scratch/up-map/`):
- `extract.py FILE LABEL` prints a labelled environment.
- `secdiff.py A B` gives per-section diff counts, with sections matched by title. The
  N5→V2→…→V16 chain output is in `secdiff-chain.txt`.
- `refmatrix.py FILE labels…` lists, for each section, the `\ref`s to the given labels.
- `thmnum.py FILE labels…` computes printed theorem numbers. Its output is in
  `thmnum-table.txt`.

## 0. Summary

1. **Upstream never withdrew or changed the N5 construction (VERIFIED).** Every version from V2
   to V16 keeps N5's Theorem 1.1, the 292890231905-variable polynomial, in its abstract and
   body, and its statement is byte-identical.
   - The same holds for these statements: Assembly; Generator certificate; Theorem 4.1
     (six-contact estimate, with the same constants); Theorem 5.2 (PC, same pole polynomial and
     pole template E_ℓ: y² = x(x−ℓ)(x+3ℓ)); Theorem 5.3 (RC); Proposition 6.1 (finite box);
     Proposition 6.2 (22P); the catalogue definition; Proposition 12.1 (literal cutoff).
   - Compared with `extract.py` (§3 below).
   - §§9–12 of N5 (limits, compiler, bridge, cutoff and size, including the catalogue bound) are
     byte-identical in V16.
2. **Proofs were changed in two versions: V10 (Issue 2 review) and V14. V15 inlined two V14
   supplements. V16 changes none of the N5 core (VERIFIED).** The changes that matter for the
   fork:
   - **H (Theorem 4.1, numbered 4.2 from V14 on).**
     - The modularity step changed. N5 had "a direct modularity argument at coefficient prime
       five" plus a de Rham descent appendix. From V14 the proof uses a new Lemma 4.1
       (`lem:qm-modularity-descent`), built on the *published* prime-five modularity statement
       \[Calegari, ICM 2022, p. 624\] (proof source Pan).
     - The integral-model step was expanded into six phases, with proofs in §§`v15:marking-descent`
       and `v15:tate-polarized`.
     - Four project proof supplements under `research/version14/proofs/` are cited.
     - Constants and statement are unchanged.
   - **22P (Proposition 6.2).** The Green–Tao–Ziegler inverse theorem \[GTZ, Thm 1.3\] (used in
     N5–V13) was replaced in V14 by a project supplement (`local-gi`). From V15 it is replaced by
     an internal proof of GI(k), the ~6000-line Part `v15:gi-full`. V16's second correction
     sits inside that Part.
   - **PC/RC.** Statements and the descent reduction are unchanged. The proofs gained citations
     and detail: Silverman C.13.6 for BCDT, Kolyvagin, an explicit J₁(N)→A map, and
     \[ddselmer\] for parity. RC is now said to be a special case of two OpenAI 2-converse
     preprints, which are cited for attribution only.
3. **Upstream's new results do not run through H, PC or 22P (VERIFIED by `refmatrix.py`).**
   - The quartics (12504 down to 299/314 variables) and the 222-variable family use different
     inputs:
     - a *five-contact* height estimate (contacts ∞, 0, 1, 2401, −343/32, via a
       discriminant-210 Shimura curve);
     - a seven-variable pole lemma proved from RC;
     - a simultaneous-prime theorem for ℤ[i], proved in an appendix following Sun's strategy;
     - GI.
   - The 222-variable family adds Von Buhren's semi-effective height bound, which makes its
     threshold N₀ ineffective.
   - The 214-variable proposal says explicitly that the six-contact input is "not needed".
   - So upstream's newest work relies on RC but not on H or PC. The fork's FrozenTarget still
     rests on N5's construction, which V16 keeps verbatim.
4. **The three V16 corrections (VERIFIED by diff V15→V16).**
   - Tao–Ziegler dense-model results are now "adaptations of their proofs", in the
     simultaneous-primes appendix.
   - Exact horizontal identities were added in GI §9–11.
   - A Gaudron–Rémond citation in the 222-family height section was corrected.
   - None touches a line of §§1–13 of the N5 core.
   - The GI correction does sit inside the inverse theorem that the 22P proof consumes (V16
     l.2217). It does not affect the fork, whose route AP uses neither GTZ nor upstream's GI.
5. **One new upstream record bears on the fork's H leaves (VERIFIED).**
   - `research/version14/proofs/a001-moduli-current-v1/ADVERSE-CASE.md` records a defect in the
     proof of Baba–Granath (CJM 2008) Prop. 3.7, with a counterexample to a printed sentence.
     The weighted-Igusa formula of Lin–Yang eq. (2) descends from Baba–Granath Prop. 3.9.
   - The fork's h-trust.md cites Baba–Granath 2008 and Lin–Yang 2020 directly (l.89). up-h
     should check this ancestry; see §5.1.
   - Otherwise H's proof is the same in V14, V15 and V16, apart from the inlined integral model.
     The fork's `h-v14.md` therefore carries over to V16 (§3.1).

## 1. Version table

All files are under `~/upstream` unless noted. Dates are the `\date` lines (VERIFIED).

| Version | File | Date (line) | Main theorems (beyond the N5 polynomial) |
| --- | --- | --- | --- |
| N5 | `diophantine_zq.tex` (this repo) | Nov 5 (l.37) | Thm 1.1 only: P ∈ ℤ[X₀..X_292890231904], deg < 2↑↑7, coeffs < 2↑↑8 |
| Oct 11 | `October 11 Manuscript/ZIsDiophantineInQBySohailsGPT-6.pdf` | Oct 11 (README l.3) | Conditional on four inputs from OpenAI's HTP preprint. No variable count. Degree ≤ 4 conversion (Thm 1.2, p.2) |
| V2 | `manuscripts/archive/quartic_12504.tex` | Nov 5 (l.37) | N5 Thm 1.1 + explicit quartic, 12504 vars, 135721 monomials, coeffs < 2^80 (abstract l.40, `thm:quartic` l.8688) |
| V3 | `manuscripts/archive/quartic_9625.tex` | Nov 6 (l.37) | quartic, 9625 vars, 82476 monomials, < 2^80 (abstract l.40, l.8688) |
| V4 | `manuscripts/archive/quartic_4973.tex` | Nov 6 (l.41) | quartic, 4973 vars, 72925 monomials, < 2^80 (abstract l.44, l.8695) |
| V5 | `manuscripts/archive/quartic_1272.tex` | Nov 6 (l.41) | + quartic 1272 vars, 48001 monomials, max coeff 64·3^(2^28) (`thm:v5-1272-polynomial` l.10556). Adds the appendix "Simultaneous primes with coprime adjacent norms" (l.15831) |
| V6 | not in tree. GitHub release `quartic-962-version-6`, pinned to snapshot a9e834b (`releases/quartic-962-version-6/README.md`) | — | 962-variable quartic + degree-four lower bound (release README) |
| V7 | `manuscripts/archive/quartic_v7.tex` | Nov 6 (l.41) | 4973 + 962-var quartic (55409 monomials; l.11217). "Degree at least four" section |
| V8 | `manuscripts/archive/quartic_v8.tex` | Nov 6 (l.41) | Same polynomials. Abstract states that the minimum degree is 4 (l.44) |
| V9 | `manuscripts/quartic_v9.tex` | Nov 7 (l.41) | quartics in 540 vars (coeff < 2^3247) and 523 vars (64·3^(2^27)) (`thm:v9-quartics` l.18807) |
| V10 | `manuscripts/quartic_v10.tex` | Nov 7 (l.41) | Same tables. Issue 2 response (V10 l.122–126; V16 l.155–159) |
| V11 | `manuscripts/quartic_v11.tex` | Nov 7 (l.41) | Same tables. Kato index-set repair in App "Fixed-form arithmetic" |
| V12 | `manuscripts/quartic_v12.tex` | Nov 7 (l.41) | quartics in 514 vars (< 2^3247) and 498 vars (16·3^(2^26)) |
| V13 | `manuscripts/quartic_v13.tex` | Nov 7 (l.41) | quartics in 411 vars (6388 monomials) and 394 vars |
| V14 | `manuscripts/quartic_v14.tex` | Nov 9 (l.41) | quartics in 314 vars (6672 monomials, < 2^6496, decimal table 264430 bytes) and 299 vars (186624·3^(2^26)) |
| V15 | `research/version15/snapshots/v15-222-004/manuscript/quartic_v15.tex` | Nov 10 (l.42) | Thm 1.1 = 314-var decimal quartic (l.98). Thm 1.2 = 222-variable family P_N, N ≥ N₀ *ineffective* (l.104). Thm 1.3 = N5 polynomial (l.113) |
| V16 | `manuscripts/quartic_v16.tex` | Nov 11 (l.42) | Same three theorems (l.98, 104, 113) |
| p214 | `~/upstream-p214/research/quartic214/{README,PROOF}.md` | Nov 11 (PROVENANCE.json) | proposal: 214-variable family, N ≥ N₀ ineffective, review pending (README l.3–11) |

All versions are effective except where marked. In each quartic version the quartic is
explicit, with a specified coefficient table. V15/V16 Thm 1.2 and p214 are not effective: no
member P_N is certified (V16 l.109; p214 README l.11).

**Relation to FrozenTarget.** FrozenTarget is N5's Thm 1.1: the polynomial P_*, 292890231905
variables, deg < 2↑↑7, coeffs < 2↑↑8. Every version V2–V16 restates it verbatim.
- In V2–V14 it is `thm:target`, Theorem 1.1. In V15–V16 it is Theorem 1.3, at l.113–129.
- The abstract of every version opens with it (VERIFIED, abstracts l.40–58).
- The quartics are different polynomials. They are not reductions of P_*: they come from
  a separate construction, the base residual compiler of §`sec:degree8-original`, described
  in §2.3 below.

## 2. Where the N5 inputs live in each version

### 2.1 Labels and line numbers (VERIFIED by grep and `thmnum.py`)

| Version | thm:target | thm:height (H) | hyp:PC | hyp:RC | prop:fixed-prime-pattern (22P) | prop:cutoff |
| --- | --- | --- | --- | --- | --- | --- |
| N5 | 60 (1.1) | 404 (4.1) | 1001 (5.2) | 1005 (5.3) | 1267 (6.2) | 6285 (12.1) |
| V2 | 63 | 415 | 1012 | 1016 | 1278 | 6296 |
| V3 | 63 | 415 | 1012 | 1016 | 1278 | 6296 |
| V4 | 72 | 424 | 1021 | 1025 | 1287 | 6305 |
| V5 | 76 | 432 | 1029 | 1033 | 1295 | 6313 |
| V7 | 76 | 435 | 1032 | 1036 | 1298 | 6316 |
| V8 | 71 | 430 | 1027 | 1031 | 1293 | 6311 |
| V9 | 78 | 445 | 1042 | 1046 | 1308 | 6326 |
| V10 | 87 | 473 | 1073 | 1083 | 1378 | 6464 |
| V11 | 87 | 473 | 1073 | 1083 | 1378 | 6464 |
| V12 | 87 | 480 | 1080 | 1090 | 1385 | 6471 |
| V13 | 87 | 480 | 1080 | 1090 | 1385 | 6471 |
| V14 | 87 (1.1) | 682 (4.2) | 1712 | 1722 | 2052 | 7244 |
| V15 | 113 (1.3) | 707 (4.2) | 1736 | 1746 | 2076 | 7268 |
| V16 | 113 (1.3) | 707 (4.2) | 1736 (5.2) | 1746 (5.3) | 2076 (6.2) | 7268 (12.1) |

V2–V13 use N5's numbers: 1.1, 4.1, 5.2, 5.3, 6.2, 12.1.

### 2.2 Section-level changes to the N5 core (VERIFIED, `secdiff-chain.txt`)

- **N5→V2.** Changes:
  - §1 gains 8 lines (the quartic mention).
  - The de Rham appendix gains 64 lines.
  - Two sections are added: "The base residual compiler" (l.6602) and "An explicit quartic
    definition of the integers" (l.8679).
  - Core §§2–13 are unchanged.
- **V2→V9.** Only §1, the de Rham appendix and the quartic sections change. The appendix gains
  12 lines at V2→V3 and 7 at V3→V4, then shrinks from 397
  to 75 lines at V4→V5 (V5 l.15755). The "Simultaneous primes" appendix is new in V5 and grows
  in V7 and V9.
- **V9→V10 (Issue 2).** Small additions throughout:
  - §3 +3, §4 +5, §5 +9, §6 +41, §7 +22, §8 +53, §13 +16;
  - App "Source identities" +8, App "Literal finite-constructor specification" +88 (the
    saved-template identification table), App "Fixed-form" +61.
  - V16 §1 l.155–159: "Version 10 clarified determinant specialization, the published prime-two
    Euler-system input, the local valuation deduction, and the identification of the saved
    templates … The polynomial specifications and numerical bounds are unchanged."
- **V10→V11.** Only App "Fixed-form arithmetic and the even coefficient source" changes (−10/+69).
  V16 §1 l.152–153: "Version 11's index-set and retained-class identification in the published
  Kato application".
- **V13→V14.** Changes:
  - §4 height: −146/+778.
  - §5 pole: −8/+43.
  - §7 RC: −12/+117.
  - App odd theta: −96/+59.
  - The de Rham appendix is GONE; its role passes to the new Lemma 4.1.
  - "Simultaneous primes": −71/+248.
- **V14→V15.** One-line citation changes in the core:
  - §4: five cites of the b11 supplement become internal sections;
  - §6: `local-gi` becomes `v15:gi-full`.
  The new parts are GI (l.23831–30083) and the 222 family (l.30185–39914).
- **V15→V16.** See §4.
- §§9–12 (two limits, compiler, bridge, cutoff/size) are byte-identical from N5 to V16.

### 2.3 Which inputs each construction uses in V16 (VERIFIED, `refmatrix.py`)

- **N5 polynomial (Thm 1.3).**
  - Inputs: thm:height, hyp:PC, hyp:RC, 22P. The V16 proof of the theorem is at l.216–234 and
    uses the same G, M, H, PC, C, B decomposition as N5 (V16 l.181–207).
  - §6 cites `v15:gi-full` at l.2217.
- **Base residual compiler** (§`sec:degree8-original`, l.7587):
  - F₈ in 15672 variables, degree 8 (prop:o8-finite l.7598).
  - Interpretation `thm:o8-conditional` (l.7612).
  - Inputs:
    - **five-contact height estimate** `hyp:o8-height` (l.7651–7656): h(a) ≤ H_* M₅(a)^24,
      contacts {∞, 0, 1, 2401, −343/32}, S_* = primes ≤ 76176, log₂H_* < 4783227. The proof
      goes through the Shimura curve of discriminant 210 and González–Rotger 2006;
    - **seven-variable pole lemma** `hyp:o8-pole` (l.8803), proved from hyp:RC (l.8870).
  - V16 l.7622–7626 says that thm:height "uses a different contact set". The pole lemma "is not
    inferred from Theorem hyp:PC".
- **Explicit quartic** (l.9950, `thm:quartic` l.9957). Inputs: the sharper five-contact estimate
  `thm:quartic-height19` (l.10005) and GI (l.10406).
- **962-variable quartic** (l.11789, theorem l.12479). Inputs: `thm:v5-simultaneous-primes`
  (l.17565; Sun, arXiv:2610.20691v2, bib l.39185), hyp:o8-pole and hyp:o8-height.
- **523/540-variable quartics** (`sec:v9` l.20357). Inputs: thm:quartic-height19, hyp:o8-pole
  and simultaneous primes.
- **498/394/299/314.** `subsec:v12-inputs` (l.21018–21060) retains:
  - E: y² = x³ − Dx over K = ℚ(√2) with D = (3−√2)² and 2E(K) = ℤP;
  - hyp:o8-pole, `lem:original-seven-simultaneous-realization`, `lem:v5-one-place`;
  - H₁₉.
  `thm:v14-quartic` (l.22822) inherits these.
- **222 family** (Part l.30185).
  - Height sections: `v15:height` "effective contact height" (l.30186), amplification
    (l.30907), aggregate (l.31269).
  - The base248 height h(u) ≤ C₃ M₅(u)³(1 + log M₅(u)), with C₃ = 2^330770 (l.32427–32429).
  - A pole obstruction outside 2, 3, 17, and a simultaneous prime pattern (l.32432–32438).
  - Ineffectivity comes from Von Buhren's family height theorem: the slope is effective and the
    additive constant is not (l.31490–31519; bib l.39776).
- **None of the quartic or 222 sections refers to thm:height, hyp:PC or
  prop:fixed-prime-pattern.**

## 3. The four N5 inputs, version by version

### 3.1 Theorem 4.1, six-contact height estimate (H)

- **Statement.** Byte-identical in every version (N5 l.404–409; V16 l.707–712).
  - The constants block (F₀, D, G₀, E₀, Q_R, B_cm, C_cm, H₆) is identical: N5 l.390–400,
    V16 l.489–499.
  - Its number becomes 4.2 in V14+, because Lemma 4.1 is inserted before it. (VERIFIED)
- **N5–V13 proof.**
  - The section intro (N5 l.401–403) announces "a direct modularity argument at coefficient
    prime five and a separate effective CM argument".
  - The de Rham descent is in the appendix "De Rham comparison and finite descent in the height
    argument" (N5 l.10936).
  - Integral model: \[Buzzard, Thm 2.1, Cor 2.3\] applied to V₁(5) over ℤ[1/30] (N5 l.443–478).
  - Citations in N5 §4 + appendix: Lin–Yang, Gaudron–Rémond 2014 (Duke), Faltings 1983, Pan
    2022, Buzzard, Baba–Granath, Pazuki, cmheight, Li, Shimura, Scholze 2013, Brinon–Conrad,
    Silverberg–Zarhin, Javanpeykar. (VERIFIED, citation counts)
- **V14–V16 proof** (V16 §4 l.473–1704).
  - The intro (l.475–477) adds: "the preprint's height assertion is not taken as an additional
    premise". At l.501–503 the direct argument becomes "the published prime-five modularity
    theorem".
  - New **Lemma 4.1** `lem:qm-modularity-descent` (l.505–528, proof to l.692). For a QM abelian
    surface with a rational scalar descent, r₅ is the Tate realization of a weight-two newform.
    - Supplier: \[Calegari, ICM 2022, Vol. 2, p. 624\] (bib l.39652). Pan 2022, JAMS 35, is the
      proof source (bib l.39309).
    - Also used: Faltings 1986, Scholze 2013, Fontaine 1994, Deligne–Serre 1974, Kato
      (Astérisque 295), Washington, Shimura, Li.
  - "Scope of the modularity input" (l.694–705): the lemma does not claim that every input to
    Pan's proof has been reproved. It cites the project supplement
    `direct-p5-modularity-project` (bib l.39140).
  - Integral model (l.829–1141, the replaced hunk): six phases, with full proofs in §`v15:marking-descent`
    (l.30109) and §`v15:tate-polarized` (l.30096). Bib `b11-integral-model-project` (l.39281)
    points to `research/version14/proofs/b11-integral-model-v1`; it is listed but not cited in
    the text.
  - Other project supplements cited in §4: `a001-moduli-project` (l.748), `ly-d6-normalization-project`
    (l.781, 1203, 1633), `igusa-theta-project` (l.1647). Their files are under
    `research/version14/proofs/` (26 supplement directories).
  - New citations in V16 §4: Deligne 1971, Deligne–Serre, Kato, Calegari, Milne–Shimura 2005,
    Igusa 1967, Carayol 1987, Voight 2021, Serre–Tate. (VERIFIED)
- **V14 → V16 (VERIFIED, diff of V14 l.448–1680 against V15 l.473–1704, then V15 → V16).**
  - The only change in §4 after V14: five citations of `b11-integral-model-project` become
    §`v15:marking-descent` / §`v15:tate-polarized`.
  - So V16 §4 is V14 §4 with the b11 supplement inlined. The fork's `docs/research/h-v14.md`
    (the H trust leaves re-based on V14 §4) therefore applies to V16 §4 line for line, after a
    V14 → V16 offset of +25 lines (+24 after V14 l.785). The exception is the integral-model leaves, which now point
    into the manuscript.
- **Bearing on the fork.** h-b1.md replaces "the unpublished integral-model supplement" by Lemma PR.
  - Upstream now writes that integral-model construction out in the manuscript: V16 l.829 ff.
    and §`v15:marking-descent`.
  - Upstream's modularity step now goes through a published statement (Calegari ICM p. 624),
    replacing N5's direct argument.
  - Both are leads for up-h. Whether they change the trust statement in h-trust.md is up-h's
    question. (SPECULATIVE as to impact)

### 3.2 Theorem 5.2, pole completeness, and the pole template

- **Unchanged in V16 (VERIFIED, diff N5 l.973–1122 against V16 l.1705–1898):**
  - Q_pole with its eleven witnesses, S₀ = {2, 3, 5, 7, 13}, degree 75;
  - E_ℓ: y² = x(x−ℓ)(x+3ℓ), the template x + 3ℓ;
  - `lem:pole`, the PC and RC statements, and the descent-reduction text.
- **Additions:**
  - attribution to \[openaihtp, §3\] (l.1706–1707);
  - non-CM check via Fowler's class polynomial;
  - `lem:corank` cites Poonen–Stoll Cor. 4, 7 and Thm 8;
  - `lem:forward-rank` uses BCDT via Silverman Thm C.13.6, Kolyvagin Thm 1 (pp. 430–431), an
    explicit J₁(N) → A via a Picard norm (§`v15:picard-norm` l.30124), and Kato Cor. 14.3.
- No version replaces the template x + 3ℓ. The fork's Route K (x − ℓ, x + ℓ, congruent number
  curves) has no upstream counterpart in any version. (VERIFIED for every version's `hyp:PC` statement, which is byte-identical.)
- **VERIFIED by grep:** the phrase "congruent number" does not occur in V16.
  - In `~/upstream/research`, `docs` and the p214 proposal it occurs only in the retained copy of
    OpenAI's pointwise 2-converse preprint (`research/version14/retained-sources/parity-frozen-4eaee875.tex`
    l.291), in a literature remark on π/3- and 2π/3-congruent numbers.
  - The fork's congruent-number route (slot-k.md) and CR3 have no upstream counterpart.

### 3.3 Theorem 5.3, restricted converse (RC)

- **Statement identical (VERIFIED).**
- **V16 additions:**
  - l.1740–1744: RC "is the E = E_ℓ, s₂(E) = 1 case of \[openaipointwise, Thm 1.1\]" and
    follows from \[openaigoldfeld, Thm 1.1\]. Both are OpenAI preprints of 7 October 2026 (bib
    l.39551–39559), "cited for attribution, not assumed".
- **§7 changes (diff N5 l.1760–2717 against V16 l.2570–3651):**
  - organisation credited to openaipointwise (l.2571–2577);
  - explicit non-CM invariants (l.2582–2600);
  - modularity via BCDT, Silverman C.13.6/C.16.4, Amir–Hong Thm 3.1, Shimura Thm 1, Faltings 1983
    (l.2612–2677);
  - parity via \[Dokchitser–Dokchitser, Selmer, Thm 1.4\] instead of \[dd, Thm 1.8\]
    (l.2686–2689);
  - at the prime 2, \[Kato 1999, Thm 0.8\] (l.2781–2785);
  - a new paragraph "native genus lattice" (l.3317–3342);
  - Cornut–Jetchev Thm 3.1 replaced by §`v15:cm-oriented` (l.3448–3449).
- The fork does not use RC: Route K uses CR3. Upstream's quartics and the 222/214 families do
  use RC, through the seven-variable pole lemma.

### 3.4 Proposition 6.2, the twenty-two-prime pattern (22P), and the catalogue

- **Statement identical (N5 l.1267–1297; V16 l.2076–2106). VERIFIED.**
- **Inverse theorem in the proof:**
  - N5–V13 use \[Green–Tao, Main Theorem p. 1763\] + \[Green–Tao, Möbius, Thm 1.1\] +
    \[GTZ, Thm 1.3\], read in arXiv v5 with its erratum (N5 l.1405–1418).
  - V14 replaces GTZ with the supplement \[local-gi, Assembly §§1, 6\] (V14 l.2193; bib l.23990,
    "A local proof supplement for the required Gowers inverse theorem", 8 Nov 2026,
    `manuscripts/quartic-local-gi-supplement.pdf`).
  - V15 and V16 cite the internal Part `v15:gi-full` instead (V16 l.2217). This is the only §6
    change from V14 to V15.
  - The rest of the 22P proof is unchanged: catalogue, W-trick, Mertens, Dirichlet.
- **Part `v15:gi-full`** (V16 l.23831–30083) proves GI(k) in linear-nilsequence form, with no
  effective bounds (l.23849–23865). It consists of internal modules: GTZ-LP replacements,
  degree–rank induction, and others.
- **Other §6 changes (both from V10):**
  - The twelve tests are written explicitly as A_i − σ(A′_i), with conjugated primed ratios
    (V16 l.1951–1958; V10 l.1254). The template table of V10 (l.12079) identifies the saved
    `test_group`.
  - The fork's `ZInQKernel/Multiplication/Certificate/TestGroup.lean` already uses `Pair.val_conj`
    (l.272, 333). (VERIFIED as to the term; not re-audited.)
  - The valuation deduction at a contact prime is now written out (V16 l.1978–2007, against
    N5 l.1194–1198).
- **Catalogue.**
  - Definition: N5 l.238–245 = V16 l.331–338.
  - Bound: H_max < X = 2^{W³}, H_cat ≤ X^{22W}, log₂N_s < 2^2054, via \[BMOR, Thm 1.2, Cor 6.17\].
    In §12, N5 l.6296–6310; byte-identical in V16.
  - The fork proves this in the weaker form CAT8 (cutoff 2^(W⁸)), using its own effective
    Dirichlet theorem.
  - Upstream has not changed this statement. (VERIFIED)
- **The prime-pattern analog for the quartics** is `thm:v5-simultaneous-primes` (V16 l.17565).
  - It gives simultaneous Gaussian primes p_j = u + c_j w² with congruence conditions and coprime
    adjacent norms.
  - Its strategy follows \[Sun, 86 unknowns, arXiv:2610.20691v2\].
  - Its inputs are Mitsui, Green–Tao, transference and the Tao–Ziegler dense model. V15 applies
    Tao–Ziegler literally; V16 calls it an adaptation of their proofs (§4).

## 4. V15 → V16: the three corrections (VERIFIED, full diff)

1. **Simultaneous-primes appendix** (V16 l.20060–20077, against V15 l.20060–20072).
   - The Tao–Ziegler dense-model results (Thm 11, Cor 3, Thm 13, and Thm 15) cannot be applied
     literally, because the W-modulus contains a fixed extra factor. They are now "adaptations
     of their proofs".
2. **GI "Sections 9--11 at every rank step"** (V16 l.26822–26842, l.26908–26915).
   - The horizontal Taylor identities are made exact by lattice corrections γ_{h,i} before the
     coordinates are removed. Fixed lifts are divided by M.
3. **Citation correction** (V16 l.30664, l.30677).
   - In `v15:height`, the uses of §2.3 and Cor. 8.4 now cite \[Gaudron–Rémond, Théorème des
     périodes et degrés minimaux d'isogénies, CMH 89 (2014)\] (`gr-periods2014`, bib
     l.39342–39346).
   - §4's uses of \[gr2014\] = *Polarisations et isogénies* (Duke 2014), Thm 1.4 / §9, are
     unchanged (V16 l.1322, 1599, 1616; N5 l.615, 878, 895). VERIFIED: the locators agree with the
     Duke bib entry, which lists "Theorem 1.4 and Section 9" (V16 l.39347–39350). The V16 README
     says "The Duke paper remains cited for its separate isogeny results".
   - Whether Theorem 1.4 of the Duke paper says what §4 needs was not checked here (UNCHECKED;
     h-v14.md treats this leaf).
- Otherwise V16 changes only the title, the date and the AI statement, which adds Fable 5.2.

## 5. Release notes, findings and edit records (research/versionN/)

All paths are relative to `~/upstream`.
- VERIFIED marks lines read for this note.
- "(survey)" marks a line located by a delegated read-only survey and not re-read here.

### 5.1 Version by version

- **Collaborator notes, 11-06** (`research/2026-11-06-collaborator-notes/`).
  - README l.5 (VERIFIED): the collaborators' von Känel–Kret height estimate "can be replaced by
    the existing five-contact proof in Version 4". This concerns the quartic route, not
    Theorem 4.1.
  - `fable-repository-audit.md` l.13–15 (VERIFIED):
    - completeness is treated as depending on RC;
    - "the prime-pattern theorem in Section 6 was not read in any pass".
- **V6** (`research/version6/README.md` l.9, 13; `analytic-proof/ASSESSMENT.md` l.17, 21;
  survey).
  - V6 proves the Gaussian ray-field estimate in place of the Frei–Tinková theorem.
  - It feeds the simultaneous-primes appendix of the quartics.
  - The original construction "do[es] not use this new input".
- **V7** (`research/version7/README.md` l.3, 7; survey). Four audits of the Gaussian appendix
  and their repairs. They do not re-audit RC or the height theorem.
- **V9** (`research/version9/README.md` l.3, 9; survey). Adds the 523/540 quartics. "No new
  external arithmetic theorem."
- **V10, Issue 2.**
  - Issue 2 is manvirjaswal's "Full check of the 11/5 manuscript"
    (`docs/manuscript-revisions/version10/issue2.json` l.5, VERIFIED). It raised nine points
    (`version10/README.md` l.7–17; dispositions in `responses.json` l.4–96; survey).
  - Points bearing on the inputs (survey):
    - 2: determinant specialization in the RC chain;
    - 4: Kato 1999 Thm 0.8 at the prime 2, in the RC chain;
    - 5–6: conjugated ratios printed, the template dictionary, and the δ/α valuation deduction
      in §6;
    - 7: OpenAI credit at §4, §5, RC and §7;
    - 9: no-seed congruence in §7.
  - `docs/audit-history/issue2/README.md` l.3–17 (survey): most edits "restored or connected
    existing arguments".
- **V11** (`docs/manuscript-revisions/version11/README.md` l.3, VERIFIED). A follow-up on Issue 2
  "found a missing connection in Version 10":
  - K8 had been defined on Kato 2004's restricted index set, but Kato 1999 needs every multiple
    of a fixed integer.
  - The repair is in App "Fixed-form arithmetic and the even coefficient source", in the RC
    chain.
- **V12, V13** (`version12/README.md` l.36; `version13/GUIDE.md` l.35; survey). New quartic
  reductions only. They explicitly do not re-prove RC, the height theorem or the prime pattern.
- **V14.**
  - `research/version14/README.md` (13 lines) and `SUPPORTING-NOTES.md` (63 lines) (VERIFIED).
    - The supporting notes are mostly RC: Heegner descent, CM points, Néron models, Atkin–Lehner,
      Cornut–Jetchev conductor-one.
    - The others are on GI (LP03 selection, Bertrand, the convex boundary) and on the forgetful
      Picard map.
  - `research/version14/proofs/` has 26 supplement directories. Their statuses (VERIFIED, first
    lines):
    - `direct-p5-modularity-v1`: "AUTHORED FOR INDEPENDENT REVIEW … not an acceptance of the full
      modularity ancestry";
    - `b11-integral-model-v1/ASSEMBLY.md`: "Author draft for independent review";
    - `igusa-theta-v1/PROOF.md`: "pending independent review" (replaces the LNY publisher-proof
      citation for two theta identities);
    - `ly-d6-normalization-v1`: "pending review".
  - **`a001-moduli-current-v1/ADVERSE-CASE.md` (14 lines, VERIFIED)** records a defect in the
    proof of Baba–Granath (CJM 2008) Prop. 3.7:
    - the map J(C) → E₁ × E₂ there has degree 4;
    - the printed curve-point separation claim has a direct counterexample, the Weierstrass
      points (±√r, 0).
    - The narrowed A001 argument does not use Prop. 3.7. But Lin–Yang's eq. (2) weighted-Igusa
      formula is attributed to Baba–Granath Prop. 3.9, which uses 3.7. Upstream therefore routes
      the normalization through `ly-d6` and `igusa-theta`.
    - V16 bib l.39270–39276 keeps this: "The adjacent Baba--Granath product-map finding is
      preserved separately."
    - The fork's `h-v14.md` l.203 already records Props 3.7–3.8 as "explicitly not used"
      (V14 L757–759).
    - h-trust.md l.89 uses Baba–Granath 2008 and Lin–Yang 2020 in place of `a001`, `ly-d6` and
      `igusa-theta`. Its leaf F1 (l.688–696, `j` in theta constants) lists "Lin–Yang 2020, eqs.
      (2), (14), (13)" among its suppliers, next to Igusa 1967, Lauter–Naehrig–Yang and
      `igusa_check.py` (VERIFIED).
    - **up-h should decide whether F1 stands without Lin–Yang eq. (2).** (SPECULATIVE as to
      impact.)
  - The V14 GI objections are listed in `version14/final-coverage/ADDITIONAL-FINDINGS-HISTORY.json`
    l.5–22 (survey).
- **V15** (`research/version15/RELEASE-NOTES.md`, 19 lines; `README.md`, 18 lines; VERIFIED).
  - The 222 family: 196 residuals, 2277 monomials, ineffective N₀. Published from merge 2b34f71
    after PR 26.
  - The original construction "remain[s] available".
  - Protocol records `protocol/current222/`: 193 applications, 1187 source uses, 1167
    connections. `FINDINGS.proposed.json` holds 32 formal findings: 30 repaired, 2 out of scope.
    - None concerns the statements of Thm 4.1, PC, RC or 22P.
    - The height-related findings HEIGHT-MODULAR-CLAUSE6 and SF11-SOURCE-ROUTE concern the
      222-family modular height application.
    - `unpublished-foundation-closure-1..5` keep GI and the theta transport internal.
    - `CONNECTIONS.json` still binds the original six-contact theorem's connections. (VERIFIED by
      a JSON read.)
- **V16** (`research/version16/README.md`, VERIFIED).
  - Three corrections from the "fourth Fable 5.2 audit" (`audits/fable-5-2-audit-4.pdf`,
    pp. 84–97). "The abstract, theorem statements and polynomial data are unchanged".
  - The exact edits are in `EDITS.json`. Recheck with `python -B research/version16/check.py`
    (not run here).
  - `FINDINGS.json` l.26–37 (VERIFIED):
    - the Bogolyubov-numbering objection was withdrawn;
    - unclosed audit scope: "Kato1999 pp314–318 and Ribet1990 pp440–443 unread by Fable", and
      the changed-modulus Tao–Ziegler estimates were not re-derived;
    - `"no_new_whole_proof_acceptance": true`.

### 5.2 Upstream's theorem-application audit (`docs/theorem-application-audit/`)

- An inventory of 82 external-theorem application families (A001–A082). It is bound to
  `source/audited-baseline.tex`, whose 11259 lines are N5's line count, so it audits N5 itself.
  Its anchors are N5 line numbers: `thm:height` 404, `hyp:PC` 1001, `hyp:RC` 1005, 22P 1267,
  catalogue 238–241, cutoff 6285. (survey)
- Entries by input (survey):
  - H: A001–A018, A061–A064, A078–A079. `evidence/height-whole.md` l.9–14: "No material
    mathematical defect".
  - PC: A019, A020, A082. `evidence/pole.md` l.5–9: no new gap in RC ⇒ PC.
  - RC: A022–A029, A032, A049–A051, A076.
  - 22P: A021, using GTZ v5 Thm 1.3 "with separate erratum".
  - Dirichlet/catalogue: A057.
  - BMOR cutoff: A046.
- **`SOURCES.md` l.404 (VERIFIED):** the GTZ input is arXiv:1009.3998v5 together with the
  separate author erratum. v5 "retains original Proposition 8.3", so the erratum is required.
  - This is the background to upstream replacing GTZ by its own GI proof.
  - The fork's route AP (nt-22p.md) does not use GTZ.
- Findings F001–F008 (survey):
  - F001: Faltings 1988 was cited for de Rham but gives only Hodge–Tate. It was replaced by
    Scholze plus corrigendum and Brinon–Conrad, in the height proof.
  - F007: the Kolyvagin locator, in the PC chain.
  - The others are locators or misprints.

### 5.3 What the records say about the original construction

- No record withdraws, weakens or makes conditional any statement of the 292890231905-variable
  construction.
  - The V16 README and RELEASE-NOTES say the statements are unchanged.
  - `research/version16/review/coverage/REVIEW.md` l.39 (survey) says the construction "retains
    its six-component arithmetic and compiler composition".
- Every release disclaims a whole-proof acceptance.
- Upstream's Lean formalization has a `sorry` (README l.93; survey).

### 5.4 The 214-variable proposal and the October 11 manuscript

- **p214** (`~/upstream-p214`).
  - A single commit, 110cf72 (Cameron Freer, 11-11). Its parent is upstream main *before* V16
    (`research/quartic214/PROVENANCE.json`), so p214 builds on V15, not V16.
  - Statement (README.md l.5–11, VERIFIED):
    - an ineffective N₀; for N ≥ N₀, x ∈ ℤ ⇔ ∃y ∈ ℚ^213 with P_N(x, y) = 0;
    - P_N is a sum of squares of 188 quadratic rows, degree 4;
    - H(P_N) = 149^(4N+2) + 1 for N ≥ 53.
  - Status: "public author proposal", independent review pending (README l.3).
  - Inputs:
    - `proofs/source-carry.md` l.7 (C02, VERIFIED): "The original huge polynomial's compiler,
      six-contact input and canonical code domain are not themselves needed".
    - RC is kept for E_ℓ: y² = x(x−ℓ)(x+3ℓ) (C04, l.11–15; survey).
    - The eleven-witness PC is not used.
    - A new ten-contact height h(u) < C₂ M_S10(u)^(2103/1024) (`proofs/uniform-existence.md`
      l.40, P10, VERIFIED), with modularity via Calegari ICM.
    - Von Buhren 2017 Thm 1.1 is the source of ineffectivity (P09, l.38–39, VERIFIED).
    - V15's GI Part, and V15's Gaussian simultaneous-prime theorem in place of a prime pattern
      (survey).
- **October 11 manuscript** (`October 11 Manuscript/README.md` l.3; survey of the PDF).
  - "A conditional Diophantine definition of Z in Q from four arithmetic inputs", Sohail Farhangi
    with ChatGPT 6, dated Oct 11.
  - Thm 1.1 (p.1) is conditional on four inputs imported from OpenAI's HTP preprint (Sept 24
    version):
    - pole parity;
    - rank one for y² = x³ − d²x with d = 75 − 53√2 over ℚ(√2);
    - a *five-point* height estimate (p.3, eq. 2.6);
    - compatible prime patterns (pp.3–4).
  - No variable count. Thm 1.2 (p.2): a reduction convertible to degree ≤ 4.
  - It has no RC or PC template analog. Its height input is a five-point analog of H.
  - Page numbers come from a custom PDF text parser (no pdftotext on the host) and were not
    re-checked.

## 6. Status in V16 of the N5 statements the fork formalizes or assumes

| N5 statement (fork use) | V16 | Status |
| --- | --- | --- |
| Thm 1.1 / FrozenTarget (formalized target) | Thm 1.3, l.113–129 | **Unchanged** (byte-identical). Upstream calls it "Original" in README's table |
| Construction behind FrozenTarget: §2 spec, §3 model, §6 templates, §§9–12 compiler/bridge/cutoff, App literal | §§2–3, 6, 9–12 | **Unchanged polynomial.** §§9–12 identical. §2: one wording change (SOURCE_MAP.json → "the same manifest"). §3: Minkowski argument → norm-Euclidean (l.369–371). §6: twelve tests written with explicit σ (V10). App literal: +88-line template table (V10). V16 l.159: "The polynomial specifications and numerical bounds are unchanged" |
| Thm 4.1 = H (assumed, SixContactMin) | Thm 4.2, l.707 | **Statement and constants unchanged. Proof changed in V14** (published modularity via Calegari ICM p.624 / Pan in Lemma 4.1; integral model written out; project supplements). V15 inlines the b11 supplement; V16 leaves §4 unchanged, so `h-v14.md` applies. Baba–Granath Prop. 3.7 concern recorded upstream (§5.1) |
| Thm 5.2 PC + pole template x + 3ℓ (fork replaces by Route K + CR3) | Thm 5.2, l.1736 | **Unchanged** statement, polynomial and template. Proof gained detail; RC attributed to OpenAI 2-converse preprints |
| Thm 5.3 RC (not used by fork) | Thm 5.3, l.1746 | **Unchanged** statement. Proof elaborated (V10, V14) |
| Prop 6.2 = 22P (fork replaces by route AP) | Prop 6.2, l.2076 | **Statement unchanged.** Proof's GTZ inverse theorem replaced by internal GI (V14 supplement, V15 Part) |
| Catalogue definition and bound CAT (fork: CAT8) | l.331–338; §12 l.7255–7425 | **Unchanged** (byte-identical) |
| Prop 6.1 finite box, Prop 12.1 literal cutoff | l.2034, l.7268 | **Unchanged** |
| De Rham descent appendix (N5 l.10936) / "direct modularity argument" | — | **Gone** since V14. Replaced by Lemma 4.1 |
| \[gtz, Thm 1.3\] as an external input of 22P | — | **Gone** since V14. Replaced by local-gi, then by Part v15:gi-full |

No N5 statement that the fork formalizes or assumes was removed or weakened upstream.
