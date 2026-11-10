# Version 14 and our hypotheses: what changed in the arithmetic route

Status: research note. First version 2026-11-09 (task v14-routes), from Version 13 and the isolated
Version 14 section only. Revised 2026-11-10 (task v14-routes2) against the published Version 14
source. Every claim carries a mark:

- VERIFIED: checked against a text. The texts are the 11/5 manuscript `diophantine_zq.tex`, upstream's
  Version 13 and Version 14 sources (read-only copies, not in this repository), the Lean sources, a
  note of this repository, or an exact computation in `scratch/v14-routes/`.
- STANDARD: a published theorem whose exact statement was checked.
- SPECULATIVE: an idea or assessment that is not proved.
- UNCHECKED: a source that could not be read here.

Our hypotheses are those of the narrowest variant of the main theorem: `SixContactMin` (H, the
instance `S = S_mul`, `R = D` of Theorem 4.1), `CertifiedRankSel` (CR₃ in 2-Selmer form) and
`GoodPrimeDensity` (Proposition D). `GreenTaoDense` is now a Lean theorem (branch `wip/gt-dense2`,
commit 0859a41, VERIFIED from the log). `FixedPrimePattern` (22P) is still a hypothesis of the
base theorem `ZInQ.exists_bounded_integer_polynomial_defining_integers_of`, but not of the
narrowest variant. The frozen target is fixed, so only the hypotheses and their justifications
matter.

**Line numbers.**
- "N5 L": a line of `diophantine_zq.tex` (11/5).
- "V13 L", "V14 L": lines of upstream's Version 13 source (November 7, 22,087 lines) and published
  Version 14 source (November 9, 24,347 lines; upstream main 009b47f8, 2026-11-10), after
  removing carriage returns. Both files mix CRLF and LF line ends, and removing the CRs does not
  change the line count.
- The V13 line numbers of the first version of this note are unchanged: the labels it located
  sit at the same lines in the copy used here (VERIFIED).
- The first version's "V14 L x" referred to the separate file `addition.tex`. In the published
  source that line is **V14 L(x + 22783)**. VERIFIED on the section heading, the
  `subsec:v14-H` heading at V14 L22858, the point `U = f(H)²` at L22886 and the root-height
  display at L22844-22846. All V14 line numbers below are published-source lines.

**Tools.** `scratch/v14-routes2/hunks.py` lists the hunks of the diff with their line ranges,
enclosing sections and changed labels. `scratch/v14-routes2/stmts.py` compares labelled statements
and their proofs between two sources. Neither prints manuscript text beyond headings and labels.
The diff itself, and upstream's sources and guide, are kept outside the repository.

## Summary

1. **The published Version 14 has now been read in full (VERIFIED).** Its diff against Version 13
   has 72 hunks (`diff -u`/`git diff --no-index`). Removing carriage returns gives +2,948 −688
   lines; git counts +2,953 −693, because five lines differ only in their line ends. The hunks
   classify as follows (full table in §1):
   - the new section `sec:v14` (1 hunk, 962 lines; it matches the earlier `addition.tex` by line
     offset);
   - quartic constructions (17 hunks);
   - the arithmetic argument of the main construction (34 hunks);
   - exposition, attribution and audit records, including the bibliography (20 hunks).

   **The first version's conclusion does not hold.** It could not see Version 14 outside the new
   section, and concluded that the main construction's arithmetic was untouched. In fact
   Version 14 rewrites large parts of the **proof** of Theorem 4.1. It also tightens the proofs of
   Lemmas 5.4 and 5.5, changes the inverse-theorem source in the proof of Proposition 6.2, and
   repairs several steps inside the proof of RC.
2. **No hypothesis is weakened, removed or replaced (VERIFIED).** The statements of Theorem 4.1
   (with every constant of `H₆(S;R)`), Lemma 5.1, Theorems 5.2 and 5.3, Lemmas 5.4 and 5.5,
   Proposition 6.2, `prop:generator` and `lem:assembly` are byte-identical in 11/5, Version 13
   and Version 14. The polynomial is unchanged: "The polynomial of the main construction is
   unchanged" (V14 L22789-22790).
3. **What changes is the justification of two of our hypotheses (VERIFIED, §2).**
   - **SixContactMin.** The proof of Theorem 4.1 grows from 557 to 987 lines (V13 L486-1042,
     V14 L688-1674), and Appendix H (`lem:de-rham-descent`) is deleted. The changes:
     - The modularity step becomes the new Lemma `lem:qm-modularity-descent` (V14 L480-667;
       scope paragraph L669-680). Its immediate supplier is "the published statement in [Calegari, ICM 2022, p. 624]; Pan's work
       is its proof source". Berger's monodromy theorem and Conrad's local-algebraicity preprint
       drop out. The twist and the weight are pinned down by a new argument (Deligne–Serre,
       Kato 2004 §§9.4 and 14.10, Shimura, Li).
     - Lemma 3.1 of Baba–Granath has a "local index slip" (V14 L23870-23871, the bibliography's
       note on `babagranath`). Their printed principal form is six times the determinant-one
       form (V14 L699-704).
     - The integral model and its identification with the adelic level-3 curve are proved in full
       (Deligne 1971 PEL theory).
     - The conductor is compared at every prime through Carayol 1987.
     - Published editions are now cited in place of preprints: Baba–Granath 2008, Buzzard 1997,
       Lin–Yang 2020, Igusa 1967, Milne 1986, Fontaine 1994, Serre–Tate 1968.

     Several of these are exactly the repairs that `h-leaves.md` §§4.4 and 6 recommended. The
     result is a sharper paper proof of the same statement.
   - **CertifiedRankSel.** Lemma 5.5 (GZK) now cites Kolyvagin's address in *Proc. ICM Kyoto
     1990*, pp. 429-436, instead of the MPIM preprint MPI/90-69 that nt-tyz §5.2 flagged. Its
     proof now gets BCDT through Silverman, Theorem C.13.6. Lemma 5.4's proof now argues the
     maximal divisible subgroup explicitly and pins Poonen–Stoll's Corollaries 4 and 7 and
     Theorem 8. The ICM text could not be read here (UNCHECKED).
   - **GoodPrimeDensity**: unaffected. Proposition 6.2's proof now takes the inverse theorem
     GI(20) from an unpublished project supplement (`local-gi`, 8 November 2026) instead of
     Green–Tao–Ziegler arXiv v5 with the erratum. This affects only the justification of 22P,
     which the narrowest variant no longer uses. Proposition D does not use the GTZ machinery
     (nt-22p L539).
   - **The repairs inside the proof of RC** (§5 non-CM remark, §7, Appendices E and F) do not
     touch Route K, which never uses RC (VERIFIED, as before).
4. **The quartic route (VERIFIED, §5).** Version 14 also changes the quartic route outside
   `sec:v14`:
   - its five-contact height proof is now built on the same Calegari/Pan lemma;
   - its 41-form prime pattern and its Gaussian prime appendix now take their inverse theorem from
     `local-gi` (Dodos–Kanellopoulos is dropped);
   - the degree-four section cites Colliot-Thélène–Salberger instead of Kollár.

   The earlier assessment stands: adopting the quartic route would cost months and remove no
   hypothesis (SPECULATIVE).
5. **Recommendation (§8).** The order is unchanged:
   1. finish GoodPrimeDensity;
   2. then move the elementary half of CertifiedRankSel into Lean (tyz-5b §4);
   3. for SixContactMin, a new and cheap first step: re-base the h-leaves inventory on Version 14
      §4 before doing more paper-side work (nt-h §5). The proof that h-leaves audited has been
      partly rewritten upstream, and five upstream proof supplements now carry parts of it.

## 1. Classification of the 72 hunks (VERIFIED)

Classes:
- **N**: the new Version 14 section.
- **Q**: the quartic constructions, meaning Version 13 sections 14-17, the simultaneous-prime
  appendix, the Version 9-13 quartic sections, and the abstract's sentence about them.
- **A**: the arithmetic argument of the main construction (Theorem 4.1, Lemma 5.1, Theorems 5.2
  and 5.3, Lemmas 5.4 and 5.5, Proposition 6.2, §§7-9, Appendices E-H, and their inputs).
  Each A hunk carries a tag for what it feeds:
  - **A/H**: the proof of Theorem 4.1, which justifies SixContactMin;
  - **A/CR**: Lemmas 5.4 and 5.5, used in CertifiedRankSel's justification;
  - **A/22P**: the proof of Proposition 6.2;
  - **A/RC**: the proof of RC;
  - **A/G**: the generator certificate.
- **E**: exposition, attribution and audit records, including the bibliography.

Ranges are those of `diff -u` (three lines of context).

| # | V13 lines | V14 lines | Where | Class | Change |
| --- | --- | --- | --- | --- | --- |
| 1 | 36-44 | 36-44 | title | E | Version 14, November 9 |
| 2 | 49-59 | 49-59 | abstract | Q | quartic sizes 314/299 replace 411/394 |
| 3 | 119-130 | 119-130 | §1 | E | version paragraph |
| 4 | 203-209 | 203-209 | proof of Thm 1.1 | E | pointer to upstream's `research/version14/SUPPORTING-NOTES.md` |
| 5 | 341-349 | 341-349 | proof of `prop:generator` | A/G | class number one by norm-Euclidean `ℤ[√2]` instead of the Minkowski bound; same conclusion |
| 6 | 473-481 | 473-683 | §4 preamble | A/H | "direct modularity argument" becomes "published prime-five modularity theorem"; new `lem:qm-modularity-descent` (L480-667) and "Scope of the modularity input" (L669-680) |
| 7 | 492-557 | 694-1120 | proof of `thm:height`, polarization and moduli | A/H | Baba–Granath 6× form; branch indices; `eq:qm-normalized-igusa` (L750); local normalizer index; integral model in six phases; generic adelic curve and rational model (L932-1118) |
| 8 | 606-643 | 1169-1250 | proof of `thm:height`, Hom field | A/H | rank bound via Milne 2005; inertia via Serre–Tate; descent of morphisms to `L` |
| 9 | 727-734 | 1334-1356 | proof of `thm:height`, scalar descent | A/H | degree of rational quasi-isogenies; `ε = c/|c|` |
| 10 | 761-771 | 1383-1395 | proof of `thm:height`, Brauer step | A/H | local Brauer classes; citation pinned |
| 11 | 808-847 | 1432-1446 | proof of `thm:height`, modularity | A/H | de Rham/Berger/oddness/Pan/Conrad paragraph replaced by the new lemma |
| 12 | 849-873 | 1448-1484 | proof of `thm:height`, compatible system | A/H | every `ℓ`; conductor via Carayol 1987 |
| 13 | 933-946 | 1544-1567 | proof of `thm:height`, transfer from `J₁(N)` | A/H | complement via Milne 1986 Prop. 12.1 |
| 14 | 981-999 | 1602-1631 | proof of `thm:height`, theta formula | A/H | Igusa 1967 replaces Lauter–Naehrig–Yang; weighted rescaling |
| 15 | 1095-1102 | 1727-1736 | after `hyp:RC` | A/RC | non-CM of `E_ℓ` via eq. `rc-noncm-invariants` |
| 16 | 1161-1169 | 1795-1808 | proof of `lem:corank` | A/CR | maximal divisible subgroup; Poonen–Stoll Cor. 4, 7, Thm 8 |
| 17 | 1174-1181 | 1813-1822 | proof of `lem:forward-rank` | A/CR | BCDT via Silverman C.13.6; Kolyvagin ICM 1990, Thm 1, pp. 430-431 |
| 18 | 1186-1192 | 1827-1859 | proof of `lem:forward-rank` | A/CR | explicit `J₁(N) → A` over `ℚ` for Kato's finiteness |
| 19 | 1380-1386 | 2047-2053 | comment before `prop:fixed-prime-pattern` | E | bibliography key `gtz` → `local-gi` |
| 20 | 1523-1529 | 2190-2196 | proof of Prop. 6.2 | A/22P | GI source: GTZ Thm 1.3 → `local-gi` |
| 21 | 1531-1539 | 2198-2207 | proof of Prop. 6.2 | A/22P | "arXiv version 5 with the erratum" → "the local inverse-theorem proof" |
| 22 | 1887-1895 | 2555-2579 | §7 | A/RC | invariants and non-CM of `E_ℓ` written out |
| 23 | 1901-1912 | 2585-2656 | §7 | A/RC | modular parametrization: Silverman C.13.6/C.16.4, Amir–Hong, Shimura, Faltings; Hecke normalization; `2 ∣ N` |
| 24 | 1915-1922 | 2659-2668 | §7 | A/RC | parity: Dokchitser–Dokchitser Annals 2010 Thm 1.4 replaces Crelle 2011 Thm 1.8 |
| 25 | 2544-2549 | 3290-3321 | §7, before `ex:sec7-genus-lower` | A/RC | native genus lattice; index at most two |
| 26 | 2649-2655 | 3421-3428 | §7 | A/RC | Cornut–Jetchev Thm 3.1 → project supplement `cj-conductor-one` |
| 27 | 6938-6951 | 7711-7943 | §14, proof of `hyp:o8-height` | Q | full level-3 marking at a ramified prime, rigidity, projectivity, generic moduli problem (`sec:h5-full-three-construction`) |
| 28 | 6965-6971 | 7957-7963 | §14 | Q | page locator |
| 29 | 7011-7023 | 8003-8056 | §14 | Q | conjugate isogenies, GL₂-type over `L` |
| 30 | 7041-7046 | 8074-8082 | §14 | Q | no use of Yuan's coarse Lemma 2.1 |
| 31 | 7065-7071 | 8101-8107 | §14 | Q | page locator |
| 32 | 7090-7096 | 8126-8132 | §14 | Q | comment: "Proposed repair … Independent review pending" removed |
| 33 | 7164-7176 | 8200-8238 | §14 | Q | `B`-linear normalizer isogenies |
| 34 | 7222-7365 | 8284-8424 | §14 | Q | modularity now via `lem:qm-modularity-descent`; compatible system and conductor at every `ℓ` |
| 35 | 7424-7430 | 8483-8489 | §14 | Q | comment: "UNAPPLIED CANDIDATE: global review and published Pan match are pending" removed |
| 36 | 8479-8485 | 9538-9544 | §14, 41 contacts | Q | GI source → `local-gi` |
| 37 | 9317-9328 | 10376-10398 | §15 conventions | Q | source statuses: `local-gi`, Calegari, Yuan's Chinese article |
| 38 | 11755-11768 | 12825-12842 | §18, degree ≥ 4 | E | Kollár → Colliot-Thélène–Salberger for unirationality of cubics |
| 39 | 11873-11881 | 12947-12955 | §18 | E | same |
| 40 | 11920-11931 | 12994-13005 | App. B | E | source catalogue pointers |
| 41 | 12194-12201 | 13268-13275 | App. D | E | parity record |
| 42 | 12205-12213 | 13279-13290 | App. D | E | CM record; conductor-one supplement |
| 43 | 12216-12233 | 13293-13311 | App. D | E | height and prime records: Calegari for Pan, `local-gi` for GTZ |
| 44 | 12613-12620 | 13691-13698 | App. E | A/RC | generator at two: minimal invariant differential |
| 45 | 12758-12765 | 13836-13847 | App. E | A/RC | Kato's cochain conventions and support modulus |
| 46 | 13777-13784 | 14859-14867 | App. F | A/RC | parity via DD 2010 |
| 47 | 13992-14008 | 15075-15101 | App. F | A/RC | supersingular class set via Ribet 1990 |
| 48 | 14630-14635 | 15723-15737 | App. F | A/RC | CM inputs pointer (project supplements) |
| 49 | 14723-14808 | 15825-15852 | App. F | A/RC | Cornut–Jetchev specialization (80 lines) → conductor-one supplement |
| 50 | 14816-14822 | 15860-15866 | App. F | A/RC | "pairs" → "coarse points" |
| 51 | 14881-14887 | 15925-15931 | App. F | A/RC | same |
| 52 | 14954-14961 | 15998-16006 | App. F | A/RC | index two by hunk 25 |
| 53 | 16466-16542 | (17511-17516) | App. H | A/H | `app:de-rham-descent`, `lem:de-rham-descent` deleted; content now in `lem:qm-modularity-descent` |
| 54 | 18472-18491 | 19446-19620 | simultaneous-prime appendix | Q | Dodos–Kanellopoulos → Green–Tao Prop. 10.1 + `local-gi`; new `lem:ga-full-prime-majorant` |
| 55 | 18503-18568 | 19632-19719 | same | Q | majorant normalization |
| 56 | 19823-19830 | 20974-20981 | `sec:v12` | Q | layout |
| 57 | 19885-19891 | 21036-21042 | `sec:v12` | Q | layout |
| 58 | 20184-20190 | 21335-21341 | `sec:v12` | Q | Voight page locator |
| 59 | 21630-21636 | 22781-23749 | new `sec:v14` (L22784-23739) | N | §3 |
| 60-72 | 21646-22073 | 23759-24333 | bibliography | E | §2.5 |

Count: N 1; Q 17 (hunks 2, 27-37, 54-58); A 34 (5-18, 20-26, 44-53); E 20 (1, 3, 4, 19, 38-43,
60-72). In the hunk list, hunks 60-72 appear "inside" `sec:v14` because the bibliography follows
it without a new heading (V14 L23740-24331).

## 2. Changes to the main construction's arithmetic, and their effect on our hypotheses

### 2.1 The statements did not change (VERIFIED)

`stmts.py` gives the following.

| Label | N5 | V13 | V14 | Statement | Proof (V13 → V14) |
| --- | --- | --- | --- | --- | --- |
| `prop:generator` | 268 | 339 | 339 | identical | changed (hunk 5) |
| `thm:height` (Thm 4.1) | 404 | 480 | 682 | identical | changed, 557 → 987 lines |
| `lem:pole` (Lemma 5.1) | 988 | 1067 | 1699 | identical | identical |
| `hyp:PC` (Thm 5.2) | 1001 | 1080 | 1712 | identical | (proved in §5 text) |
| `hyp:RC` (Thm 5.3) | 1005 | 1090 | 1722 | identical | (§§7-9) |
| `lem:corank` (Lemma 5.4) | 1072 | 1157 | 1791 | identical | changed, 9 → 14 lines |
| `lem:forward-rank` (Lemma 5.5) | 1086 | 1171 | 1810 | identical | changed, 19 → 47 lines |
| `prop:fixed-prime-pattern` (Prop. 6.2) | 1267 | 1385 | 2052 | identical | changed, 406 → 407 lines |
| `lem:assembly` | 110 | 178 | 178 | identical | identical |

The definitions in front of Theorem 4.1 are identical between N5 and V14: `𝒞`, `F`, `G`, `M_S`,
`F₀`, `D`, `G₀`, `E₀`, `Q_R`, `B_cm`, `C_cm` and `H₆(S;R)`. Only the sentence after them differs
(N5 L391 ± 12 against V14 L467 ± 12). So `SixContactEstimate` and `SixContactMin`
(`ZInQKernel/Hypotheses/Height.lean`, `HeightMin.lean`) still state Theorem 4.1 and its instance
with the same numerals.

### 2.2 Theorem 4.1: the justification of SixContactMin (VERIFIED)

**Statement and constants: unchanged.** The §4 preamble now reads "The geometric construction is
followed by the published prime-five modularity theorem and a separate effective CM argument. The
constants in the displayed definition of `H₆(S;R)` are unchanged" (V14 L476-478). Version 13
said "a direct modularity argument at coefficient prime five" (V13 L476).

**The modularity step: new lemma.**
- `lem:qm-modularity-descent` (V14 L480-503, proof L504-667). Hypotheses: `A` is an abelian
  surface over a finite Galois extension of `ℚ` whose geometric endomorphism algebra is a quaternion division algebra
  `B`; there are `B`-compatible quasi-isogenies `μ_σ` with rational cocycle `c(σ,τ)`; and there is
  a cochain `t` with `t_σ t_τ c(σ,τ) = t_{στ}`. Conclusion: "If `ρ₅(σ) = t_σ μ_σ ∘ σ` is written
  as `r₅ ⊕ r₅` …, then `r₅` is the Tate realization of a primitive weight-two cuspidal newform,
  after a finite coefficient extension" (V14 L499-501).
- The proof checks the hypotheses of the cited modularity statement for `r₅`:
  - continuity;
  - absolute irreducibility (Faltings 1986);
  - finite ramification;
  - de Rham with weights `0, −1` (Scholze 2013 with the erratum, Milne 1986 Thm 15.1, Fontaine
    1994 Thm 3.8, and descent to `ℚ₅`);
  - oddness ("`t_c μ_c c` has trace zero", via Milne 2005 Thm 6.8).
- It then removes the twist and fixes the weight without a local-algebraicity theorem:
  - Deligne–Serre §1 picks a primitive constituent;
  - weight `1` is excluded by Deligne–Serre Thm 4.1 and equal Hodge–Tate weights;
  - for `k ≥ 2`, Kato 2004 §§6.3, 9.4 and (14.10.2)-(14.10.3) give `HT(U_f) = {0, 1−k}`, so
    `k = 2` and the twist has weight `0`;
  - the twist is finite because `δ² = α/ε_f` with `α² = 1`;
  - Washington Thm 14.1, Shimura's translate formula and Li's newform theory then absorb the twist
    into a weight-two newform.
- "Scope of the modularity input. The immediate supplier is the published statement in
  [Calegari, p. 624]; Pan's work is its proof source. This use imposes no residual restriction
  at five. It does not assert that every input to Pan's proof has been reproved here" (V14
  L669-674).
- In the proof of Theorem 4.1 the old paragraph (V13 L808-847) is replaced by "Apply Lemma
  `lem:qm-modularity-descent` with `t_σ = a_σ/β(σ)`. It identifies this same `r₅` with the Tate
  realization of a primitive weight-two newform `f`" (V14 L1438-1440).
- Version 13 had instead:
  - "Berger's p-adic monodromy theorem makes this de Rham representation potentially semistable,
    as required by Pan's theorem" (V13 L815-817);
  - "Apply [Pan, Theorem 1.0.4] at ℓ = 5" (V13 L832);
  - local algebraicity from Conrad's 2011 preprint (V13 L837).
- Berger, Conrad and Appendix H are no longer cited (citation counts V14: 0, 0, 0). Pan is
  cited once, in the scope paragraph.

**What the cited source says (VERIFIED in arXiv:2109.14145v1, source file `Survey.tex`;
the ICM proceedings pagination was not compared).**
- Calegari's survey says that Pan found a way "to completely prove the modularity (up to twist) of
  any geometric representation `ρ: G_ℚ → GL₂(Q̄_p)` for `p ≥ 5` only assuming the hypotheses that
  `ρ` has distinct Hodge–Tate weights and that `ρ` is odd". This is the paragraph on Pan in its
  section on p-adic local Langlands, `Survey.tex` L630-633.
- "Geometric" there means a continuous irreducible representation, unramified outside finitely
  many primes and potentially semistable (equivalently de Rham) at `p` (`Survey.tex` L124-128).
- The supplier is therefore a sentence in a survey, not a numbered theorem. Its content is Pan,
  Theorem 1.0.4 for `p = 5`, with Berger's equivalence (pst ⟺ de Rham) folded into the definition
  (SPECULATIVE reading). It is no weaker as an input. It is a different citation form, which our
  trust statements would need to name.

**The geometric part.**
- Polarization: "The form printed in [Baba–Granath §2.1], `Trd(x̄μy)`, is six times this form,
  since `μ² = −6`. It has determinant `6⁴` on this lattice. We use the determinant-one form
  above" (V14 L699-702). Version 13 used the determinant-one form too, but cited Baba–Granath's
  datum without the correction (V13 L494-499).
- The bibliography adds: "The printed principal-form normalization and the local index slip in
  Lemma 3.1 are treated in [a001-moduli-project]" (V14 L23870-23872).
- Branch indices `4, 6, 2` now come from cyclic stabilizers (V14 L715-718).
- The Igusa point is derived from Lin–Yang Examples 29-30 as `eq:qm-normalized-igusa`: `[J₂, J₄,
  J₆, J₁₀] = [12(j+1), 6(j²+j+1), 4(j³−2j²+1), j³]` (V14 L750-753). Version 13 stated the same
  vector without derivation (V13 L611-616).
- Normalizer index `|N/(𝔸_f^* K₀)| = 4` is proved locally. "This uses the kernel definition of
  `K₃`, so no surjectivity of reduction is needed" (V14 L802-803). The bound `324` is unchanged.
- Integral model: six phases over `ℤ[1/30]` (V14 L805-931): the initial `V₁(5)` model, full
  five-marking, full three-marking, freeness and rigidity, quotient and descended object, and the
  whole full-three functor.
- Then a new identification of the constructed scheme with the generic adelic curve and its
  `ℚ`-model through Deligne's *Travaux de Shimura* (V14 L932-1118): "This is the actual map to a
  fine moduli scheme, not descent of an arbitrary complex isomorphism" (V14 L1081-1082).

**The arithmetic part.**
- Hom field `L`: unramified outside `T` via Serre–Tate (V14 L1209-1235); bound `[L:ℚ] ≤ D`
  unchanged.
- Scalar descent: degree of rational quasi-isogenies `D(cu) = c⁴D(u)` (V14 L1337-1353).
- Compatible system:
  - Version 13 used "`r₃` to compute the conductor at five and `r₅` at all other primes"
    (V13 L869-870).
  - Version 14 identifies `r_ℓ` with `U_{f,ℓ}` for every `ℓ` and compares conductors through
    Carayol 1987, §§2.1, 2.4, 4.1 (V14 L1451-1481).
  - h-leaves listed this input (I1) as used without citation. It is now cited.
  - I2, the reduction of `μ_σ`, is still uncited: "The actual isogeny `μ_σ` extends over the local
    abelian schemes" (V14 L1459-1460).
- Transfer: the complement `Z` comes from Milne 1986 Prop. 12.1 instead of "Poincaré
  reducibility" (V14 L1553-1564).
- Theta formula: Igusa 1967 replaces Lauter–Naehrig–Yang (V14 L1605-1628).

**Published editions now cited in §4 and its bibliography (VERIFIED from V14 L23741-24329):**
- Baba–Granath, Canad. J. Math. 60 (2008);
- Buzzard, Duke 87 (1997);
- Lin–Yang, Math. Z. 295 (2020), 775-819 (h-leaves: "publication not determined");
- Yuan, the published Chinese article, in place of the English translation;
- Voight, GTM 288 (2021);
- Milne 1986 (Cornell–Silverman) and Milne, *Introduction to Shimura varieties* (2005), replacing
  Milne's *Abelian varieties* course notes;
- Fontaine, Astérisque 223 (1994), replacing Brinon–Conrad.

Upstream also adds five project proof supplements. They are cited, but their text is not in the
manuscript: `direct-p5-modularity`, `a001-moduli`, `ly-d6-normalization`, `b11-integral-model`
and `igusa-theta`. Four "Pan" supplements are listed in the bibliography but not cited in the
text, among them "A published replacement for the surjectivity step in Pan's Lemma 3.5.9" (V14
L23919-23923; the other three at L24274-24292). None of these could be read here (UNCHECKED).

**Effect on SixContactMin.**
- Not weakened, removed or replaced: the statement and the constant are those of 11/5.
- The argument that justifies it is repaired and made more explicit.
- h-leaves' inventory and line numbers (N5 L404-966 and the appendix lemma) describe the older
  proof. Its open checks change status as follows (SPECULATIVE where it says "would"):
  - §4.4: upstream has done most of the published-edition replacements. Brinon–Conrad, Conrad's
    preprint, Milne's notes, and the preprints of Baba–Granath, Buzzard and Lin–Yang are no longer
    cited in §4.
  - §6 item 3 (I1, Carayol) is addressed upstream.
  - §6 item 2 (crystalline comparison, option (b)): Version 14 no longer cites Berger, because
    the survey's definition of "geometric" already takes pst ⟺ de Rham as given. Berger's theorem
    therefore enters only through that definition (SPECULATIVE reading, §7). Scholze is still
    used for the de Rham property, so option (b) would still remove both.
  - §6 item 1 (non-circularity of GR14 Theorem 1.4) is unaffected: the `J₁(N)` transfer with GR14
    is unchanged apart from the complement.
  - ser-ell's Serre-conjecture route still replaces exactly the modularity input, now
    `lem:qm-modularity-descent`. Upstream mentions "separate GL2-type and Serre weight-transfer
    reconstructions" that "are not inputs to the present lemma" (V14 L676-677), so it has its
    own version of that route (UNCHECKED).

### 2.3 Lemmas 5.4 and 5.5: the justification of CertifiedRankSel (VERIFIED)

Lemma 5.5 (`ord_{s=1} ≤ 1` ⟹ rank equal and `Ш` finite) is the GZK input of CR₃'s main route
(Proposition N, tyz-5b step 5; nt-tyz §5.2 item 1). Lemma 5.4 (`dim Sel₂ = 3` ⟹ corank one, via
Cassels–Tate) enters only the alternative route through Kriz's 2-converse (KERNEL_PLAN.md). The
main route uses no Cassels–Tate pairing (nt-tyz §5.1).

- **Lemma 5.4** (statement V14 L1791-1794, identical). The proof now states: "The displayed
  divisible summand is the maximal divisible subgroup: any divisible subgroup maps trivially to
  the finite quotient `F`. The Cassels–Tate pairing on that quotient is nondegenerate and
  alternating for an elliptic curve [Poonen–Stoll, Corollaries 4, 7 and Theorem 8]" (V14
  L1798-1802). It is the same argument with the citation pinned. The conclusion is unchanged.
- **Lemma 5.5** (statement V14 L1810-1814, identical).
  - "Use the modularity theorem of Breuil, Conrad, Diamond and Taylor in the published formulation
    [Silverman, Theorem C.13.6, p. 442]. Apply [Kolyvagin, Theorem 1, pp. 430–431]" (V14
    L1816-1819). Version 13 had "[Theorem 1, pp. 4–5]" (V13 L1178).
  - The bibliography entry changes from "MPIM preprint MPI/90-69 (1990), Theorems 1–5, pp. 4–5" to
    "Proceedings of the International Congress of Mathematicians, Kyoto 1990, Vol. I, Mathematical
    Society of Japan, 1991, pp. 429–436, Theorems 1–5, pp. 430–431" (V13 L21875-21879, V14
    L24054-24059).
  - The proof also adds an explicit construction of `q = f_*: J₁(N) → A` over `ℚ` for Kato's
    Corollary 14.3 (V14 L1831-1855).
- **Effect.**
  - CertifiedRankSel is not weakened. The repair narrows the unrefereed-citation issue of nt-tyz
    §5.2 item 1: upstream now cites the published ICM address, which is the candidate nt-tyz named
    (whose contents were not compared there).
  - An ICM address is published but not refereed in the journal sense, and its Theorems 1-5 are
    announcements whose proofs are in Kolyvagin's other papers (SPECULATIVE characterization; the
    ICM text could not be fetched here, UNCHECKED).
  - nt-tyz §6 route 2, refereed Gross–Zagier plus Kolyvagin (Izvestiya 1989) with a nonvanishing
    theorem, remains the way to a fully refereed citation. For the CM curves `C_d` only "analytic
    rank one ⟹ rank ≥ 1" is needed (pc-audit RK7).
  - The new BCDT citation does not matter for `C_d`, which has CM.

### 2.4 Proposition 6.2: the justification of 22P, not of GoodPrimeDensity (VERIFIED)

- The statement is identical (V14 L2052-2082).
- In the proof, the inverse theorem GI(20) came from "[Theorem 1.1]{moebius} and [Theorem
  1.3]{gtz} … The inverse theorem is read in arXiv version 5 together with the separate erratum,
  in particular its Proposition 3.1 and modified deduction of Proposition 7.3" (V13 L1525-1536).
- It now comes from "[Assembly, Sections 1 and 6]{local-gi} … The local inverse-theorem proof
  supplies the normalized finite-family statement with linear nilsequences of step at most 20; its
  constructions and published inputs are given in the accompanying supplement" (V14 L2192-2204).
- `local-gi` is "Project proof supplement, *A local proof supplement for the required Gowers
  inverse theorem*, version 1, 8 November 2026, accompanying this manuscript as
  `quartic-local-gi-supplement.pdf`" (V14 L23990-23995). The `gtz` entry is gone from the
  bibliography.
- The same replacement is made for the quartic route (hunks 36, 37, 54).

**Effect.**
- **GoodPrimeDensity: none.** Proposition D (nt-22p §2, pd-paper) is a density statement whose
  justification does not use the GTZ machinery: "The GTZ machinery of record A021 leaves the
  trust base of this hypothesis" (nt-22p L539).
- The good-prime conditions it is about are defined by §6's multiplication tests, which Version
  14 does not change (hunks 19-21 touch only a comment and Proposition 6.2's proof).
- **22P (FixedPrimePattern)** keeps its statement, but upstream now justifies GI(20) by an
  unpublished, unrefereed supplement instead of the published GTZ theorem with its erratum.
  rs-pattern still records the GTZ source. For the base theorem's trust statement the published
  GTZ citation is still the better one, unless the erratum turns out to be insufficient. Upstream
  does not say why it switched (SPECULATIVE).
- The narrowest variant does not use 22P.

### 2.5 The proof of RC, and the remaining A hunks (VERIFIED)

The changes to RC's proof:
- the non-CM argument for `E_ℓ : y² = x(x − ℓ)(x + 3ℓ)` is written out through Fowler's class
  polynomial (hunks 15, 22);
- the modular parametrization and Hecke normalization use Silverman C.13.6/C.16.4, Amir–Hong
  Thm 3.1, Shimura and Faltings (hunk 23);
- the parity input becomes Dokchitser–Dokchitser, Annals 172 (2010), Theorem 1.4 (hunks 24, 41,
  46);
- a native genus lattice paragraph is added (hunks 25, 52);
- Cornut–Jetchev's Theorem 3.1 is replaced by the project supplement `cj-conductor-one` (hunks
  26, 42, 48, 49, the last removing an 80-line verification of CJ's hypotheses);
- Kato's cochain conventions are fixed (hunk 45);
- the supersingular class set comes from Ribet 1990 (hunk 47).

Route K proves PC from CR₃ for the curves `x + ℓ`. CR₃ rests on Tian–Yuan–Zhang and GZK, not on
RC (KERNEL_PLAN.md, `ZInQ.poleCompleteness_of_certifiedRank`). So none of these hunks enters our
development or the justification of CertifiedRankSel. Dokchitser–Dokchitser appears in our notes
only inside Kriz's proof (pc-audit L204), and Cornut–Jetchev not at all in the Route K notes
(VERIFIED by search).

Lemma 5.1 (`lem:pole`, soundness, used by Route K for the `x + ℓ` curves as well) is identical
with its proof.

Hunk 5 (A/G) re-proves class number one of `ℤ[√2]` by the norm-Euclidean property. MW and the
generator certificate are Lean theorems here (`ZInQ.mordellWeilE`), so this does not matter to us.

**Bibliography (hunks 60-72).**
- Removed: `conrad-local-characters`, `dd`, `gtz`, `Kollar2002Cubic`, `lny`, `v5dk`.
- Added: 32 keys, among them `calegari-icm2022`, `carayol1987`, `deligne-serre1974`,
  `Deligne1971`, `ddselmer`, `local-gi`, `ribet-geometry-1990`, `amirhong`, `igusa1967`,
  `milne1986-abelian`, `milne-shimura2005`, `fontaine1994-representations`,
  `serre-tate-good-reduction`, `washington1997`, fourteen project supplements (including
  `local-gi`), and `stacks-h5-fine`.
- Changed in place, among others: `kolyvagin` (§2.3), `babagranath`, `buzzard`, `linyang`,
  `Yuan2024`, `voight-quaternion`, `poonenstoll`, `fowler`, `pan2022`.

## 3. The new section `sec:v14` (VERIFIED in the published source)

`sec:v14` is V14 L22784-23739, inserted by hunk 59. Its first lines are the comments "Isolated
Version 14 author draft; assembled independent review is required" and "This file does not
modify the original polynomial or Version 13" (L22784-22785). These comments survive into the
published source, although upstream's commit calls the version "reviewed". The line structure
matches the first version's reading of `addition.tex` at offset 22783, and its only `\ref`s are
to `sec:v13`, `subsec:v12-inputs` and its own labels (VERIFIED). The first version's findings
therefore stand. They are restated here with published line numbers:

- **Theorem `thm:v14-quartic`** (L22792-22812): a quartic `P_299` in 299 variables (6,630
  monomials, content one, largest coefficient `186624·3^(2^26)`) and `P_314` (6,672 monomials,
  coefficients `< 2^6496`), each with rational zero projection exactly ℤ.
- **Retained inputs** (L22834-22855): "the squareclass calculation, formal expansions and
  logarithm estimates, simultaneous contact-prime construction with its real-density condition,
  preparation-zero pole criterion, root-height implication, Lucas argument and
  scalar-depth-24 argument".
  - The root-height conclusion `B² − 6 < 7𝓗|N|^{19/k}` with `1 ≤ 𝓗 < 2^2093966`
    (L22844-22846) is the exponent-19 estimate `thm:quartic-height19`.
  - The pole interface is the preparation-zero lemma (L22852-22855).
- **The auxiliary point `H`.** "The fixed-difference chart for H" (`subsec:v14-H`, L22858), "the
  H-depth bootstrap" (L23309) and "choose H in the original progression" (L23463) refer to the
  auxiliary point `H` with `U = f(H)²` (L22886), not to the height hypothesis.
- **The changes** are of three kinds:
  - private witness changes with inverses: L22858-22914, L23179-23308, L23575-23682 (the private
    changes, shorter power chains and Lucas recentering), and L23683-23738 (the ordinary
    presentation);
  - changed certificates with separate soundness and completeness proofs: the parity anchor
    (L22916-23031), contact poles and common-scale groups (L23032-23178), auxiliary point domains
    (L23309-23399), simultaneous completeness (L23400-23468), and the coupling to the quaternion
    anchor with a weak-approximation argument (L23469-23574);
  - retained arithmetic inputs, quoted, not reproved.
- "The independently restored scalar anchor gives `B > (40𝓗)^10`, excluding all three radicals
  equal to one without using H or auxiliary logarithms" (L22848-22850). That is a special case.
  The root-height implication is still needed in general.

## 4. 11/5 against Version 13 (VERIFIED; first version, still valid)

Version 14 left these Version 13 changes in place, except where noted.
- **Attributions to OpenAI's preprints**, unchanged in Version 14: `openaipointwise`,
  `openaigoldfeld` and `openaihtp` have the same citation counts and the same bibliography entry.
  Before RC: "The following statement is the `E = E_ℓ`, `s₂(E) = 1` case of [openaipointwise,
  Theorem 1.1] … these preprints are cited for attribution, not assumed as additional converse
  inputs" (V13 L1084-1088, V14 L1716-1720).
- **The multiplication test list** states the conjugation `A_i − σ(A'_i)` (V13 L1260-1267),
  which our Lean template already applies (`ZInQKernel/Syntax/Templates/Certificate.lean` lines
  63-64).
- **The valuation deduction at a contact prime** is written out (V13 L1287-1316), with the same
  conclusion that our Lean multiplication soundness proves.
- **Three repairs inside RC's proof**:
  - Kato 1999, Theorem 0.8, at the prime 2 (§7; Appendix E, V13 L12677-12787);
  - the off-filter scope of `a_p(E^{(k)}) ≡ p + 1 (mod 8)` in §8;
  - `lem:v10-determinant-specialization` in §9 (V13 L4124, V14 L4897; statement and proof
    identical in V14).
- **Appendices.** Appendix F was unchanged from 11/5 to V13 but changes in V14 (§2.5). Appendix H
  was unchanged to V13 and is deleted in V14 (§2.2).
- **Lemma 5.5.** The first version said it "still cites Kolyvagin's MPIM preprint". That holds for
  Version 13 only; Version 14 cites the ICM address (§2.3).

The 11/5 against Version 13 comparison of this section was made by the first version (`scratch/v14-routes/`).

## 5. The quartic route (VERIFIED)

### 5.1 Its curve is our curve

- The quartic route uses `K = ℚ(√2)`, `d = 3 − √2`, `D = d²`, `E : y² = x³ − Dx` and
  `P_* = (57/8 − 7√2/2, −165/8 + 417√2/32)` (V13 L10733-10747). `sec:v14` uses the same curve
  (V14 L22820-22825; `P = (c_*, a_*b_*)` with `a_* = −1 + 7√2/4`, `b_* = 39/8 − 9√2/2`, which is
  `P_*`, checked by hand).
- With `ε = 1 + √2`, `(x, y) ↦ (ε⁴x, ε⁶y)` sends the main curve (`d = 75 − 53√2`, N5 L257) to it
  and `P₀` to `P_*` (`scratch/v14-routes/checks.py`, output `checks.output.txt`).
- So `ZInQ.mordellWeilE` would transfer by an isomorphism.

### 5.2 Its height input

- `hyp:o8-height` (V13 L6854, V14 L7627; statement identical, proof changed from 848 to 1134
  lines): `h(a) ≤ H_* M_5(a)^24` with `log₂ H_* < 4783227`, for the contacts `∞, 0, 1, 2401,
  −343/32`.
- `thm:quartic-height19` (V13 L8922, V14 L9981; statement and proof identical): exponent 19,
  `log₂ H_19 < 2093966`.
- Version 14 changes the proof of `hyp:o8-height` (hunks 27-35) in the same way as Theorem 4.1:
  - a full level-3 marking at a ramified prime, with rigidity, projectivity and the generic moduli
    problem (`sec:h5-full-three-construction`, V14 L7729);
  - modularity through `lem:qm-modularity-descent` (V14 L8296);
  - the compatible system and conductor at every `ℓ`.
- Version 13 had marked this step "Proposed repair of the original H5 arithmetic step.
  Independent review pending" (V13 L7093) and "UNAPPLIED CANDIDATE: global review and published
  Pan match are pending" (V13 L7427). Version 14 replaces both comments.
- In Version 13 the quartic route already used the Calegari formulation (V13 L7239).
  Version 14 moves that approach into Theorem 4.1.
- It remains an estimate of the same depth as Theorem 4.1 for another contact set.

### 5.3 Its pole input

- `hyp:o8-pole` (V13 L7720, V14 L8779): statement and proof identical. Its proof "applies the
  existing Theorem hyp:RC and Lemma lem:corank" (V13 L7731-7733).
- The quartic route still rests on RC for the `x + 3ℓ` curves, so the RC repairs of §2.5 matter
  to upstream, not to us.

### 5.4 Its prime input

- `thm:v5-simultaneous-primes` (V13 L16566, V14 L17540): statement identical. In its appendix,
  Dodos–Kanellopoulos Theorem 5.1 is replaced by Green–Tao's relative inverse theorem
  (Proposition 10.1) with `local-gi`, and a full-prime majorant lemma `lem:ga-full-prime-majorant`
  is added (hunks 54-55).
- The first version's assessment stands (SPECULATIVE): Tao–Ziegler's polynomial theorem gives the
  primes and the single-prime Chebotarev conditions, but not the coprimality of adjacent norms
  across different members of the pattern. So this input is harder than our GreenTaoDense plus
  GoodPrimeDensity.

## 6. Effect on each hypothesis, and the cost of adopting the quartic route

**SixContactMin** (`ZInQKernel/Hypotheses/HeightMin.lean`).
- Statement and constant unchanged from 11/5 (VERIFIED).
- The justification is repaired: new modularity lemma, polarization correction, the integral
  model identified, Carayol cited, published editions (§2.2).
- No weaker hypothesis results: Version 14 proves the same inequality.
- The quartic route's `H_19` is as deep and concerns another contact set.
- Our trust statement for H should name Calegari/Pan, not Pan Thm 1.0.4 with Berger and Conrad,
  if it follows Version 14 (SPECULATIVE recommendation).

**CertifiedRankSel** (`ZInQ.RouteK.Selmer.CertifiedRankSel`).
- Lemmas 5.4 and 5.5 are unchanged as statements (VERIFIED).
- Their proofs pin Poonen–Stoll and move Kolyvagin from the MPIM preprint to the ICM 1990
  Proceedings (§2.3). This narrows, but does not close, nt-tyz §5.2 item 1.
- Route K uses neither RC nor its proof (VERIFIED).
- The pointer to OpenAI's pointwise 2-converse (§7) is unchanged.

**GoodPrimeDensity** (`ZInQKernel/Hypotheses/GreenTao.lean`).
- Unaffected (VERIFIED): §6's tests are unchanged, and the only change in §6, the GI source of
  Proposition 6.2, lies outside its justification.
- **GreenTaoDense** is proved in Lean.
- **22P** keeps its statement. Its upstream justification now uses an unpublished GI supplement
  (§2.4).

**Cost of switching to the quartic route** (SPECULATIVE). Unchanged:
- a small finite part (299 variables) but entirely new arithmetic: charts, formal logarithms,
  Lucas growth, root height, parity anchor, common-scale groups, weak approximation;
- three hypotheses in return: `H_19` (as deep as H), RC or a redone Route K for `Ψ`, and the
  Gaussian prime theorem (harder than ours);
- legal under the frozen target, but it buys nothing.

## 7. Items worth recording

**OpenAI's pointwise 2-converse** (UNCHECKED). The citation is unchanged in Version 14 (VERIFIED,
§4).
- Version 13 calls RC "the `E = E_ℓ`, `s₂(E) = 1` case" of its Theorem 1.1.
- If that theorem covers the curves `C_d`, it is a second, unrefereed source for CR₃^Sel, next to
  Lemma 5.4 and Lemma 5.5 (SPECULATIVE).
- The preprint (`openai/math`, revision 4eaee875…) could not be read here.

**A survey as the modularity supplier** (VERIFIED, §2.2). Version 14 cites Calegari's ICM survey
sentence for Pan's theorem and keeps Pan as "proof source". Two points for our notes:
- h-leaves and ser-ell describe A011 as Pan Thm 1.0.4 with potential semistability. That is
  still what the survey sentence reports.
- The survey's "geometric" includes irreducibility and pst ⟺ de Rham, so Berger is folded in,
  not removed (SPECULATIVE reading).

**Project supplements.**
- Version 14 hands parts of three arguments to versioned upstream proof files that are not in
  the TeX:
  - Theorem 4.1: `direct-p5-modularity`, `a001-moduli`, `ly-d6-normalization`,
    `b11-integral-model`, `igusa-theta`;
  - Proposition 6.2: `local-gi`;
  - RC: `cj-conductor-one`, `cj-cm-inputs`, `cj-good-reduction`.
- Upstream's guide calls its application records "not a proof of the arithmetic, authentication
  of an agent identity, or approval to publish" (upstream `GUIDE.md`).
- For SixContactMin this means part of the paper proof now lives in unrefereed supplements, as
  do our own NoCM and ser-ell notes (SPECULATIVE assessment; none of the supplements was read).

**The quartic route's height constant.** `H_19 < 2^2093966` against `log H₆(D) ≈ 17·D·E₀·log D`.
The size bounds already absorb the large constant (nt-h §1.3). No Lean consequence (SPECULATIVE).

## 8. Recommendation

Version 14 weakens none of our hypotheses, so the priorities stand. One cheap step is added for
SixContactMin.

1. **Finish GoodPrimeDensity** (Lean work in progress on `wip/pd-lean-1`, `wip/pd-lean-2`,
   `wip/pd-sieve`). It is the only hypothesis of the narrowest variant that Lean work can remove
   outright. GreenTaoDense is done. Version 14's prime changes concern 22P and the quartic
   route, not Proposition D.
2. **Then CertifiedRankSel: its elementary half into Lean.** This is the first version's task,
   unchanged: tyz-5b §4, Lemma 4.1, Lemma 4.2 and Theorem 4.3 over `ZMod 2` from the Route K
   Legendre data.
   - *Success:* `lake build` and `check_target.py` pass, Theorem 4.3 is proved for every `r`
     with the standard axioms, and a `decide +kernel` cross-check for `r ≤ 4` agrees with
     brute-force counts.
   - *Chance:* high. *Payoff:* medium.
   - Version 14's switch of Kolyvagin to the ICM address removes nothing from this chain. The
     citation question of nt-tyz §6 route 2 can be closed on paper later.
3. **SixContactMin: re-base before doing more.** h-leaves, rs-height and ser-ell inventory the
   11/5 proof of Theorem 4.1, which Version 14 has partly rewritten.
   - *First task* (paper, about one session): map h-leaves' 23-row table (§5.1) onto V14
     L448-1680. For each row record the new citation and line range; mark the leaves Version 14
     removed (Berger, Conrad, Brinon–Conrad, LNY, Milne's notes) and added (Calegari survey,
     Deligne–Serre, Kato 2004, Washington, Shimura translate, Deligne 1971, Fontaine 1994, Milne
     1986/2005, Serre–Tate, Carayol 1987, Igusa 1967); and list the five project supplements as
     unread.
   - *Success:* every `\cite` in V14 L448-1680 is accounted for, and the open checks of h-leaves
     §6 are restated against Version 14.
   - *Chance:* high.
   - After that, nt-h §5 (the Serre route, NoCM) continues as planned. Version 14 makes the Serre
     route a replacement for `lem:qm-modularity-descent`, not for Pan's Theorem 1.0.4 with Berger
     and Conrad.

## Scripts

- `scratch/v14-routes2/hunks.py`: lists the hunks of `diff -u` between two sources (CRs removed),
  with line ranges, removed and added counts, enclosing sections and changed labels.
- `scratch/v14-routes2/stmts.py`: compares a labelled statement and its following proof between
  two sources and reports identical or changed.
- `scratch/v14-routes2/log.md`: the work log of this revision.
- `scratch/v14-routes/checks.py` (first version): exact arithmetic in `ℚ(√2)` for §5.1.
