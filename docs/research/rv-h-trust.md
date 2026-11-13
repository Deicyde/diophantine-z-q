# Review of h-trust.md: the trust statement for H

Status: adversarial review (task rv-h-trust, 2026-11-11) of `docs/research/h-trust.md` as merged at
81057fcc (below: *the note*). "N5 Lxxx" refers to the frozen 11/5 manuscript `diophantine_zq.tex`
(commit 97cec7fd, sha256 `cb1148cd…`). "11/4" is the manuscript at commit 09c0c3f3 (sha256
`bfc4192d…`), which is the text the Astra reviews accepted. The work log, the reruns and the scripts
are in `scratch/rv-h-trust/`.

Marks:

- **VERIFIED**: checked in this task, by reading N5, the 11/4 text, a repository note or the Lean
  source, or by a computation in `scratch/rv-h-trust/`.
- **STANDARD**: a published theorem, with a reference. There is no network here, so every locator
  is unread in this task.
- **ASTRA-READ**: the repository's Astra records (`docs/reviews/height-replacement/`) say that the
  reviewer opened the primary source at that place. This is a model's reading, not a human's,
  but it is a reading.
- **SPECULATIVE**: an assessment.

## Verdict

**Adopt after the listed repairs (§6).** No step of the proof is missing in a way that affects the
mathematics, no constant changes, and no unpublished upstream supplement is an input. But the note
was written in parallel with rv-h-b1 and is stale where that review landed. It also states the
review coverage of four N5 paragraphs wrongly, and its list of unread locators ignores readings
already recorded in the repository. The repairs are bookkeeping and citations; none changes an
argument.

| Question | Answer |
| --- | --- |
| (1) Completeness: does every step of Theorem 4.1's proof appear in the outline? | **Yes for the N5 text.** Every line range from L405 to L964, and the lemma at L10938-11000, falls in a step (§1.1). Three steps use refereed inputs that neither N5 nor the outline names; the main one is in C8 (§1.2). Between Theorem 4.1 and the Lean statement nothing is skipped (§1.3) |
| (2) Suppliers and statuses | **Mostly honest, with four wrong review attributions** (C3, the Milne paragraph of A9, the Li–Shimura sentence of C9, and the [U] marks of A4-A6). One locator contradicts the repository's reading of the source (E1, Faltings) (§2) |
| (3) D1 (Scholze + Berger) and D2 (Faltings 1983) | **Both valid as used.** D2 does make W4 irrelevant. D1's reason ("no new repository argument") holds only because N5's de Rham lemma already exists, and that lemma had no review before this one (§3) |
| (4) Residual list | **Item (iii) is now covered** (rv-h-b1), and §2.5 overstates what is unread. **Missing:** the p-adic Hodge theory of the eigenform (C8), the polarization uniqueness in A4, the three N5-only paragraphs that only this review has read, and N5's own integral-model route as a second route for A5-A6 (§4) |
| (5) Docstrings and KERNEL_PLAN row | **They name no supplement as an input.** But they say Lemma PR is unreviewed (stale). Their list of model-reviewed arguments omits the twist, the de Rham lemma and the theta-height comparison. And "no unpublished supplement" should say "upstream" (§5) |

## 1. Completeness (question 1)

### 1.1 Line coverage (VERIFIED by reading N5 L376-966 and L10935-11006)

| N5 | Steps | Remark |
| --- | --- | --- |
| L405-422 | A1, A2 | |
| L423-441 | A3 | N5 prints `|(𝒪/3𝒪)^*| ≤ 81`; the true value 72 (form_check, rv_checks R4) fits |
| L443-530 | A4-A6 | replaced by Lemma PR; see §4 item 4 for N5's own route |
| L532-543 | A7 | |
| L544-563 | A8 | |
| L564-577 | A9 | L564-570 (Milne paragraph) is new in N5, see §2.1 |
| L578-631 | A10 | replaced by NoCM. The constant `C_cm` stays in `H₆` and is now vestigial: the max only weakens the bound |
| L632-716 | B1-B3 | |
| L719-795 | C1-C10 | |
| L796-857 | D1-D5 | |
| L860-905 | E1-E4 | |
| L908-964 | F1-F4 | |
| L10938-11000 | C3 | the lemma `lem:de-rham-descent` |

The proof cites 24 bibliography keys (count by script over N5 L398-966 and L10935-11006). Every key
is in the note except `faltings1988`, which appears only in the closing remark after the lemma and
is not used. `fowler` and `cmheight` occur only in the CM paragraph, which NoCM deletes. The proof
cites no supplement (grep for "supplement" and the supplement names: no hit in that range).

One more implicit input is checked here (VERIFIED, `branch_check.py`). For `u ∈ ℚ \ 𝒞`, `J(u)` is
not a branch value:

- `J + 16/27 = 16H²/(27G⁶)`;
- the three quadratic factors of `H` have discriminants 10800, 43200 and 43200, which are not
  squares;
- `disc G = −10800`.

So the fibre lies over a point where `Y₃ → P¹_j` is étale. A5 (h-b1 M8) and A7 use this. N5
states only "finite and nonzero".

### 1.2 Inputs used but not named

1. **C8, the twist and the weight (N5 L757-768). The main finding of this section.**
   - N5 says that the twisting character "is a de Rham subrepresentation of the Hom
     representation". It then compares `{0, −1}` with "the modular weights `{0, 1−k}`".
   - Both statements need the `5`-adic representation `ρ_g` of a cuspidal eigenform of
     arbitrary weight `k` to be Hodge–Tate at 5 with weights `{0, 1−k}`. For the first statement,
     Hodge–Tate is enough: Tate's local algebraicity applies to Hodge–Tate characters.
   - This is a theorem of p-adic Hodge theory for modular forms (STANDARD):
     - Faltings, *Hodge–Tate structures and modular forms*, Math. Ann. 278 (1987), for
       Hodge–Tate;
     - Scholl, Invent. Math. 100 (1990), together with Faltings 1989 or Tsuji 1999, for de Rham;
     - or Saito, Invent. Math. 129 (1997).
   - Neither N5 nor the note cites it. Version 14 used Kato 2004 at this point (h-a011 §4). The
     note's C8 lists only the local algebraicity of characters.
   - The Astra descent addendum (item 5) accepted the argument without naming this input.
   - It is refereed and standard. But the note's claim in §2 ("everything not listed here is a
     refereed theorem cited in §1") is false until it is added.
2. **C9.** Two more standard inputs:
   - twisting an eigenform by a Dirichlet character gives an eigenform (Shimura's book, §3.6, or
     Atkin–Li, Invent. Math. 48 (1978));
   - the passage to the primitive newform (Li 1975, already cited, main theorem).

   Locators UNVERIFIED.
3. **C10.** Two standard inputs not listed:
   - Brauer–Nesbitt needs the modular side semisimple: Faltings Satz 3 applied to `A_f/ℚ`, which
     is already a leaf;
   - the specialization `V_ℓ(A) ≅ V_ℓ(Ā_v)` at good reduction (Serre–Tate 1968).

   The Astra descent addendum (item 6) gives Milne, *Abelian varieties*, Prop. 10.20 as a locator
   for the independence of `ℓ`. That is course notes, so the note's Mumford §19 Thm 4 is the
   better citation.
4. **D4.** The bound `a_p ≤ 2 + 2U₀` uses the Artin–Swan conductor in upper numbering (Serre,
   *Corps locaux*, VI §2). D1 cites only III §6 and IV §§1-3.
5. **A4.** rv-h-b1 §7 item 2 needs the principal polarization with Rosati involution
   `a ↦ μ⁻¹āμ` to be unique. Otherwise `λ` adds data to the moduli problem.
   - The note's A1 says this uniqueness is "not needed". That is right for A1, which only writes
     down the form, but A4 needs it.
   - A proof is elementary (VERIFIED as an argument). If `λ' = λ∘a` has the same Rosati
     involution, then `a` is Rosati-symmetric and central in `End⁰(A_ℚ̄)`, which is `B` or
     `M₂(k)`. So `a ∈ ℚ_{>0}`, and both polarizations principal give `a = 1`.
   - Alternatively cite Rotger (rv-h-b1).

Items 2-5 are routine. Item 1 is the one a referee would ask about.

### 1.3 From Theorem 4.1 to the Lean statement (VERIFIED)

- **`SixContactEstimate`** (`Hypotheses/Height.lean`) matches N5 L380-403. The checks:
  - the quantifiers: ∀S (primes, containing the primes ≤ 324), ∀R ≥ max(D, max S, 10¹²),
    ∀u ∉ 𝒞;
  - `ratHeight`;
  - `contactSupport` (positive odd valuations only, as at N5 L389);
  - the constants.

  This agrees with docs/kernel-audits/hypothesis-audit.md §H. N5's last sentence ("every
  permitted larger R") is the ∀R.
- **`SixContactMin`** is derived in Lean (`ZInQKernel/Main.lean:70`). The derivation uses four
  facts:
  - `S_mul` consists of primes;
  - it contains the primes ≤ 324;
  - `max S_mul ≤ D`;
  - `10¹² ≤ D`.

  The note's HeightMin draft names only the second and third (§5).
- **R-uniformity.** Every place where the proof uses `R` uses only the lower bound:
  - `m ≤ 2R^R M` uses `max S ≤ R`;
  - tameness at `p > R` uses `R ≥ D`;
  - `Q ≥ 10¹²` is used in the transfer.

  So the outline's claim that the proof "is uniform in admissible S and R" holds.

## 2. Suppliers and statuses (question 2)

### 2.1 Which N5 text the Astra reviews read (VERIFIED by diff)

`git show 09c0c3f3:diophantine_zq.tex` has sha256 `bfc4192d…`, the hash recorded in Astra's
`FINAL_REVIEW.json` and in both addenda. The Theorem 4.1 section of that file was compared with
N5 (`scratch/rv-h-trust/thm41_n4_vs_n5.diff`). Inside the proof, N5 differs from 11/4 only here:

| N5 | Change | Who has reviewed the N5 text |
| --- | --- | --- |
| L417-419 (A1) | Riemann-form convention sentence added | form_check (cosmetic) |
| **L564-570 (A9)** | **Milne paragraph added**: polarizable tori, Hodge endomorphisms algebraic and defined over `ℚ̄` | **nobody before this review** |
| **L734-737 + L10938-11000 (C3)** | **11/4 said "finite-extension descent … [faltings1988]"; N5 substitutes Lemma `lem:de-rham-descent` (Scholze route). 11/4 has no such lemma** | **nobody before this review**. h-leaves §3.1 read it, but h-leaves is an inventory, not a review |
| L759-761 (C8) | local algebraicity citation added | the argument is as in 11/4 (Astra descent addendum, item 5) |
| **L768-772 (C9)** | **Li's Fricke formula + Shimura Thm 1 sentence added** | **nobody before this review** |
| L776-781 (C10) | "arithmetic Frobenius lift" becomes "lift of `x ↦ x^p`" | cosmetic |
| L804-811 (D1), L828-830 (D3) | Herbrand derivation, Silverman IV.6.4 | rv-h-novel (on N5) |
| L908-927 (F1) | LY/LNY substitution written out | igusa_check.py (rerun) |

Everything else in the proof is identical in 11/4 and N5. So the note's "[M] (Astra …)" is
accurate for A2-A3, A7, A8, the centralizer part of A9, B1-B3, C1-C2, C4-C7, C10, D2, D4-D5, E and
F2-F4. It is **not** accurate for C3, the Milne paragraph of A9, or the Li–Shimura sentence of C9.

**Review here of the three N5-only passages** (VERIFIED as arguments; this is a single model
review):

- **Lemma `lem:de-rham-descent`.** It holds, given Scholze Cor. 1.8 and Thms 9.1 and 9.3 with the
  corrigendum (locators UNVERIFIED).
  - The weight step is right. `(V ⊗ C) ⊗_{C,τ} ℚ̄_ℓ = V ⊗ ℚ̄_ℓ` has weights `{0,0,−1,−1}`, which
    is twice the weights of `r ⊗_τ ℚ̄_ℓ`. So `r` has weights `{0, −1}` at every `τ`. HT weights
    do not change under restriction to `G_F`.
  - The descent paragraph is Hilbert 90 for the semilinear `Gal(F'/K)`-action on
    `(B_dR ⊗ W)^{G_{F'}}`, and it is correct.
- **A9's Milne paragraph.**
  - For `σ ∈ Aut(ℂ/ℚ̄)`, `σφ` and `φ` agree on torsion, which is Zariski dense. So `φ` is
    fixed by `Aut(ℂ/ℚ̄)`, hence defined over `ℚ̄`.
  - The centralizer step: the rational elements of `B ⊗ B^op` commuting with right
    multiplication by `J` are `B ⊗ Z_B(J)`, with `Z_B(J) = ℚ` or an imaginary quadratic
    `k ⊂ B`.
  - Correct.
- **C9's sentence.** Correct, provided Shimura 1973 Thm 1 asks exactly for a Hecke- and
  Fricke-stable span, which is what Li's formula supplies. That provision is UNVERIFIED. After
  that, Eichler–Shimura, Chebotarev and Faltings semisimplicity place `r₅` in `V₅(A_f)`.

### 2.2 Statuses

1. **A4, A5, A6 are no longer [U].**
   - rv-h-b1 was merged at 3aae7eed, before the note at 81057fcc. It finds Prop. TS, Lemma NV,
     M1-M10 and Lemma PR (i), (ii) "hold as stated". It finds the identification A4 "holds
     (STANDARD) once four citations are made explicit" (rv-h-b1 §7).
   - So A4-A6 are [M] (rv-h-b1), subject to rv-h-b1's repairs 1-6.
   - The note's Summary counts (7/5/21/3), §2.2 and the "unreviewed" wording in §3 are stale.
2. **The status rule is not applied as stated.** The note defines a step's status as "the weakest
   of its suppliers". Yet C6 and D4 are marked [M] while "inheriting [U]", and A8 (`L` unramified
   outside `T`) uses A5 and A6 without saying so.
   - Since A4-A6 are now [M], the labels do not change.
   - But the rule should say that the status is local, meaning the step's own argument, and that
     every downstream step inherits the weakest upstream status.
3. **C3** is [M] by this review only, not by Astra (§2.1). The note's "(Astra 'descent'; read in
   h-leaves §3.1)" is wrong on both counts.
4. **C7.** The hypothesis check is reviewed on N5 directly:
   - Astra descent AUDIT (the Pan item) and Astra whole REPORT ("Scalar descent and modularity")
     check Pan's hypothesis list against text identical to N5's C2 and C4-C6;
   - C3 is covered by §2.1.

   The detour through rv-h-a011 (Version 14) is not needed, but it is harmless. ASTRA-READ: Pan
   arXiv v2, Thm 1.0.4 with Conj. 1.0.1. The JAMS text has been read by no one.
5. **C9's "application [M] (Astra 'descent')"** covers only the 11/4 part, as §2.1 shows.
6. **E1 locator conflict.** The note cites "Faltings 1983, Satz 4 (the Hom theorem)". The Astra
   descent AUDIT (ASTRA-READ, printed pp. 360-361) says that Satz 3 is semisimplicity, Satz 4 the
   endomorphism comparison, and **Korollar 1 the Hom comparison**. Cite Korollar 1, or Satz 4
   applied to `A × J`.
7. **The other statuses checked hold**: A1, A2, C4, D5, E2, E3 and F1 as [R] or [S]; C2, C9, E4 and
   F3 as [R] plus model-reviewed bookkeeping; the rest as [M].

### 2.3 Scripts (VERIFIED; reruns in `scratch/rv-h-trust/reruns/`)

| Script | Outcome here |
| --- | --- |
| `scratch/h-v14/form_check.py` | identical to saved output |
| `scratch/h-v14/igusa_check.py` | identical |
| `scratch/h-b1/b1_checks.py` (now on main) | identical |
| `scratch/rv-h-cm/check.py` | identical |
| `scratch/rv-h-novel/c1_constants.py` | identical to `scratch/h-trust/reruns/` |
| `scratch/rv-h-novel/c2_sqrt_criterion.py` | identical to `scratch/h-trust/reruns/` |
| `scratch/rv-h-novel/c3_breaks.py` | "ALL OK: True" on 15 local Galois extensions. The note says "not rerun"; it is rerun now |

The note says "seven exact scripts" (Summary 4(d), §2.7(iv)). Its own table lists nine scripts in
eight rows. rv-h-b1's `scratch/rv-h-b1/rv_checks.py` (R2 elliptic enumeration, R6 neatness) is now
an input of A4-A5 too. This is cosmetic.

## 3. The two base-shrinking choices (question 3)

**D2 (Faltings 1983 instead of GR14 + Tate): valid, and it does make W4 irrelevant.** W4 (h-map
§2.3) asks whether GR14 Theorem 1.4 is proved without Faltings' Tate theorem. That question matters
only if GR14 is to replace Faltings, which was h-leaves R5.1. Under D2 both are leaves, and GR14 is
used only for E3's explicit degree bound. A dependence of GR14 on Faltings is then a dependence
between two accepted leaves, not a circularity. VERIFIED as reasoning.

Two qualifications:

- The Hom locator should be Korollar 1 (§2.2 item 6).
- Faltings' 1984 erratum should be checked: it must not touch Satz 3, Satz 4, Korollar 1 or the
  height-variation lemma used in E4 (UNVERIFIED; E4 already offers Raynaud, Astérisque 127, as an
  alternative).

**D1 (Scholze + Berger instead of Lemma PG + crystalline comparison): valid as used, with its
reason overstated.**

- What holds:
  - Pan's Theorem 1.0.4 asks for pst, through Conj. 1.0.1 (h-leaves §3.1; rv-h-a011 §2;
    ASTRA-READ).
  - Scholze's comparison gives de Rham. Berger's theorem gives dR ⇒ pst (ASTRA-READ numbering:
    Thm 0.7 / Cor. 5.22 in the author's published version; Thm 0.6 / 5.19 in arXiv v3, Astra
    descent addendum item 3). The note calls the journal number UNVERIFIED and does not mention
    this record.
  - Both papers are refereed.
- What is overstated. "Need no new repository argument" is true only in the sense that N5's
  lemma `lem:de-rham-descent` already exists. The note's own status claim for that lemma ("Astra
  'descent'") is false: no review read it before this one (§2.1).
  - The trade is therefore Scholze (with corrigendum and the GAGA step, Thms 9.1 and 9.3),
    Berger, and an N5 lemma with one model review (this one),
  - against Lemma PG (four lines, from inputs already in the base: SZ Thm 3.5, NOS, `B ⊗ ℚ₃`
    division), (Cris) (sources UNCHECKED) and the same descent paragraph, which C8 needs in either
    route (h-leaves §3.4).
- Both routes are sound, and D1 is a reasonable choice. It removes nothing relative to N5; the
  note does not claim it does. SPECULATIVE recommendation: name option (a) of h-leaves §3.2
  (Fontaine / Faltings 1989 / Tsuji 1999, citation-only, no GAGA step) as the fallback if
  Scholze's analytic comparison is questioned.

## 4. The residual list (question 4)

**Listed but in fact covered:**

1. **§2.2 / §2.7(iii), "Lemma PR and the moduli identification (unreviewed)".**
   - Lemma PR is model-reviewed by rv-h-b1, holding after repairs that do not change the
     argument.
   - The identification is a citation task: rv-h-b1 §7 inputs 1-4, including the explicit
     statement that NV, PR(ii) and Baba–Granath's `j` use one `ℚ`-structure.
   - Move both to §2.1 (model-reviewed) and list rv-h-b1's repairs 1-6 as conditions.
2. **§2.5 overstates the unread set.** The Astra records (ASTRA-READ) already contain primary-source
   readings of the following:

   | Source | Places read | Astra record |
   | --- | --- | --- |
   | Faltings 1983 | Satz 3, Satz 4, Kor. 1, pp. 360-361 | descent/AUDIT |
   | Silverberg–Zarhin | Thm 3.5, p. 406, `n ≥ 3` | conductor/AUDIT |
   | Berger | numbering as in §3 | descent/ADDENDUM |
   | Javanpeykar | Thm 1.1.1, p. 90; §2.3, p. 98; original Faltings metric | height/AUDIT, whole/REPORT |
   | GR14 | Thm 1.4 (the exact `κ(A)`, original stable Faltings normalization, both directions); §9 (Bost's `−3 dim/2`); pp. 2058-2060, 2098, 2101-2102 | height/AUDIT |
   | Pazuki | §2.3, Cor. 1.3(2), the `log π` shift for `g = 2` | whole/REPORT |
   | Baba–Granath (MPI preprint) | §2.1 Thm 1, §3.2 | whole/REPORT |
   | Pan | arXiv v2 | descent/AUDIT, whole/REPORT |
   | Milne ADT | Ch. I | descent/AUDIT, whole/REPORT |

   - So the note's item 3 (GR14) is settled, as far as a model reading goes, and items 6, 9 and
     part of 10 are as well.
   - Item 1 is half settled: the arXiv text is read, the JAMS text is not.
   - Item 8 is settled.
   - Mark these ASTRA-READ rather than UNVERIFIED. The note's definition of UNVERIFIED ("no one
     in this repository has read the source at that place") is not met for them.

**Missing from the residual list:**

3. **The p-adic Hodge theory of the eigenform (C8, §1.2 item 1).** Add it to C8's suppliers, to
   §2.5 as a new locator, and to the docstring's refereed list.
4. **N5's own route for A5-A6.**
   - Astra whole REPORT reviewed N5 L443-530 (identical in 11/4) and accepted it: the "workable
     tame extension argument", Buzzard Thm 2.1/Cor. 2.3 ASTRA-READ, and the polynomial checks in
     `whole/arithmetic.json`.
   - So A5-A6 have two independent model-reviewed routes: B1 (rv-h-b1) and N5's integral model
     (Astra).
   - The note presents B1 as the replacement of an unread supplement. In N5 the integral-model
     text is inline and has a review. B1 still removes the integral model and Buzzard from the
     base, but the note should record N5's route as a fallback rather than as removed text
     (SPECULATIVE on how much weight that adds).
5. **Three N5-only passages with a single model review**: C3's lemma, A9's Milne paragraph, C9's
   Li–Shimura sentence (§2.1). Add them to §2.1 with "rv-h-trust only".
6. **A4's polarization uniqueness** (§1.2 item 5): one line, or Rotger.
7. **§2.6 conventions** should add the height normalizations:
   - Javanpeykar and GR14 both use the original stable Faltings height (ASTRA-READ);
   - Pazuki's Deligne normalization is handled explicitly by `X_D` (N5 L939-941);
   - rv-h-novel step 9 shows that `O(g)` shifts are absorbed.

   So there is no residual here. It should be said.
8. **Minor.** rv-h-novel's step-4 range "L797-818" is also off, by about +21 (C10 is
   N5 L776-795). The note's Summary item 6 names only steps 5-8.

**Not missing (checked):**

- `faltings1988`, `fowler` and `cmheight` (unused or deleted);
- the five citation swaps of §2.4 (each swap keeps the statement; Conrad's appendix and Serre
  1968 III state Tate's theorem for Hodge–Tate characters, which is all C8 uses beyond item 3);
- the CM constant `C_cm` (vestigial).

## 5. Docstrings and the KERNEL_PLAN row (question 5)

No draft names an unpublished upstream supplement as an input (VERIFIED by reading §3 of the
note). Required changes:

**Module docstring of `Hypotheses/Height.lean`:**

1. Replace "**This argument has not yet been reviewed.**" (Lemma PR) by "model review:
   `docs/research/rv-h-b1.md` (holds; its repairs are bookkeeping)". Add rv-h-b1 §7's citations
   for the `ℚ`-structure (canonical model = PEL moduli scheme; one `ℚ`-structure for NV, PR(ii) and
   Baba–Granath).
2. Change "The proof uses no unpublished supplement" to "**no unpublished upstream proof
   supplement**". NoCM and Lemma PR are themselves unpublished repository arguments, and the
   docstring lists them a few lines later.
3. The model-reviewed list should include all of the following:
   - the level-three degree and conjugates (A3, A7);
   - **the de Rham descent lemma (reviewed only in rv-h-trust)**;
   - oddness;
   - **the twist and weight argument (Astra only, on the 11/4 text)**;
   - **the theta-height comparison and the return to `u` (Astra "height")**.

   For the application of Pan, name the Astra descent and whole reviews, which read N5's text,
   alongside rv-h-a011.
4. In the refereed list, add the p-adic Hodge theory of modular forms (Faltings 1987, Scholl 1990
   or Saito 1997; §1.2 item 1). Also add: "five citations of the manuscript to lecture notes or
   preprints are replaced by refereed editions (h-trust §2.4)". As it stands, the docstring calls
   refereed some steps that N5 supports by Conrad's preprint, Brinon–Conrad and Milne's notes.
5. "It rests on the following" reads as exhaustive. Either say "principally", or add Mumford,
   Skolem–Noether and Milne ADT / Tate (Brauer group of `ℚ`).

**Docstring of `SixContactEstimate`:** correct as drafted once item 1 is done. "Reviewed by
models" is then true of every repository argument.

**`Hypotheses/HeightMin.lean` paragraph:**

- "uses only two facts about this instance" should read "the instance is admissible because
  `S_mul` consists of primes, contains the primes `≤ 324`, `max S_mul ≤ D`, and `10¹² ≤ D`"
  (`Main.lean:70-77`).
- The `SixContactMin` docstring draft is correct.

**KERNEL_PLAN H row:**

- Replace "(h-b1; review pending)" by "(h-b1; model review rv-h-b1)".
- Add "the manuscript's geometric, twist and theta-height bookkeeping (Astra; the de Rham lemma
  reviewed only in rv-h-trust)" to the model-reviewed clause.
- Add "p-adic Hodge theory of modular forms" and "Li, Shimura 1973" to the refereed list.

## 6. Repairs, by section of h-trust.md

**Summary**

- S1. Recount the statuses after A4-A6 become [M] (rv-h-b1): [U] = 0.
- S2. Item 4(b)-(c): Lemma PR and A4 are model-reviewed (rv-h-b1). A4 is a citation task.
- S3. Item 4(d): nine scripts, plus `rv-h-b1/rv_checks.py`.
- S4. Item 6: add rv-h-novel step 4 (L797-818 → L776-795).

**§1, the outline**

- O1. A4: status [M] (rv-h-b1 §7); list its inputs 1-4; add polarization uniqueness (§1.2
  item 5).
- O2. A5, A6: [M] (rv-h-b1) with its repairs 1-6. Record N5's own route (Astra whole) as a
  fallback.
- O3. A9: the Milne paragraph is N5-only; reviewed in rv-h-trust §2.1.
- O4. C3: status "[M] (rv-h-trust only)". Delete "Astra 'descent'".
- O5. C4: add Berger's published numbering Thm 0.7 / Cor. 5.22 (ASTRA-READ).
- O6. C7: cite the Astra descent and whole reviews as the N5-direct hypothesis check.
- O7. C8: add the Hodge–Tate / de Rham property of eigenform representations (Faltings 1987;
  Scholl 1990 with Faltings 1989 or Tsuji 1999; or Saito 1997) as a supplier.
- O8. C9: the Li–Shimura sentence is N5-only (reviewed here). Add the twist of eigenforms
  (Shimura §3.6 / Atkin–Li) and Li's newform theorem.
- O9. C10: add semisimplicity of `V₃(A_f)` (Faltings Satz 3) and the specialization at good
  reduction.
- O10. D4: add Serre, *Corps locaux*, VI §2 (conductor in upper numbering). D5 can import N5's
  own Carayol locator from L9778 (§§0.3-0.7, Thm A, pp. 409-411).
- O11. E1: Faltings Korollar 1 (Hom), not Satz 4 (ASTRA-READ).
- O12. The status rule: statuses are local, and downstream steps inherit (C6, D4, A8).

**§2, the residuals**

- R1. §2.1: add Lemma PR and A4 (rv-h-b1), and the three N5-only passages (rv-h-trust only).
- R2. §2.2: empty after R1. If the project wants a second model review of C3's lemma, list it
  here.
- R3. §2.3: c3_breaks rerun ("ALL OK"); add `rv-h-b1/rv_checks.py`; fix the count.
- R4. §2.5: re-mark the ASTRA-READ locators (§4 item 2). Add the C8 locator (Faltings 1987 or the
  alternatives) and Shimura 1973 Thm 1's hypothesis.
- R5. §2.6: add the height normalizations (no residual).
- R6. §2.7: change (iii) to "Lemma PR and the moduli identification (model review rv-h-b1;
  citations per rv-h-b1 §7)". Change (iv) to "nine scripts". Add "(vii) three N5 passages with a
  single model review (rv-h-trust)".

**§3, the drafts**

- D1. Module docstring: §5 items 1-5.
- D2. HeightMin paragraph: the four admissibility facts.
- D3. KERNEL_PLAN row: §5.

**§4, next step**

- N1. Items (1), (2) and (4) are done here and in rv-h-b1.
- N2. Item (3), C8, is done except the new supplier of O7.
- N3. What remains: the network checks of §2.5 as re-marked by R4. The most important are Pan's
  JAMS text, Carayol's Théorème A at `F = ℚ`, the C8 supplier, and Shimura 1973 Thm 1's
  hypothesis.

## 7. Computations

- `scratch/rv-h-trust/thm41_n4_vs_n5.diff`: `diff` of the Theorem 4.1 section, 11/4 (09c0c3f3)
  against N5 (97cec7fd).
- `scratch/rv-h-trust/branch_check.py` (sympy, under 1 s), output `branch_check.output.txt`:
  - `G⁶ − 97200F² = H²`;
  - `J + 16/27 = 16H²/(27G⁶)`;
  - the discriminants of `H`'s factors and of `G` are non-squares.
- `scratch/rv-h-trust/reruns/`: outputs of the seven reruns of §2.3, each run one at a time.
