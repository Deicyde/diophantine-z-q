# h-trust: a trust statement for H that uses no unpublished supplement

Status: research note (task h-trust, 2026-11-11; task T3 of `docs/research/h-map.md`), repaired
by task h-adopt (2026-11-11) after its review `docs/research/rv-h-trust.md` (verdict: adopt after
the repairs of its §6; changelog at the end), and by task h-c38 (2026-11-11) after the reviews
`docs/research/rv-h-c3.md` (step C3) and `docs/research/rv-h-c8.md` (step C8), and by task
h-a9c9-fix (2026-11-11) after the review `docs/research/rv-h-a9c9.md` (steps A9 and C9), and by
task h-v16-adopt (2026-11-11) after `docs/research/rv-up.md` and `docs/research/up-h.md` (steps
A2, A4, C3, C8, E4 and F1). It turns the routes of h-map §3.2 (B1-B5), the review rv-h-novel
and the earlier H notes into one numbered outline of the proof of Theorem 4.1, in the form
`ZInQ.SixContactEstimate` states it. For each step it names the supplier and gives the status.
It then lists what remains outside refereed sources (§2) and drafts the replacement docstrings
for the two Lean hypotheses (§3). The work log and the rerun outputs are in `scratch/h-trust/`.

Locator audit (task loc-adopt, 2026-11-12). The primary-source audit `docs/research/locators.md`
(AI agents with web access, not a human review) corrected several citations used here. Dated notes
in A2, A5, A7, A10, C4, C7, C8, D2, D5, E2-E4, F1, F3 and §2.5 record them. Where a correction
may affect an argument rather than a citation (A2/A5's use of ramification orders, A10's use of
the CM count) the note says so and the argument is left unchanged: a separate review task checks
those.

Sources used. All of them are in the repository or on fleet branches. No source outside the
repository could be read (there is no network).

- The frozen 11/5 manuscript `diophantine_zq.tex` (commit 97cec7fd, sha256 `cb1148cd6c77…`).
  "N5 Lxxx" refers to its lines. The proof of Theorem 4.1 is N5 L405-964, and its appendix lemma
  is N5 L10939-11000.
- On main: `h-map`, `h-leaves`, `h-v14`, `h-a011` with `rv-h-a011`, `h-cm` with `rv-h-cm`, and
  `docs/reviews/height-replacement/` (the Astra reviews).
- `docs/research/h-b1.md` (route B1), with its model review `docs/research/rv-h-b1.md` (Lemma PR
  and Prop. TS hold as stated; the identification A4 holds once four citations are explicit).
  The repairs 1-6 of rv-h-b1 §8 are applied in h-b1 (its changelog).
- `docs/research/rv-h-novel.md` (review of the novel steps, repairs R1-R3).
- `docs/research/rv-h-trust.md`, the review of this note, which also gives the first model review
  of three passages that are new in N5 (§2.1 item 1 below).
- `docs/research/rv-h-c3.md`, a second, independent model review of C3's lemma (holds as stated;
  repairs R1-R3), and `docs/research/rv-h-c8.md`, a focused model review of C8 on the N5 text
  (holds after repairs R1-R3: normalization of `ρ_g`, weight one, levels divisible by 5).
- `docs/research/rv-h-a9c9.md`, a second model review of A9's Milne paragraph (holds as stated;
  citation repairs R-A9-1, R-A9-2) and of C9's Li–Shimura sentence (holds after R-C9-1 to
  R-C9-3; R-C9-1 replaces the Euler-factor inference by the `K_f`-linear Eichler–Shimura
  relation).
- `docs/research/up-h.md`, the comparison with upstream's Versions 13-16 (Theorem 4.1 unchanged;
  its §4 recommends adopting four upstream fixes), and `docs/research/rv-up.md`, its
  verification (§2.3 checks C8's determinant argument; §3 the Baba–Granath record and F1's
  suppliers, with the scripts `scratch/rv-up/endo24.py` and `theta24.py`). Upstream's Version 16
  is cited by line ("V16 L"), as in those notes; no upstream text is copied.
- The Lean files `ZInQKernel/Hypotheses/Height.lean` and `ZInQKernel/Hypotheses/HeightMin.lean`.

Marks:

- **VERIFIED**: checked in this task, against N5, a repository note or the Lean source, or by
  rerunning a repository script and comparing its output with the saved one.
- **STANDARD**: a published theorem, cited with a locator.
- **ASTRA-READ** (after a locator): the Astra records (`docs/reviews/height-replacement/`) say
  that the reviewer opened the primary source at that place. This is a model's reading, not a
  human's (rv-h-trust §4 item 2).
- **AUDIT-READ** (after a locator): the upstream theorem-application audit
  (`docs/theorem-application-audit/evidence/`) reports reading the page scan at that place; no
  copy of the source was available in this repository (mark of rv-h-a9c9). Like ASTRA-READ, a
  model's reading, not a human's.
- **UNVERIFIED** (after a locator): no one in this repository, model or human, has read the
  source at that place. The text says where to check it.
- **SPECULATIVE**: an assessment.

Status of a step. The status is **local**: it is the weakest of the suppliers of the step's own
argument. Every step also inherits the weakest status of the earlier steps it uses (for example
A8, C6 and D4 use A5 and A6); since no step is [U] any more, inheritance changes no label
(rv-h-trust §2.2 item 2).

- **[R] refereed**: a theorem in a refereed journal, an Astérisque, SGA or LNM volume, or a
  standard monograph.
- **[P] published but unrefereed**: lecture notes or a preprint. This is used only where N5
  cites such a version today. In every case §2.4 names a refereed replacement.
- **[M] repository argument reviewed by a model only**: N5's own text, or a repository note,
  with the model review named. "Astra" means the four scoped Astra reviews of the **11/4** text
  (sha256 `bfc4192d…`, not N5; rv-h-novel, Provenance). Inside the proof the two texts differ
  only in a few passages (rv-h-trust §2.1); three of them (C3's lemma, A9's Milne paragraph,
  C9's Li–Shimura sentence) were first read by rv-h-trust, and each has a second model review:
  C3's lemma by rv-h-c3, the other two by rv-h-a9c9.
- **[U] unchecked**: a repository argument that no independent review has read.
- **[S] script**: an exact computation in the repository with its output saved. "rerun" means
  it was rerun here and gave identical output (log, Step 9).

## Summary

1. **The outline (§1)** has 36 steps in six parts: geometry, scalar descent, modularity,
   conductor, transfer, and the return to `u`.
   - 7 steps rest only on refereed theorems and verified scripts: A1, A2, C4, D5, E2, E3, F1.
   - 5 steps apply a refereed theorem through bookkeeping that has had only a model review:
     C2, C7, C9, E4, F3.
   - 24 steps are N5 or repository arguments reviewed by models only. They are covered by
     rv-h-novel (N5 text), Astra (11/4 text), rv-h-a011 (Version 14 text), rv-h-cm, rv-h-b1
     (A4-A6), rv-h-trust (the three N5-only passages in A9, C3 and C9), rv-h-c3 (C3, a second
     review), rv-h-a9c9 (A9 and C9, a second review) or rv-h-c8 (C8 on the N5 text).
   - No step is unchecked. A4-A6 (the identification of N5's level-three curve with the moduli
     scheme, and h-b1's Lemma PR (i) and (ii), which replace the integral model) are
     model-reviewed by rv-h-b1, whose repairs 1-6 are applied in h-b1.
2. **No unpublished supplement is used.**
   - `direct-p5` was never cited by N5, which applies Pan's Theorem 1.0.4 directly at L756.
     h-a011 is needed only for its hypothesis check.
   - `a001`, `ly-d6` and `igusa-theta` are replaced by Baba–Granath 2008 (Thm 2.1, Lemma 3.1;
     not Props 3.7-3.10), Lin–Yang 2020 (eq. (3), Lemma 3, eqs. (13)-(14), Examples 29-30; not
     eq. (2); the discriminant-6 example is arXiv v1 Example 29, locator audit 2026-11-12, see
     F1), Igusa 1967 and Lauter–Naehrig–Yang 2015, read through
     `scratch/h-v14/form_check.py` and `igusa_check.py` (both rerun, identical output).
   - `b11` and Buzzard 1997 (N5 L443-530) are replaced by h-b1's Lemma PR.
3. **Two choices that shorten the trust base (VERIFIED as reasoning).**
   - **(D1)** Potential semistability is taken as N5 has it: Scholze's de Rham comparison with
     Berger's monodromy theorem. It is not taken from Lemma PG plus the crystalline comparison
     (h-leaves R5.2(b)). The reason is that Scholze 2013 and Berger 2002 are refereed and need
     no new repository argument beyond N5's existing Lemma `lem:de-rham-descent`, while Lemma PG
     would add one. That lemma is itself an N5 argument with two independent model reviews
     (rv-h-trust §2.1, rv-h-c3), so D1 trades Scholze (with the corrigendum and Thms 9.1, 9.3),
     Berger and that lemma against Lemma PG and the crystalline comparison; both routes are
     sound (rv-h-trust §3). rv-h-c3 §3.2 adds a third, citation-only route: pst at 5 directly
     from semistable reduction (SGA 7 IX) and `C_st` (Tsuji 1999), with neither the descent
     paragraph nor Berger (STANDARD; SPECULATIVE as a recommendation). Fallback if Scholze's
     analytic comparison is questioned: option (a) of h-leaves §3.2 (Fontaine / Faltings 1989 /
     Tsuji 1999, citation only; SPECULATIVE).
   - **(D2)** Semisimplicity, the endomorphism theorem and the Hom theorem are taken from
     Faltings 1983, not from GR14 plus Tate's argument (h-leaves R5.1). With this choice the
     non-circularity of GR14 (h-map W4) no longer matters: GR14 is used only for its explicit
     isogeny bound, and its correctness, like that of any refereed theorem, is accepted as
     published.
4. **What remains outside refereed sources (§2):**
   - (a) N5's own arguments. These are W1: the descent, the conductor bound and the transfer,
     plus the geometric bookkeeping. They have model reviews only.
   - (b) Two repository replacements, both model-reviewed: NoCM (rv-h-cm) and Lemma PR
     (rv-h-b1).
   - (c) One identification: step A4, N5's `Y₃` as the fine moduli scheme over `ℚ`. It is
     model-reviewed (rv-h-b1 §7) and is a citation task: the four inputs of h-b1 §4A.
   - (d) Nine exact scripts in eight rows of §2.3, plus `scratch/rv-h-b1/rv_checks.py`,
     `branch_check.py`, and rv-up's `endo24.py` and `theta24.py` (A2, F1).
   - (e) Four unrefereed editions cited by N5, each with a refereed replacement named.
   - (f) About 40 locators that are UNVERIFIED, with places to check them, about ten read by
     a model only (ASTRA-READ), and a few reported by the upstream audit (AUDIT-READ) (§2.5).
   - (g) The policy that the works cited inside Pan's proof are not leaves.
5. **Drafts (§3).** The replacement module docstring and hypothesis docstring for
   `Hypotheses/Height.lean` (`SixContactEstimate`) and `Hypotheses/HeightMin.lean`
   (`SixContactMin`), and a supplement-free H row for KERNEL_PLAN.md, repaired after rv-h-trust
   §5. Task h-adopt applied them (docstrings and the KERNEL_PLAN row only).
6. **Minor finding (VERIFIED).** rv-h-novel's line numbers for its steps 4-8 are off by about
   +22. In N5 the compatible system (step 4, given there as L797-818) is L776-795, the break
   bound L796-812, semistability and odd `p` L813-823, the `p = 2` paragraph L823-846, and the
   conductor exponents with `N ≤ QM²` L846-857. Its steps 1-3 and 9, and its scope line, are
   right.

## 0. The statement, and the route through the proof

**Statement (VERIFIED).** `SixContactEstimate` (`Hypotheses/Height.lean`, the last definition) is
N5 Theorem 4.1 (L398-403) with the constants of N5 L388-397. The match was checked numeral by
numeral in h-leaves §5.2 and rechecked here by reading. `SixContactMin` is its instance
`S = S_mul`, `R = D` (`sixContactMin_of_sixContactEstimate`, `ZInQKernel/Main.lean:70`),
admissible because `S_mul` consists of primes, contains the primes `≤ 324`, `max S_mul ≤ D` and
`10¹² ≤ D`. The proof below is uniform in admissible `S` and `R` (it uses `R` only through
`max S ≤ R`, `R ≥ D` and `R ≥ 10¹²`; rv-h-trust §1.3), so it proves both.

**Route (the decisions; reasons in the Summary).**

| Part of N5 | Supplier in this outline | Removes |
| --- | --- | --- |
| L405-441, datum and quotient | N5 text, with BG 2008 and LY 2020, through `form_check.py` | `a001` (form part) |
| L443-530, integral model, `K`, good reduction | h-b1 Lemma PR (route B1; model review rv-h-b1). Fallback: N5's own integral-model text, model-reviewed by Astra "whole" (A5) | `b11`, Buzzard 1997, uncited scheme theory (A078) |
| L531-577, conjugates, Hom field, dichotomy | N5 text | — |
| L578-631, CM branch | NoCM (rv-h-cm §7.2), route B5 | Fowler, Barquero-Sanchez et al., the CM use of GR14 |
| L632-716, scalar descent | N5 text, with rv-h-novel repair R1 | — |
| L719-795, modularity | N5 text: Pan Thm 1.0.4, Scholze + Berger (D1), Faltings (D2); hypothesis check by Astra "descent" and "whole" on the N5 text, and rv-h-a011 §3.1; citations per rv-h-a011 R1-R2; eigenform p-adic Hodge theory for the twist, in the Tate-module normalization, for all levels (Saito, Scholl with Scholze, or Kato 2004) and with Deligne–Serre for weight one, and the determinant argument for the finiteness of the twist (C8, rv-h-c8, rv-up §2.3); the `K_f`-linear Eichler–Shimura relation for `r₅ ⊂ V₅(A_f)` (C9, rv-h-a9c9); route B2 | `direct-p5` (never in N5); Conrad's preprint (local algebraicity, replaced by the determinant argument of V16 L660-667) |
| L796-857, conductor | N5 text, with rv-h-novel repairs R2-R3; Carayol 1986 for I1 (B4) | — |
| L860-905, transfer | N5 text; GR14 for the explicit bound only (D2) | the W4 dependency |
| L908-964, back to `u` | N5 text, with LY, LNY, Igusa, Pazuki, through `igusa_check.py`; route B3 | `ly-d6`, `igusa-theta` |

## 1. Numbered outline of the proof of Theorem 4.1

Notation as in N5 and h-map:

- `T = S ∪ supp M`, with `M = M_S(u)`;
- `K` is the fibre field, `L` the Hom field and `L'` the descent field;
- `Q = Q_R = R^{R E₀}`;
- `r_ℓ` is the two-dimensional constituent, and `f` the newform of level `N`.

Each step gives N5 lines, content, supplier(s) with locator, and status.

### Part A. Geometry: from `u` to an abelian surface with good reduction outside `T`

**A1. QM datum** (N5 L410-420).
- *Content.* `B = (2,−3)`, `𝒪 = ℤ⟨1, i, (1+j)/2, (i+ij)/2⟩` and `μ = 2j + ij`.
  `Trd(μ⁻¹xȳ)` has the displayed Gram matrix, with determinant 1, and Rosati involution
  `a ↦ μ⁻¹āμ`.
- *Suppliers.* The algebra is `scratch/h-v14/form_check.py`, with output `form_check.output.txt`
  (rerun, identical). The Riemann-form convention is Lin–Yang, *Quaternionic loci in Siegel's
  modular threefold*, Math. Z. 295 (2020), eq. (3) and Lemma 3. Locator UNVERIFIED in the journal
  version; N5 cites arXiv:1807.00466v1. Uniqueness of the principal polarization with a given
  Rosati involution is not needed here, since the form is written down; step A4 needs it
  (rv-h-trust §1.2 item 5).
- *Status:* **[S]+[R]**.

**A2. Quotient and branch data** (N5 L420-422; the labelling of `j` at L908-909).
- *Content.* The normalizer quotient of the discriminant-six curve is `P¹_j`. Its branch values
  are `0, ∞, −16/27`, with indices `4, 6, 2`, at the CM points of discriminants `−4, −3, −24`.
- *Suppliers.*
  - Baba–Granath, *Genus 2 curves with quaternionic multiplication*, Canad. J. Math. 60 (2008),
    §2.1 Thm 2.1, Lemma 3.1 and the §3 datum (p. 739); Props 3.7-3.10 are not used. The disc
    −24 label at the `w₆` fixed points follows from `μ² = −6` and the maximality of `ℤ[√−6]`,
    and is confirmed by `scratch/rv-up/endo24.py` (rv-up §3.5 item 2). N5 cites the 2005 MPI
    preprint, whose §2.1 Thm 1 and §3.2 are ASTRA-READ (Astra whole REPORT); the journal
    numbering is UNVERIFIED. Version 14 records a
    "local index slip" in its Lemma 3.1 (h-v14 §2.2). Step A3 does not use that lemma.
  - Lin–Yang 2020, arXiv v1 Example 29 (cited as Example 30 before 2026-11-12; see the note
    below). Content VERIFIED in arXiv v1 by h-v14; the journal number is UNVERIFIED.
  - Independent check of the elliptic-point data: rv-h-cm §2.3 derives Elkies' twist constants
    from Shimura reciprocity at the three elliptic points.
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).*
  - Lin–Yang: the discriminant-6 example of arXiv:1807.00466v1 is **Example 29** (pp. 20-21);
    v1's Example 30 treats discriminant 14. h-v14 verified the content in v1 but had not
    compared the number (h-v14 row L719). The journal number (Math. Z. 295 (2020), 775-819) is
    still UNVERIFIED. Baba–Granath Prop. 3.6 (p. 742) prints the invariant tuple and is an
    alternative supplier (read by the audit; not a verification of the Lin–Yang citation).
  - Baba–Granath, read by the audit in the journal: Thm 2.1 (p. 737), Lemma 3.1 (pp. 739-740:
    `V/W ≅ P¹_ℚ`, the three distinguished images rational), §3 (p. 739), the elliptic-order table
    of §3.1 (p. 740), Prop. 3.9 and Thm 3.10 (p. 744), Cor. 3.11 (p. 745). The audit did not
    locate the 2005 preprint.
  - **Branch data.** The audit finds that `4, 6, 2` are the elliptic (orbifold) orders of the
    uniformization by the normalizer group, and that the finite degree-4 map `V → V/W`
    (`V = X₆`) has ramification index **2** at each of `0, ∞, −16/27`. The Content line above,
    "indices `4, 6, 2`", is therefore correct only as orbifold orders (or as indices of a cover
    uniformized by a torsion-free group), not as indices of `X₆ → X₆/W`. Thm 2.1 and Lemma 3.1
    alone do not fix the numerical normalization of `j`. The steps that use these indices (A5
    through h-b1's M4, which applies them to `Y₃ → P¹_j`) may be affected; the argument is not
    changed here (see the A5 note), and a separate review checks it.
- *Status:* **[R]**.

**A3. Level three, the normalizer action, and the degree** (N5 L423-441).
- *Content.*
  - `|N/(𝔸_f^* K₀)| = 4`.
  - Central ideles act trivially on `Y₃`.
  - `Γ' = N/(𝔸_f^* K₃)` acts on `Y₃` over `ℚ` with quotient `P¹_j`.
  - `deg(Y₃ → P¹_j) ≤ 4·|(𝒪/3𝒪)^*| ≤ 324`.
- *Suppliers.*
  - The local normalizers: Vignéras, *Arithmétique des algèbres de quaternions*, LNM 800 (1980),
    Ch. II. Locator UNVERIFIED; check the normalizer of a maximal order at a ramified prime.
  - `|(𝒪/3𝒪)^*| = 72`: `form_check.py` (rerun), and `scratch/h-b1/b1_checks.py` §B (rerun,
    identical). N5 L440 prints the weaker bound `≤ 81`, which suffices.
  - The action over `ℚ`: Deligne, *Variétés de Shimura*, Proc. Sympos. Pure Math. 33 (1979),
    §2.7 and §5 (UNVERIFIED).
- *Status:* **[M]** (Astra "whole"; h-b1 M1-M3 restates it, and rv-h-b1 §4 finds M1-M10 hold).
  The ingredients are [R] and [S].

**A4. Moduli interpretation over `ℚ`** (used at N5 L528, "choose a fibre"; h-b1 §4(ii) step 1).
- *Content.* `Y₃` is the fine moduli scheme over `ℚ` of `(A, ι: 𝒪 → End A, λ, η)`, with `λ`
  principal of the type fixed by `μ`, and `η: 𝒪/3𝒪 ≅ A[3]` an `𝒪`-linear isomorphism. `K₃` is
  neat.
- *Suppliers* (the four inputs of rv-h-b1 §7, written out in h-b1 §4A):
  1. Canonical model = moduli scheme, with no extra copies since `ker¹(ℚ, B^*) = 1`: Shimura,
     *Construction of class fields and zeta functions of algebraic curves*, Ann. of Math. 85
     (1967); Deligne, *Travaux de Shimura*, Sém. Bourbaki 389 (1971): Riemann's equivalence
     Thm 4.7, the homogeneous polarization and markings §§4.8-4.12, the analytic families
     §4.15, the PEL-to-Siegel closed immersion Prop. 1.15, the `ℚ`-model of the Siegel level
     §§4.16-4.17, and the canonical model of the PEL image over the reflex field `ℚ` Thm 4.21,
     Cor. 5.7 and Ex. 5.8; with Deligne 1979, 2.2.5 and 2.3.1, for the homological sign
     convention. These are the locators of V16 L979-1101 (up-h §2 row 2), adopted by task
     h-v16-adopt in place of "§§4-6". Kottwitz, J. Amer. Math. Soc. 5 (1992), §5 and §8.
     Milne, *Introduction to Shimura varieties* (Clay Math. Proc. 4, 2005), §8 and §14, is
     published lecture notes; the first three suffice.
  2. Uniqueness of the principal polarization with Rosati involution `a ↦ μ⁻¹āμ`, so that `λ`
     adds no data (rv-h-trust §1.2 item 5). Elementary proof: if `λ' = λ∘a` has the same Rosati
     involution, then `a` is Rosati-symmetric and central in `End⁰(A_ℚ̄)`, which is `B` or
     `M₂(k)` (A9); so `a ∈ ℚ_{>0}`, and both polarizations principal give `a = 1` (VERIFIED as
     an argument by rv-h-trust). Alternatively Rotger, J. reine angew. Math. 561 (2003), and
     Trans. AMS 356 (2004). N5's form has the right matrix and determinant 1 (`rv_checks.py`
     R1).
  3. The level structure: an `𝒪`-linear `η: 𝒪/3𝒪 ≅ A[3]` is a `K₃`-structure, and Weil-pairing
     compatibility up to a scalar is automatic (`ψ(xu, yu) = nrd(u)·ψ(x, y)`).
  4. Representability: `K₃` is neat (Serre's lemma; Mumford, *Abelian varieties*, §21, Thm 5;
     neatness checked in `rv_checks.py` R6), so the moduli problem is fine.

  The same `ℚ`-structure carries the Hecke action of `Γ'` (Deligne), is used by Lemma NV and
  Lemma PR(ii), and carries Baba–Granath's `j` (h-b1 §4A, Consequence). All locators
  UNVERIFIED.
- *Status:* **[M]** (rv-h-b1 §7: holds, STANDARD, once the four citations are explicit; done in
  h-b1 §4A). A citation task; [R] for the inputs.

**A5. Lemma PR(i): the fibre field** (replaces N5 L443-528; h-b1 §§1.2, 2-4).
- *Content.* `K`, the splitting field of the fibre over `J(u)`, is Galois over `ℚ` with
  `[K:ℚ] ≤ 324!` (in fact dividing 144, by h-b1 M3). It is unramified at every `p ≥ 17` unless
  some `v_p(u−c)` is positive and odd. Hence it is unramified outside `T`.
- *Suppliers.*
  - Prop. TS (h-b1 §1.2), proved from:
    - Zariski–Nagata purity, SGA 1, Exp. X, Thm 3.1;
    - Abhyankar's lemma, SGA 1, Exp. XIII, 5.3, and Grothendieck–Murre, LNM 208 (1971).

    Locators UNVERIFIED. Beckmann, J. reine angew. Math. 419 (1991), is cited for attribution
    only.
  - Lemma NV (h-b1 §3), from:
    - Shimura reciprocity for CM points on the canonical model (Deligne 1971 §3, UNVERIFIED);
    - maximality of the three CM orders (`b1_checks.py` §C, rerun);
    - the Atkin–Lehner group `W ≅ (ℤ/2)²` (Baba–Granath 2008).
  - The case analysis at `p ≥ 17`: `G⁶ − 97200F² = H²`, the resultant and discriminant supports,
    `J(∞)` and a sample of 30 cases (`b1_checks.py` §§A, E, rerun, identical, "all 30 agree:
    True"; also `scratch/h-map/beckmann_check.py`).
  - `J(u)` is not a branch value for `u ∈ ℚ \ 𝒞`: `J + 16/27 = 16H²/(27G⁶)`, the quadratic
    factors of `H` have non-square discriminants 10800, 43200, 43200, and `disc G = −10800`
    (`scratch/rv-h-trust/branch_check.py`, VERIFIED by rv-h-trust §1.1). So the fibre lies
    over a point where `Y₃ → P¹_j` is étale. A5 (h-b1 M8) and A7 use this; N5 states only
    "finite and nonzero".
- *Status:* **[M]** (rv-h-b1 §§2-5: Prop. TS, Lemma NV, M1-M10 and Lemma PR(i) hold as stated;
  its repairs 1-6 are applied in h-b1). Its inputs are [R] and [S].
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).* h-b1's table entry M4 gives the branch points and
  indices of `Y₃ → P¹_j` as `(0,4)`, `(∞,6)`, `(−16/27,2)` and cites Baba–Granath and Lin–Yang;
  Lemma NV step 2 uses that the inertia group over a branch point is cyclic of order `e_i` (M4).
  The audit shows that Baba–Granath's degree-4 cover `X₆ → X₆/W` has index 2 at each branch value
  and that `4, 6, 2` are orbifold orders. For the Galois cover `Y₃ → P¹_j` (group of order
  dividing 144, M3) the index over an elliptic point is the order of the stabilizer, which would
  equal the orbifold order if the level-3 group is torsion-free modulo the centre (neat, A4):
  SPECULATIVE, not checked here. So M4 may need a different supplier (the elliptic-order table,
  Baba–Granath §3.1, p. 740, with neatness of `K₃`) rather than a wrong number; whether the
  argument is affected is for the separate review. Prop. TS and M5-M8 use only that the branch
  values are `0, ∞, −16/27` and that `J(u)` is not one of them, which the audit does not touch.
  The argument is not changed here.
- *Fallback.* N5's own route (L443-530: the integral model through Buzzard's Thm 2.1 / Cor. 2.3,
  the tame extension argument, and the polynomial checks of Astra's `whole/arithmetic.json`)
  is inline in N5 and was accepted by Astra "whole" (11/4 text, identical there; Buzzard
  ASTRA-READ). So A5-A6 have two independent model-reviewed routes. B1 is preferred because it
  removes the integral model and Buzzard from the base (rv-h-trust §4 item 4; how much weight
  the second route adds is SPECULATIVE).

**A6. Lemma PR(ii): good reduction** (replaces N5 L529-530; used again at L556-559, L752-754,
L781 and L849-850).
- *Content.* `A` has good reduction at every finite place `v ∤ 3` of `K`, and so do all its
  conjugates `σA = A_{σx}`.
- *Suppliers* (Raynaud route; rv-a6-route §5, adopted by hsyn-fold 2026-11-12): A4; Raynaud
  (SGA 7 IX 4.7 + 3.5); Serre–Tate Thm 1; Mumford §4 (structure of `A[n]`); `B ⊗ ℚ₃` division
  (computed). Locators UNVERIFIED. In Lean (`scratch/h-decomposition/Leaves.lean`, glue-a6-alg):
  `PkgI2.goodReduction_of_QM_rational3` from the leaves `RaynaudCriterion`,
  `NeronOggShafarevich`, `TorsionStructure` alone, with the algebra step `QuatUnipotentTrivial`
  proved; axioms `propext`, `Classical.choice`, `Quot.sound`. The instantiation on N5's `A`
  (which needs A4 and the moduli objects) is not in Lean.
- *Second route* (h-b1 §4(ii) steps 2-3, kept):
  - A4 gives `A[3] ⊂ A(K)`.
  - Potentially good reduction: Grothendieck's semistable reduction theorem (SGA 7 I, LNM 288,
    Exp. IX, Thm 3.6) plus the toric-part argument of h-b1 §4(ii) step 2. Alternatively Morita,
    Hokkaido Math. J. 10 (1981). Locators UNVERIFIED.
  - Finiteness of `ρ(I_v)` and Néron–Ogg–Shafarevich: Serre–Tate, *Good reduction of abelian
    varieties*, Ann. of Math. 88 (1968), Thms 1-2. Locator UNVERIFIED.
  - `1 + 3M₄(ℤ₃)` is torsion-free (elementary; N5 L468-470).
- *Status:* **[M]** (rv-h-b1 §5: Lemma PR(ii) holds as stated, including `v | 2`; the Raynaud
  route reviewed by rv-a6-route, sound after two wording repairs). Its inputs are [R]. Fallback
  as in A5.

**A7. The conjugates of `A` are geometrically isomorphic** (N5 L532-543).
- *Content.* Baba–Granath's polarized relation gives `V_ℤ = V/W`. On the finite nonzero
  `j`-locus the polarized point is determined by
  `[J₂, J₄, J₆, J₁₀] = [12(j+1), 6(j²+j+1), 4(j³−2j²+1), j³]`. And `j = J(u)` is rational, finite
  and nonzero.
- *Suppliers.*
  - Baba–Granath 2008, Thm 2.1 (UNVERIFIED).
  - The Igusa vector: Lin–Yang 2020, eqs. (13)-(14) and Examples 29-30, through
    `scratch/h-v14/igusa_check.py` (rerun, identical). (Locator audit, 2026-11-12: the
    discriminant-6 example is v1's Example 29; Example 30 is discriminant 14. Alternative
    supplier of the tuple: Baba–Granath Prop. 3.6, p. 742. Baba–Granath Thm 2.1 was read by the
    audit, p. 737. The bracket is weighted-projective.)
  - `F(u) ≠ 0`, and `disc G = −10800 < 0`.
- *Remark.* An isogeny between the conjugates would suffice (rv-h-novel, Premises). Under A4
  the conjugates are `A_{σx}` with `σx` in one `Γ'`-orbit, so they are related by Hecke
  translates, hence isogenous (STANDARD; it would make A7 independent of the Igusa vector;
  SPECULATIVE simplification).
- *Status:* **[M]** (Astra "whole"). Its inputs are [R] and [S].

**A8. The Hom field `L`** (N5 L544-563).
- *Content.* `W₀ = Res_{K/ℚ} A` has geometric endomorphism rank `r ≤ 16F₀²`, with Galois acting
  through a finite group that injects into `GL_r(𝔽₃)`. For `L = EK`, `L/ℚ` is normal,
  `[L:ℚ] ≤ F₀·3^{r²} ≤ D`, and `L` is unramified outside `T`.
- *Suppliers.*
  - `rank Hom(A, A') ≤ 4·dim A·dim A'`: Mumford, *Abelian varieties* (1970), §19, Thm 3.
  - Finite subgroups of `GL_r(ℤ)` inject mod 3 (Minkowski's lemma; the same torsion-freeness
    of `1 + 3M_r(ℤ₃)` as in A6).
  - Néron–Ogg–Shafarevich (Serre–Tate Thm 1), at `p ∉ T` with `ℓ ≠ p`. This uses A5 and A6;
    for `p ∉ T` we have `p ≥ 17`, so `p ≠ 3`.
  - All locators UNVERIFIED.
- *Check here.* The arithmetic `16F₀²` and `F₀·3^{256F₀⁴} = D` was VERIFIED by reading.
- *Status:* **[M]** (Astra "whole"; h-leaves row 4 inventory).

**A9. The dichotomy** (N5 L564-577).
- *Content.* `End⁰(A_ℚ̄)` is `B` or `M₂(k)`.
- *Suppliers.*
  - Polarizable complex tori are abelian varieties (Riemann), and analytic homomorphisms between
    them are algebraic (GAGA, or Chow), so `End⁰(A_ℂ)` is the commutant of the complex structure
    on `H₁(A,ℚ)`. N5 cites Milne's course notes (Part I, Thms 2.8-2.9; the upstream audit reports
    that printed p. 14 states exactly this, AUDIT-READ), which are [P]. Refereed replacement
    (rv-h-a9c9 R-A9-1): Mumford, *Abelian varieties* (1970), §§1-3, with Serre, GAGA, Ann. Inst.
    Fourier 6 (1956); or Milne, *Abelian varieties*, in Cornell–Silverman (eds.), *Arithmetic
    Geometry* (1986), §1. Locators UNVERIFIED. N5's bibliography entry `milne-av` names only
    "Part I, Theorem 12.1(a)" (N5 L11024-11026), the locator of its other use (C3); the in-text
    locator at L564 (Thms 2.8-2.9) is the one to keep (cosmetic; §2.4).
  - Descent `ℂ → ℚ̄` (rv-h-a9c9 R-A9-2). N5 shows that `ᵗφ = φ` for `τ ∈ Aut(ℂ/ℚ̄)` (agreement
    on torsion, which is Zariski dense) and leaves implicit the fact that a `ℂ`-morphism between
    `ℚ̄`-varieties fixed by `Aut(ℂ/ℚ̄)` is defined over `ℚ̄` (`ℚ̄` is the fixed field and is
    perfect; descent of the graph). Equivalently, and cleaner: for abelian varieties over an
    algebraically closed `k` and any extension `K/k`, `Hom(A,B) → Hom(A_K,B_K)` is bijective
    (rigidity; e.g. Conrad, *Chow's K/k-image and K/k-trace*, Enseign. Math. 52 (2006), §3).
    Locator UNVERIFIED. STANDARD.
  - The centralizer `B ⊗ Z_B(J)^op`, with `Z_B(J)` equal to `ℚ` or an imaginary quadratic `k`
    (so `End⁰(A_ℚ̄) ∈ {B, M₂(k)}`, with equality, as A8 and A10 use): VERIFIED by rv-h-a9c9
    §1.2 item 1 (full argument; exact computation `scratch/rv-h-a9c9/a9_centralizer.py` for
    three `J` in the discriminant-6 algebra).
- *Status:* **[M]**. The centralizer step is as in 11/4 (Astra "whole"). The Milne paragraph
  (N5 L564-570: polarizable tori, Hodge endomorphisms algebraic and defined over `ℚ̄`) is new
  in N5 and has two model reviews that agree: rv-h-trust §2.1 and rv-h-a9c9 §1 (holds as stated;
  repairs R-A9-1 and R-A9-2, both citation-level, applied above). The citation is [P] until it
  is swapped (§2.4).

**A10. NoCM: `End⁰(A_ℚ̄) = B` for every rational `u ∉ 𝒞`** (replaces N5 L578-631; rv-h-cm §7.2).
- *Suppliers.*
  - `t = 1 + 27j/16` and the model `ℚ(t)(√(−t), √(3(t−1)))`: forced by the `W`-action over `ℚ`
    and by Shimura reciprocity at the elliptic points (rv-h-cm §2.3). Elkies, ANTS-III, LNCS 1423
    (1998), §3.2, serves as a cross-check.
  - The fibre over `t(u)` is a free `W`-orbit with residue field `ℚ(i)`:
    `scratch/rv-h-cm/check.py` (rerun, identical).
  - González–Rotger, *Non-elliptic Shimura curves of genus one*, J. Math. Soc. Japan 58 (2006),
    Thm 5.12 and Prop. 5.6. Prop. 5.6 may be cited only under `(f, 6) = 1`. The numbers are
    those of arXiv:math/0612732 (VERIFIED by rv-h-cm); the journal numbering is UNVERIFIED.
  - Vignéras LNM 800 for the embedding condition (UNVERIFIED).
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).* González–Rotger read by the audit in arXiv v1, v2 and
  the journal: Prop. 5.6 (journal p. 943; v1/v2 p. 15), Thm 5.8 (pp. 943-944), Thm 5.12
  (p. 946). Prop. 5.6 counts `#CM(R) = 2^{#{p | D(R)N(R)}}·h(R)` on `X₀(D,N)`; only a single
  specified orientation branch has `h(R)` points, and `(f,6) = 1` does not remove the factor
  (maximal order of discriminant −19: `h = 1`, four CM points). The fields of definition hold on
  the paper's `X₀(D,N)`, not automatically on `Y₃` or on the image in the full Atkin–Lehner
  quotient (at discriminant −24 the quotient value −16/27 is rational, while the ring class
  field has degree 4). The h-decomposition's former leaf R5 ("`#CM(R) = h(R)`") was wrong and is
  corrected there. The NoCM argument as written in h-cm (§5, and rv-h-cm §3) uses the count
  `2^b·h(𝔬)`, `b` the number of `p | 6` inert in `K` (rv-h-cm: Prop. 5.6 with `N = 1`), which
  appears to be this count (read here in h-cm.md; not re-derived). Whether the uses of the count
  and of the fields (which live on `X₀(6,1)`, while the fibre lies on `Y₃` over the quotient)
  are correct is left to the separate review; the argument is not changed here.
- *Repairs.* rv-h-cm R1-R5 must be applied when the CM paragraph is replaced.
- *Status:* **[M]** (h-cm + rv-h-cm).

### Part B. Scalar descent (N5 L632-716): rv-h-novel steps 1-3

**B1. Sign cocycle** (N5 L632-664).
- *Content.* `B`-linear isogenies `μ_σ` (Skolem–Noether), `c(σ,τ) ∈ ℚ^×`, `a_σ = (deg μ_σ)^{−1/4}`,
  and `ε ∈ {±1}`, a normalized cocycle inflated from `Gal(L/ℚ)`.
- *Supplier.* Skolem–Noether: Reiner, *Maximal orders* (1975), Thm 7.21 (UNVERIFIED).
- *Status:* **[M]** (rv-h-novel step 1; Astra "descent").

**B2. The Brauer step** (N5 L665-693).
- *Content.* `[ε] ∈ Br(ℚ)[2]` vanishes outside `T`. The Dirichlet character `χ` has the same
  local invariants, and `m ≤ 2R^R M`.
- *Suppliers.*
  - `H²(G_ℚ, ±1) = Br(ℚ)[2]`, the Hasse principle and reciprocity: Milne, *Arithmetic duality
    theorems* (Academic Press 1986; 2nd ed. 2006), Ch. I (ASTRA-READ: descent AUDIT, whole
    REPORT). Also Tate, Ch. VII of Cassels–Fröhlich (1967), UNVERIFIED.
  - The square-root criterion: `scratch/rv-h-novel/c2_sqrt_criterion.py`
    (rerun: 135 characters, 0 mismatches; output saved in `scratch/h-trust/reruns/`).
- *Repair.* Repair R1 of rv-h-novel: state `ω_p(−1) = χ_p(−1)` explicitly.
- *Status:* **[M]** (rv-h-novel step 2; Astra "descent").

**B3. The cochain β and `[L':ℚ] ≤ QM`** (N5 L693-716).
- *Supplier.* The constants: `c1_constants.py` (rerun, saved).
- *Status:* **[M]** (rv-h-novel step 3; Astra "descent").

### Part C. Modularity (N5 L719-795)

**C1. The representation `ρ_ℓ ≅ r_ℓ ⊕ r_ℓ`** (N5 L719-731).
- *Content.* It is the Tate action on `G_{L'}`.
- *Status:* **[M]** (rv-h-novel step 4).

**C2. Absolute irreducibility of `r_ℓ|G_{L'}`** (N5 L731-734).
- *Supplier.* Faltings, *Endlichkeitssätze für abelsche Varietäten über Zahlkörpern*, Invent.
  Math. 73 (1983), with erratum, Invent. Math. 75 (1984). Satz 3 is semisimplicity, Satz 4 the
  endomorphism comparison and Korollar 1 the Hom comparison (ASTRA-READ: descent AUDIT, printed
  pp. 360-361). N5 gives no locator. That the 1984 erratum touches none of Satz 3, Satz 4,
  Korollar 1 or the height-variation lemma of E4 is UNVERIFIED.
- *Status:* **[R]**. The commutant argument is [M] (rv-h-a011 §3.1 H2, against Version 14's
  identical argument).

**C3. de Rham with Hodge–Tate weights `{0, −1}`** (N5 L734-737; Lemma `lem:de-rham-descent`,
L10939-11000).
- *Suppliers.*
  - Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 and Thms 9.1, 9.3, with the corrigendum, Forum
    Math. Pi 4 (2016). UNVERIFIED in the journal; h-leaves read the arXiv introduction. Its
    hypotheses hold for `A/F` with `F` finite over `ℚ_ℓ` (rv-h-c3 §3.1 P1). It is more than the
    step needs: Faltings 1989 or Tsuji 1999 (de Rham comparison for proper smooth schemes) is a
    citation-only fallback with no GAGA step (STANDARD).
  - `V_ℓ(A) ≅ H¹_et(A_F̄, ℚ_ℓ)^∨`: N5 cites Milne's notes, Part I, Thm 12.1(a), which are [P].
    Replacement: Mumford, *Abelian varieties* (1970), §§19-20, or Milne 1986
    (Cornell–Silverman), §15.
  - Closure under duals and subquotients, and finite descent: N5 cites Brinon–Conrad, CMI notes
    (2009), Thm 5.2.1 and Props. 6.3.3, 6.3.8, which are [P]. Replacement: Fontaine,
    *Représentations p-adiques semi-stables*, in *Périodes p-adiques*, Astérisque 223 (1994),
    113-184, Thm 3.8, p. 142 (closure of de Rham representations under duals, tensor products
    and subquotients; definitions in §§3.4-3.7). This is the citation of V16 L564-565 (bibitem
    V16 L39243-39247; up-h §2 row 3), and it settles rv-h-c3 R2's exposé question by page
    range; the content is UNVERIFIED. The finite descent is the Hilbert 90 argument written in
    N5's lemma (and in V16 L566-571), from a finite Galois local extension to `ℚ₅`.
- *Galois choice of the field (task h-v16-adopt, after up-h §4 item 2).* N5 applies its lemma
  (local fields `K/ℚ_ℓ` and `F/K`) with `K = ℚ₅` and `F` a completion of `L'`, where C1 makes
  `r₅ ⊕ r₅` the Tate action of `A`. Instead, as V16 L536-537 does, let `F_glob ⊇ L'` be finite
  Galois over `ℚ` with `A` and its geometric endomorphisms defined over it, base change `A`, and
  take `F = (F_glob)_w` for a place `w | 5`. The decomposition `V₅(A) ⊗ E ≅ r₅ ⊕ r₅` restricts
  to `G_F`. This is free, since only the existence of some finite extension is used (rv-up
  §2.3). Then `F/ℚ₅` is Galois, Scholze's comparison applies to `A` over `F` directly, and the
  descent runs from `F` to `ℚ₅` with no intermediate field.
- *Repairs (rv-h-c3 §4; wording and citations, no change of argument).*
  - **R1.** Not needed with the Galois choice above. (On N5's route, which descends through a
    Galois closure `F' ⊇ F`, it is the line: `F' ⊗_F D_F → D_{F'}` is injective
    (`B_dR^{G_{F'}} = F'`), so `dim D_{F'} ≥ dim W`, and `≤` always holds; VERIFIED as an
    argument, rv-h-c3 §3.1 P5.)
  - **R2.** The citation swaps above (Milne's notes → Mumford §§19-20 or Milne 1986 §15;
    Brinon–Conrad → Fontaine, Astérisque 223, pp. 113-184, Thm 3.8, p. 142; Faltings 1989 /
    Tsuji 1999 as the fallback for Scholze). V16 L561 cites Milne 1986, Thm 15.1(a), p. 129, for
    the duality `V_ℓ(A) ≅ H¹_et^∨`, a sharper locator for the Milne 1986 option.
  - **R3.** The normalization of `ρ_g` in C8, where the lemma's weights `{0, −1}` are compared
    with the eigenform's; applied in C8 below (it is rv-h-c8's R1).
- *Shorter route (rv-h-c3 §3.2; STANDARD, SPECULATIVE as a recommendation).* `r_ℓ|G_F` is a
  summand of `V_ℓ(A_F) ⊗ C_ℓ`, and `V_ℓ(A_F)` is pst by semistable reduction (SGA 7 IX) and
  `C_st` (Tsuji 1999). So `r_ℓ|G_{ℚ_ℓ}` is pst and its Hodge–Tate weights can be read on `G_F`,
  with neither the descent paragraph nor Berger (C4). The descent paragraph is correct but not
  load-bearing; this corrects rv-h-trust §3, which said C8 needs it in either route.
- *Status:* **[M] (rv-h-trust, rv-h-c3: two independent model reviews).** The lemma is new in
  N5: the 11/4 text read by Astra said "finite-extension descent … [faltings1988]" at this point
  and has no such lemma. rv-h-trust §2.1 found the weight step and the Hilbert 90 descent correct,
  given Scholze. rv-h-c3, written without first reading rv-h-trust's treatment, found that the
  lemma holds as stated and that its conclusion is exactly what N5 uses, with the repairs above;
  the two reviews agree. h-leaves §3.1 read it as an inventory, not a review. The citations are
  [P] until they are swapped.

**C4. de Rham implies potentially semistable** (N5 L739-741).
- *Supplier.* Berger, *Représentations p-adiques et équations différentielles*, Invent. Math.
  148 (2002), Théorème 0.6 (= Théorème 5.19) in arXiv:math/0102179v3, VERIFIED there by
  rv-h-a011 §3.2. In the author's published version it is Théorème 0.7 (= Corollaire 5.22)
  (ASTRA-READ: descent ADDENDUM item 3).
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).* Both texts read: arXiv v3 Thm 0.6 (p. 6), Thm 5.19
  (pp. 56-57); published version (author-hosted copy) Thm 0.7 (p. 6), Cor. 5.22 (p. 52);
  Springer pagination unread. arXiv v3's Theorem 0.7 is a different statement. No dimension,
  oddness, residual or odd-`p` hypothesis; conclusion potentially semistable.
- *Status:* **[R]**.

**C5. Oddness** (N5 L742-751).
- *Content.* The Betti involution exchanges the Hodge summands, so `r_ℓ(c)` has eigenvalues
  `1, −1`.
- *Suppliers.* The comparison between Betti and `ℓ`-adic cohomology (Milne 1986, or SGA 4 XI).
- *Status:* **[M]** (Astra "descent"; rv-h-a011 §3.1 H5 for Version 14's version).

**C6. Finite ramification** (N5 L752-754).
- *Content.* `r_ℓ` is unramified outside `T ∪ {ℓ}`.
- *Suppliers.* A5, A6, A8, the cleanup of `β` (B3) and Néron–Ogg–Shafarevich.
- *Status:* **[M]**. It uses A5 and A6, which are [M] (rv-h-b1).

**C7. Pan's theorem at `ℓ = 5`** (N5 L755-757).
- *Supplier.* Pan, *The Fontaine–Mazur conjecture in the residually reducible case*, J. Amer.
  Math. Soc. 35 (2022), 1031-1169, cited as arXiv:1901.07166v2, Theorem 1.0.4.
  - The statement in arXiv v2 is VERIFIED by h-a011 and rv-h-a011.
  - The JAMS numbering is UNVERIFIED (repair R1 of rv-h-a011).
- *Hypotheses.*
  - continuity, irreducibility (C2), finite ramification (C6), pst at 5 (C3+C4), odd (C5) and
    distinct HT weights (C3);
  - `p = 5` makes the `p = 3` clause vacuous.

  The hypothesis check was reviewed on text identical to N5's: Astra descent AUDIT (the Pan
  item) and Astra whole REPORT ("Scalar descent and modularity") check Pan's hypothesis list
  against C2 and C4-C6, which are the same in 11/4 and N5; C3 is covered by rv-h-trust §2.1
  and rv-h-c3 §3.3 (Pan arXiv v2, Thm 1.0.4 with Conj. 1.0.1, ASTRA-READ; Pan's convention,
  `ε` of weight `−1`, is N5's). The discharge table rv-h-a011 §3.1, written for Version 14, also
  applies to N5, because the representation `r₅` and the hypothesis list are the same; its
  route (c) is N5's route.
- *Policy.* This is repair R2 of rv-h-a011: the leaf is Pan's stated theorem. The works cited
  inside its proof (Skinner–Wiles 1999/2001, Kisin, Hu–Tan, Khare–Wintenberger) are not leaves.
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).* arXiv v2 Thm 1.0.4 (p. 5) with Conj. 1.0.1 (p. 2) and
  the conventions (pp. 6-7) read; the JAMS number and page remain UNVERIFIED. At `p = 3` the
  local residual exception (semisimplification not `η ⊕ ηω`) must be kept; there is no such
  proviso at `p = 5`, so C7 is unaffected. Pan uses geometric Frobenius and cyclotomic HT weight
  −1; the arithmetic-Frobenius traces used in C8 require dualization and an adjusted twist (as
  C8's normalization paragraph already does).
- *Status:* **[R]** for the theorem; **[M]** for the hypothesis check.

**C8. The twist and the weight** (N5 L757-768).
- *Normalization (rv-h-c8 R1, rv-h-c3 R3).* Tate convention: the cyclotomic character `χ` has
  Hodge–Tate weight `−1` (as in N5 L757, C3 and Pan). `ρ_g` denotes the representation of the
  eigenform `g` (weight `k`, nebentypus `ε_g`) with `tr ρ_g(Frob_ℓ^arith) = a_ℓ(g)` and
  `det ρ_g = ε_g χ^{k−1}`, i.e. the Tate-module (arithmetic-Frobenius) normalization, as on
  `V_p(J₁(N))` for `k = 2`. Its weights are `{0, 1−k}`. N5 does not fix this, and its phrase "the
  modular weights `{0, 1−k}`" is right only in this normalization. Pan's paper uses geometric
  Frobenius: there `ρ_g` is the cohomological representation (`H^{k−1}` of the Kuga–Sato
  variety), with weights `{0, k−1}`. The two differ by duality, and `U^∨ ≅ U ⊗ det(U)^{−1}` for
  2-dimensional `U`, so bringing Pan's conclusion to the Tate-module normalization changes only
  the twisting character (h-a011 §4).
- *Content.* `r₅ ≅ ρ_g ⊗ ψ` with `ψ` continuous (Pan's "up to twist"). The `ψ`-line in
  `Hom(ρ_g, r₅)` is Hodge–Tate (N5 says de Rham, which is true but more than needed), of some
  integer weight `n`. Comparing `{0, −1}` with `{n, n+1−k}` gives `k = 2`, `n = 0`.
- *Finiteness of `ψ`: the determinant argument* (task h-v16-adopt, after up-h §4 item 1; it
  replaces N5's appeal to local algebraicity of Hodge–Tate characters at L760-761). This is
  Version 14's argument, kept in Version 16 at V16 L660-667; the wording here is ours.
  1. Let `F/ℚ` be finite Galois, containing `L'`, with `A`, its geometric endomorphisms and a
     polarization defined over `F` (the global field `F_glob` of C3). The Weil pairing of that
     polarization is `G_F`-equivariant with values in `ℚ₅(1)`, so `G_F` acts on `V₅(A)` through
     `GSp₄` with multiplier `χ`, and `det V₅(A) = χ²` on `G_F`.
  2. `V₅(A) ⊗ E ≅ r₅|G_F ⊕ r₅|G_F` (C1, restricted from `G_{L'}`), so `(det r₅)² = χ²` on
     `G_F`. The character `α := det r₅ · χ^{−1}` of `G_ℚ` therefore satisfies `α² = 1` on the
     finite-index subgroup `G_F`, and has finite image.
  3. `det r₅ = det ρ_g · ψ² = ε_g χ^{k−1} ψ²`, and `k = 2` by the weight comparison, so
     `ψ² = α ε_g^{−1}`, which has finite image. Each value of `ψ` is a square root of one of
     finitely many scalars, so `ψ` has finite image.
  4. The fixed field of `ker ψ` is finite abelian over `ℚ`, hence cyclotomic (Kronecker–Weber),
     so `ψ` is a Dirichlet character, absorbed into `f` (C9).

  The argument needs `k = 2`, which still comes from the Hodge–Tate comparison, so (HT) stays a
  supplier; it removes only the local-algebraicity step (rv-up §2.3).
- *Suppliers.*
  - **(HT) For every cuspidal eigenform `g` (every weight `k ≥ 1`, every level `N`, including
    `5 | N`, every nebentypus), `ρ_g|G_{ℚ₅}` is Hodge–Tate, with weights `{0, 1−k}` in the
    normalization above** (normalization-free form: its two weights differ by `k − 1`;
    rv-h-c8 §3.1). N5 uses this twice without a citation: the twisting character is "a de Rham
    subrepresentation of the Hom representation", and N5 compares `{0, −1}` with "the modular
    weights `{0, 1−k}`" (rv-h-trust §1.2 item 1). Hodge–Tate suffices for both uses (the weight
    comparison needs only Hodge–Tate, which is closed under Hom and subobjects). The
    eigenform of Pan's theorem can have level divisible by 5 (`T` depends on `u`, and nothing in
    N5 excludes bad reduction above 5; rv-h-c8 §3.3), so the supplier must cover all levels.
    Refereed sources (locators UNVERIFIED):
    - **for `k ≥ 2` and every level, including `5 | N`:** Saito, *Modular forms and p-adic Hodge
      theory*, Invent. Math. 129 (1997) (pst at `p` for every level; weights `0, k−1` in the
      cohomological normalization); or Scholl, *Motives for modular forms*, Invent. Math. 100
      (1990), with Scholze 2013, Cor. 1.8 and Fontaine's closure under subquotients, both already
      leaves of C3; or Kato, *p-adic Hodge theory and values of zeta functions of modular
      forms*, Astérisque 295 (2004), 117-290: §9.4, p. 188 (the realization `V` of `f` is de
      Rham, with Hodge filtration jumps at `0` and `k`), §6.3, pp. 161-162, §§5.4 and 8.3,
      pp. 155 and 181 (all levels, including `5 | N`), and (14.10.2)-(14.10.3), p. 240
      (`det V = χ^{1−k}ε_g^{−1}`, Hecke polynomial on inverse arithmetic Frobenius, so `V^∨` is
      `ρ_g` in the normalization above). These are the locators Version 14 and Version 16 use
      (V16 L618-650; up-h §2 row 4);
    - **only for `5 ∤ N`:** Scholl 1990 with Faltings 1989 (crystalline comparison); Scholl 1990
      with Tsuji 1999 covers `5 | N` only together with de Jong's alterations (Publ. IHÉS 83,
      1996);
    - Faltings, *Hodge–Tate structures and modular forms*, Math. Ann. 278 (1987) (Hodge–Tate,
      `k ≥ 2`): whether it covers `5 | N` is UNVERIFIED (check its hypotheses on the level);
    - **for `k = 1`:** none of the above. Deligne–Serre, Ann. Sci. ÉNS 7 (1974), Thm 4.1
      (weight-one forms have finite image), plus: a representation with finite image on inertia
      has all Hodge–Tate weights 0 (STANDARD). Then `ρ_g ⊗ ψ` has equal weights, which C3
      excludes. (Alternatively Pan's body produces regular algebraic automorphic
      representations, hence `k ≥ 2`; UNVERIFIED reading.)
    - Version 14 also excludes `k = 1` this way (Deligne–Serre Thm 4.1, V16 L604-616; h-a011
      §4).
  - The determinant argument: the Weil pairing of a polarization, `e(σx, σy) = χ(σ)e(x, y)`
    (Mumford, *Abelian varieties*, §20 and §23; STANDARD, locator UNVERIFIED), and
    Kronecker–Weber, Washington, *Introduction to cyclotomic fields* (2nd ed. 1997), Thm 14.1,
    p. 321 (the locator V16 L669-670 uses; UNVERIFIED).
  - No longer used: local algebraicity of Hodge–Tate characters (N5 L760-761, Conrad's preprint
    (2011), App. B, pp. 32-33, with its replacement Serre 1968 Ch. III or Tate 1967 §3.3). The
    determinant argument makes it unnecessary.
- *Check here.* In the Tate-module normalization, `{n, n+1−k} = {0, −1}` with `k ≥ 1` forces
  `n = 0`, `k = 2`; the other matching gives `k = 0` (VERIFIED as an argument). In Pan's
  cohomological normalization the comparison forces `k = 2` and twist `χ¹`, not "power zero"
  (rv-h-c8 `weights.py`, exhaustive over `k ≤ 200`, `|n| ≤ 300`). The conclusion is the same:
  for `k = 2`, `ρ_g^coh ⊗ χ = (ρ_g^Tate)^∨ ⊗ χ = ρ_g^Tate ⊗ ε_g^{−1}`, a finite twist, absorbed
  into `f` (rv-h-c8 §5; rv-h-c3 §3.4). So `k = 2` is normalization-free and "power zero" holds
  in the Tate-module normalization, which is the one C9 needs (Tate module of `A_f`).
- *Elementary steps (rv-h-c8 R4, §4 items 3-4).* rv-h-c8 R4's finiteness of `ψ` on inertia at
  `ℓ ≠ 5` is no longer needed: the determinant argument gives finiteness of `ψ` globally.
  Kronecker–Weber, which turns `ψ` into a Dirichlet character, is now cited (Washington, above).
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).* Kato, Astérisque 295 (2004), was read by the audit:
  §§9.2-9.4, especially (9.2.2), pp. 187-188, with §§6.3, 8.3, §§11.3-11.4 and §14.10.2-3
  (p. 240). It is the all-level supplier for cusp forms and newforms: no `p ∤ N` restriction,
  bad reduction handled by semistable models over finite extensions, `p = 2` included; the
  cohomological realization dualizes to the Tate weights `{0, 1−k}`. General eigenforms need the
  old/new reduction; Eisenstein series need a separate construction; weight one is outside it.
  Saito 1997 stays UNVERIFIED (body unread). Deligne–Serre Thm 4.1 (pp. 513-514) was read, with
  Lemma 3.2 for the transfer to every semisimple realization with the same traces
  (semisimplicity cannot be dropped).
- *Status:* **[M] (Astra "descent" on the identical 11/4 text, and rv-h-c8 on N5: two model
  reviews).** Astra (ADDENDUM item 5) accepted the argument without naming the eigenform input;
  its AUDIT item 6 warned against mixing the pairs `{0, k−1}` and `{0, 1−k}`. rv-h-c8 names the
  input, checks it against the N5 text, and finds that C8 holds after the repairs above
  (normalization, weight one, levels divisible by 5). The supplier (HT) is **[R]** with those
  corrections. rv-h-a011 checked Version 14's different twist argument (Deligne–Serre / Kato),
  and rv-h-novel left this paragraph out of scope. The determinant argument for the finiteness
  of `ψ`, which replaces N5's local-algebraicity sentence, is Version 14's (V16 L660-667). It was
  checked by rv-up §2.3 (sound; it removes local algebraicity but neither (HT) nor
  Kronecker–Weber) and by up-h §4 item 1; its first half, `det r₅ = α χ` with `α² = 1` on `G_F`,
  is also h-a011 §3.6, checked in rv-h-a011 §3.3.

**C9. Newform and `A_f`** (N5 L768-774).
- *Suppliers.*
  - Twisting an eigenform by a Dirichlet character gives an eigenform, of level dividing `Mm²`
    with coefficients `ψ(n)a_n`: Shimura, *Introduction to the arithmetic theory of automorphic
    functions* (1971), §3.6 (Prop. 3.64), Shimura 1973 §4, (4.1) (AUDIT-READ), or Atkin–Li,
    Invent. Math. 48 (1978). The eigenform `g` of C8 is normalized (`a₁ = 1`), so the twist is
    nonzero.
  - Li, *Newforms and functional equations*, Math. Ann. 212 (1975), main theorem (Thm 5; or
    Miyake, *Modular forms*, Thm 4.6.19): strong multiplicity one gives a unique newform `f` with
    the eigenvalues of the twist. "Primitive newform" means a normalized newform in Li's sense,
    not a twist-minimal one in the sense of Atkin–Li; with the twist-minimal reading `r₅` would
    only be a twist of `ρ_f` (rv-h-a9c9 R-C9-3).
  - Galois conjugation preserves newness: every `f^σ` is a newform of level `N` (Shimura 1971,
    Thm 3.52, rationality of the old/new decomposition, with strong multiplicity one; rv-h-a9c9
    R-C9-2). Needed to apply Li's Fricke formula to every conjugate.
  - Shimura, *On the factors of the jacobian variety of a modular function field*, J. Math. Soc.
    Japan 25 (1973), Thm 1: the quotient `A_f` of `J₁(N)` attached to the conjugate span
    `V_f = span{f^σ}`, with its `K_f`-action `θ(T_n) = a_n` (unconditional part, AUDIT-READ).
    Its hypothesis on the span is met whatever its exact form: `V_f` is Hecke-, diamond-,
    `Aut(ℂ)`- and Fricke-stable. The Fricke form (the upstream audit reports it on p. 526) is
    AUDIT-READ, and Li's Fricke formula (p. 296, paragraph before Lemma 6, AUDIT-READ; also
    Atkin–Li 1978 Thm 1.1) gives `f^σ|H_N = γ_σ f^{cσ}` with `γ_σ ≠ 0` for any nebentypus
    (rv-h-a9c9 §2.2 item 2, with a 30-sample numerical check of Li's formula,
    `scratch/rv-h-a9c9/c9_li_fricke.py`). On the `K_f`-linear route below the Fricke condition is
    not needed at all.
  - `r₅` is a constituent of `V₅(A_f)` (rv-h-a9c9 R-C9-1). The Euler-factor identity
    `L(A_f, s) ≐ Π_σ L(f^σ, s)` alone does not give this: divisibility of characteristic
    polynomials at every element does not make a representation a constituent (for
    `G = ℤ/2 × ℤ/2`, `U = ab` and `V = 1 ⊕ a ⊕ b`; rv-h-a9c9 §2.2 item 3,
    `scratch/rv-h-a9c9/c9_charpoly_divisibility.py`). The supplier is the `K_f`-linear
    Eichler–Shimura relation: `V_ℓ(A_f)` is free of rank 2 over `K_f ⊗ ℚ_ℓ` (Shimura 1971 §7;
    Ribet 1977; Diamond–Im 1995 §12.5), and `T_p = Frob_p + p⟨p⟩Frob_p⁻¹` on `J₁(N)` (Shimura
    1971, Thm 7.9; Diamond–Shurman, GTM 228, Thm 8.7.2 and §9.5) gives `tr(Frob_p | V_λ) = a_p`
    over `K_{f,λ}` for `p ∤ Nℓ`. So `V₅(A_f) ⊗ E = ⊕_τ V_τ` over the embeddings `τ: K_f → E`,
    and `V_{ι₅|K_f}` has the Frobenius traces of `r₅` at almost all `p`. Both are semisimple
    (Faltings 1983 Satz 3 for `A_f`; `r₅` is irreducible), so Chebotarev and Brauer–Nesbitt
    (§1 C10) give `r₅ ≅ V_{ι₅}`. (Alternative: the zeta identity, with the existence of every
    `ρ_{f^σ, ι}` and Brauer–Nesbitt, the upstream audit's route.) If the convention gives traces
    `\bar a_p` instead of `a_p`, nothing changes: `\bar f = f^c` is in the orbit. The side is
    right: `V₅(A_f)` and `r₅` (C8's Tate normalization) both have Hodge–Tate weights `{0, −1}`.
  - L774, "this duality preserves the conductor": the Artin / Weil–Deligne conductor of `V^∨`
    equals that of `V` (Serre, *Corps locaux* VI §2; Deligne 1973, §8), uncited in N5 (rv-h-c8
    §6; rv-h-a9c9 R-C9-2, which writes out the argument: the Swan part via the finite wild
    inertia image, the tame part via `N^∨ = −N^t`).
  - Locators UNVERIFIED unless marked AUDIT-READ.
- *Status:* **[R]**. The application is [M]: the part present in 11/4 by Astra "descent"; the
  Li–Shimura sentence (N5 L768-772) is new in N5 and has two model reviews that agree:
  rv-h-trust §2.1 and rv-h-a9c9 §2 (holds after R-C9-1 to R-C9-3, all applied above; R-C9-1
  replaces N5's stated reason, not its conclusion).

**C10. One compatible system at 3 and 5** (N5 L776-795).
- *Content.* The relative Frobenius composed with `μ̄_σ` is an endomorphism of the reduction.
  Its characteristic polynomial is rational and independent of `ℓ`. Then Chebotarev and
  Brauer–Nesbitt.
- *Suppliers.*
  - **I2**, the reduction of `μ_σ`: the Néron mapping property, Bosch–Lütkebohmert–Raynaud,
    *Néron models* (1990), §1.2, Def. 1 and Prop. 8. Locator UNVERIFIED. N5 uses it without a
    citation.
  - The independence of `ℓ`: Mumford 1970, §19, Thm 4 (UNVERIFIED; uncited in N5). Astra's
    descent addendum (item 6) gives Milne's course notes, Prop. 10.20; Mumford is the refereed
    locator.
  - The specialization `V_ℓ(A) ≅ V_ℓ(Ā_v)` at good reduction: Serre–Tate 1968 (UNVERIFIED).
  - Chebotarev: Neukirch, *Algebraic number theory*, VII.13.4. Brauer–Nesbitt: Curtis–Reiner,
    (30.16). Brauer–Nesbitt needs both sides semisimple; on the modular side this is Faltings
    1983 Satz 3 applied to `A_f/ℚ` (already a leaf). Locators UNVERIFIED.
- *Status:* **[M]** (rv-h-novel step 4).

### Part D. Conductor (N5 L796-857)

**D1. Break bound** (N5 L796-812).
- *Content.* `δ ≤ e − 1 + e·v_p(e)`, the Herbrand integral, and `u_last ≤ 2δ/e ≤ 4a²`.
- *Suppliers.*
  - Serre, *Local fields*, III §6 and IV §§1-3. N5 cites Serre in Cassels–Fröhlich, §§4.1-4.3;
    *Corps locaux* is the better locator.
  - The 15 local fields of `scratch/rv-h-novel/c3_breaks.py` (rerun by rv-h-trust: "ALL OK:
    True").
- *Status:* **[M]** (rv-h-novel step 5; Astra "conductor").

**D2. Semistability and wild inertia, odd `p`** (N5 L813-823).
- *Suppliers.*
  - Raynaud's criterion: Silverberg–Zarhin, Ann. Inst. Fourier 45 (1995), Thm 3.5, p. 406,
    `n ≥ 3` (ASTRA-READ: conductor AUDIT), or SGA 7 I, Exp. IX, Prop. 4.7 (UNVERIFIED).
    (Locator audit, 2026-11-12: Thm 3.5 read, but the extracted display could not confirm that
    the printed threshold includes `n = 3`; UNVERIFIED at the boundary, which A6 uses with
    `n = 3`. SGA 7 was not read. Silverberg–Zarhin Thm 3.4 cites the semistable reduction theorem
    as SGA 7 IX **Prop.** 3.6.)
  - Semistable reduction implies unipotent inertia: SGA 7 I, Exp. IX, §3.
  - `G₀ = |GL₄(𝔽₅)|`: `c1_constants.py` (rerun).
- *Status:* **[M]** (rv-h-novel step 6; Astra "conductor").

**D3. The `p = 2` paragraph** (N5 L823-846).
- *Suppliers.*
  - Silverman, AEC (2nd ed. 2009), IV.6.4.
  - The subgroup formula: Serre, *Local fields*, IV §1 Prop. 2 and §3 Prop. 15 (UNVERIFIED).
    It needs `L_v/ℚ₂` Galois.
- *Repairs.* rv-h-novel R2 ("If `e ≤ D`" → "Since `e ≤ D`") and R3 (cite the subgroup formula
  and its Galois hypothesis).
- *Status:* **[M]** (rv-h-novel step 7; Astra "conductor").

**D4. Conductor exponents** (N5 L846-852).
- *Content.* `a_p ≤ 2 + 2U₀ ≤ E₀` at `p ≤ R`. At `R < p ∈ T` the extension is tame and `A` has
  good reduction (A6), so `a_p ≤ 2`. Outside `T`, `a_p = 0`.
- *Supplier.* The Artin–Swan conductor in upper numbering: Serre, *Corps locaux*, VI §2
  (UNVERIFIED).
- *Status:* **[M]** (rv-h-novel step 8). It uses A6, which is [M] (rv-h-b1).

**D5. Level ≤ conductor: I1** (N5 L852-857).
- *Content.* `N ≤ ∏_{p≤R} p^{E₀}·M² ≤ QM²`.
- *Supplier.* Carayol, *Sur les représentations ℓ-adiques associées aux formes modulaires de
  Hilbert*, Ann. Sci. ÉNS 19 (1986), 409-468, Théorème (A). It is applied at `F = ℚ`, weight 2,
  with `λ | 5` for `p ≠ 5` and `λ | 3` for `p = 5`, in the direction "`v_p(N)` = conductor
  exponent". The bibliography entry is already in N5 (`carayol`), but it is not cited in the H
  proof. N5 cites it elsewhere (L9778) with the locator §§0.3-0.7, Théorème A, pp. 409-411, which
  can be imported here.
- *To check (UNVERIFIED).* That Théorème (A) covers `F = ℚ` at every `p ≠ ℓ`, including
  `p | N`; see the statement in §0 of the paper. Fallback: Langlands, *Modular forms and
  ℓ-adic representations*, LNM 349 (1973), together with Carayol's §0 remarks (SPECULATIVE).
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).* §§0.3-0.8 and Théorème A (pp. 409-411) read: it covers
  every finite `p` and every coefficient place of different residue characteristic, so `p | N`
  and `ℓ = 2` are covered; the extra discrete-series hypothesis is only for totally real fields
  of even degree, not `ℚ`. Still to supply: the newform conductor `a(π_p) = v_p(N)` and the
  identification of the chosen realization (contragredient and norm twists do not change the
  conductor). The check above is answered by the audit (AI), not by a human.
- *Status:* **[R]**.

### Part E. Transfer (N5 L860-905)

**E1. An isogeny `A × Z → J₁(N)` over `L'`** (N5 L861-867).
- *Suppliers.*
  - Faltings 1983, Korollar 1 (the Hom theorem), or Satz 4 applied to `A × J`; uncited locator
    in N5; ASTRA-READ (descent AUDIT, pp. 360-361).
  - Poincaré reducibility: Mumford §19, Thm 1.
- *Status:* **[M]** (rv-h-novel step 9). With D2, no GR14 input enters here.

**E2. Height of the Jacobian** (N5 L868-876).
- *Content.* `h_F(J₁(N)) ≤ 1.3·10⁷N¹²`.
- *Supplier.* Javanpeykar, Algebra Number Theory 8 (2014), Thm 1.1.1 (p. 90) and §2.3 (p. 98),
  with the original Faltings metric (ASTRA-READ: height AUDIT, whole REPORT). (Locator audit,
  2026-11-12: read again; `h_Fal(X) ≤ 13·10⁶·g·deg_B(X)⁵` for smooth projective connected `X/ℚ̄`
  of genus `g ≥ 1`, the stable Jacobian height; no field-degree factor.)
- *Status:* **[R]**.

**E3. The explicit isogeny bound** (N5 L878-892).
- *Supplier.* Gaudron–Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), Thm 1.4:
  the exact `κ(A)`, the original stable Faltings normalization, both directions (ASTRA-READ:
  height AUDIT, pp. 2058-2060, 2098, 2101-2102). (Locator audit, 2026-11-12: read in a typeset
  author copy: `α(g) = 1024g³`, `κ(A) = ((14g)^{64g²}[k:ℚ]max(h_F(A), log[k:ℚ], 1)²)^{1024g³}`
  (p. 2058), pair convention (p. 2059), Thm 1.4 (p. 2060); an isogeny in each direction, each of
  degree `≤ κ(A)`, the degree for a pair being the maximum; specialize `k = K`.)
- *Check.* The arithmetic is in `c1_constants.py` (rerun).
- *Status:* **[R]**.

**E4. Height variation, additivity, lower bound** (N5 L893-905).
- *Suppliers.*
  - Faltings 1983, Lemma 5. Alternative: Raynaud, Astérisque 127 (1985), Exp. VII,
    Cor. 2.1.3.
  - Bost's lower bound `h_F ≥ −(3/2)·dim`, through GR14 §9 (ASTRA-READ: height AUDIT).
  - Second locator for all three (task h-v16-adopt, after up-h §3 and §4 item 4):
    Gaudron–Rémond, *Théorème des périodes et degrés minimaux d'isogénies*, Comment. Math.
    Helv. 89 (2014), 343-403, §2.3 (pp. 351-352) and Cor. 8.4 (p. 400). Version 16 cites it for
    Bost's bound `h_F ≥ −log(π√2)·dim > −(3/2)·dim` and for `h_F(A) ≤ h_F(B) + ½·log deg` in
    its five-contact section (V16 L30661-30677); upstream keeps the Duke §9 locator in the
    height section on purpose. Read by upstream's V16 reviewer (a model) only; read by no one
    here. `log(π√2) = 1.4913 < 3/2` (up-h `checks.py` §5).
  - The Faltings and Raynaud locators are UNVERIFIED.
  - Locator audit (2026-11-12): Faltings' Lemma 5 unread (UNVERIFIED; Pazuki's Remark 2.3 points
    to p. 358); Bost's displays unreadable (UNVERIFIED from Bost); Gaudron–Rémond's use of
    `−(3/2)dim A` in the proof of their Lemma 9.1 (p. 2098) read. Conditional on a
    Deligne-normalized bound `h_D ≥ −(g/2)log(2π)`, one gets `h_F ≥ −(g/2)log(2π²) > −(3/2)g`.
- *Status:* **[R]**. The arithmetic is [M] (rv-h-novel step 9) and [S].

### Part F. Back to `u` (N5 L908-964)

**F1. `j` in theta constants** (N5 L908-927).
- *Content.* `j = 3779136·(∏ z_m)⁴/(∑ z_m⁸)⁵`.
- *Suppliers* (rv-up §3.5 item 1).
  - Lin–Yang 2020, arXiv v1 **Example 29** (pp. 20-21; cited as Example 30 before 2026-11-12;
    v1's Example 30 is discriminant 14; journal number UNVERIFIED; locator audit 2026-11-12, see the F1 note
    below): the divisors of `s₂ = ψ₄` and `s₅ = 2¹²3⁵χ₁₀` on the
    quaternionic locus `X`. They make `χ₁₀²/ψ₄⁵` a degree-one function on `X ≅ P¹` with zero at
    P₋₄ and pole at P₋₃. Also eqs. (13)-(14), Igusa's conversion between `ψ₄, ψ₆, χ₁₀, χ₁₂` and
    `J₂…J₁₀`.
  - Lauter–Naehrig–Yang, J. Number Theory (2015), §2.2, and Igusa, *Modular forms and
    projective invariants*, Amer. J. Math. 89 (1967), pp. 833-834 and 848: the theta
    expressions of `ψ₄` and `χ₁₀`.
  - `scratch/h-v14/igusa_check.py` (rerun, identical; again by h-v16-adopt). It derives the
    Igusa vector from Example 29 (formerly cited as Example 30) without eq. (2).
  - The constant at P₋₂₄ is checked without Lin–Yang's `Y′₅` data and without Baba–Granath by
    `scratch/rv-up/endo24.py` and `scratch/rv-up/theta24.py` (both rerun by h-v16-adopt,
    identical). The first shows, exactly, that at the disc −24 Heegner point of `Y′₅` the
    principally polarized surface carries N5's QM datum and that its commutant is `ℤ[√−6]`. The
    second shows that the theta expression equals −16/27 there (to 40 digits).
  - Not used: Lin–Yang eq. (2), cited at N5 L911. Lin–Yang attribute it to Baba–Granath, whose
    Prop. 3.9 rests on Prop. 3.7, whose printed proof has a defect recorded upstream (rv-up
    §3: the separation claim fails at the Weierstrass points, and the product map has degree
    4; the statement itself is not claimed false).
  - Journal locators UNVERIFIED. F1 does not stand on Igusa 1967 and computation alone: the
    global shape of `j_θ` on `X` (its divisor `P₋₄ − P₋₃`) is the Lin–Yang input (rv-up §3.4).
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).* The Lin–Yang locator used in this step (here and in
  `igusa_check.py`'s description) is arXiv:1807.00466v1 **Example 29**, the discriminant-6
  example; "Example 30" is v1's discriminant-14 example. Journal numbering unread. Baba–Granath
  Prop. 3.6 (p. 742) independently prints the invariant tuple. The invariant brackets are
  weighted-projective. Igusa 1967 pp. 833-834, 848 were opened by the audit but the decisive
  signs (`χ₁₀ = −2⁻¹⁴Πθ_m²`) and the `J`-conversion could not be read: UNVERIFIED; the 40-digit
  numerical checks are not a proof of the normalization. The content of F1 is unchanged.
- *Status:* **[R]+[S]**. This replaces `ly-d6` and `igusa-theta` (route B3).

**F2. `h(j) ≤ 40·h([z_m]) + 22`** (N5 L928-932).
- *Content.* Degree 40, with `ℓ¹` norms `3779136` and `10⁵`.
- *Status:* **[M]** (Astra "height").

**F3. Theta height against Faltings height** (N5 L934-947).
- *Supplier.* Pazuki, *Theta height and Faltings height*, Bull. Soc. Math. France 140 (2012),
  Cor. 1.3(2) and §§2.2-2.3, with the `log π` shift for `g = 2` (ASTRA-READ: whole REPORT).
- *Locator audit note (loc-adopt, 2026-11-12; `docs/research/locators.md`, AI agents with web access, not a human review).* Read in arXiv v2 (Cor. 1.3(2), p. 3; Def. 2.1,
  pp. 6-7; Def. 2.6, p. 9; Lemma 5.7, p. 20) and the journal (Cor. 1.3, pp. 21-22; metric p. 26;
  theta height p. 30; Lemma 5.7 p. 43). A consequence, not the literal corollary: the corollary
  compares the truncated heights `max(1,h_Θ)` and `max(1,h_D)` with `min` inside the logarithm,
  `C₂ = 1000r^{2g}(log r^{2g})⁵`. Its metric is Deligne's: `h_D = h_F + (g/2)log π`, i.e.
  `h_D = h_F + log π` for surfaces, so the bound must use `X_D ≥ max(1, h_D)`; for `h_F ≤ X`
  take `X_D = max(1, X + log π)`. N5's bookkeeping `X_D ≤ 3X` and the repository's hardened
  `X_D = max(1, h_F + 3)` (h-decomposition R22) both dominate this; the theta height (the
  paper's Fubini–Study height of the theta embedding) must be identified with the coordinate
  height used in F2.
- *Status:* **[R]**. The normalization bookkeeping (`X_D ≤ 3X`) is [M] (Astra "height").

**F4. From `j` to `u`, and the final constant** (N5 L949-964).
- *Content.* The rational-root theorem gives `h(u) < h(j) + 74`. Then
  `40·10000·2²⁴ + 96 = 6710886400096 < 10¹³` (VERIFIED here). So
  `h(u) ≤ ½H₆(S;R)·M^{24}`, for every admissible `R`.
- *Status:* **[M]** (Astra "height"); the numerics are VERIFIED.

## 2. What remains outside refereed sources

The list is exhaustive relative to §1. Everything not listed here is a refereed theorem cited
in §1 (this includes the eigenform input added to C8 after rv-h-trust §1.2 item 1).

### 2.1 Repository arguments reviewed by models only (no human referee)

1. **N5's own text**:
   - A3, A7, A8 and the centralizer step of A9 (Astra "whole", 11/4 text);
   - B1-B3, C1, C10 and D1-D4 (rv-h-novel on N5, plus Astra);
   - C5, C8 and the 11/4 part of C9 (Astra "descent", 11/4 text; parts of C2 and C5 also in
     rv-h-a011, on Version 14; C8 also in rv-h-c8, on N5);
   - E1 and E4 (rv-h-novel);
   - F2-F4 (Astra "height").

   **Three passages are new in N5** (Astra read the 11/4 text, which lacks them). Each has two
   model reviews that agree:
   - A9, the Milne paragraph (N5 L564-570): rv-h-trust §2.1 and rv-h-a9c9 §1 (holds as stated;
     repairs R-A9-1, R-A9-2, citation-level);
   - C9, the Li–Shimura sentence (N5 L768-772): rv-h-trust §2.1 and rv-h-a9c9 §2 (holds after
     R-C9-1 to R-C9-3; R-C9-1 replaces the Euler-factor inference by the `K_f`-linear
     Eichler–Shimura relation);
   - C3's Lemma `lem:de-rham-descent` (N5 L734-737 and L10938-11000): rv-h-trust §2.1 and
     rv-h-c3 (holds as stated; repairs R1-R3, wording and citations).

   So every passage new in the 11/5 text has two model reviews (with C8 below). These remain
   model reviews, not human refereeing.

   **C8** (twist and weight) has two model reviews: Astra's of the 11/4 text, which did not name
   the eigenform input, and rv-h-c8 on N5, which names it and finds that C8 holds after its
   repairs R1-R3 (normalization of `ρ_g`, weight one, levels divisible by 5), applied in §1 C8.
   Its finiteness step is now Version 14's determinant argument (V16 L660-667), not N5's
   local-algebraicity sentence; that argument was checked by rv-up §2.3 and up-h §4.
2. **NoCM** (A10): h-cm with the review rv-h-cm, after its repairs R1-R5.
3. **The hypothesis check for Pan** (C7): Astra "descent" and "whole" on text identical to N5,
   and h-a011 with the review rv-h-a011, written for Version 14 and transferred to N5 in §1 C7.
4. **Lemma PR** (A5, A6): h-b1's Prop. TS, Lemma NV, the M1-M10 bookkeeping and the reproof of
   Morita, with the review rv-h-b1 (holds as stated). Conditions: rv-h-b1's repairs 1-6, all
   applied in h-b1 (its changelog). N5's own integral-model route (Astra "whole") is a second
   model-reviewed route (§1 A5, Fallback).
5. **The moduli identification** (A4): N5's `Y₃` as the fine moduli scheme over `ℚ`, holding
   (STANDARD) by rv-h-b1 §7 once its four citations are explicit; they are written out in h-b1
   §4A, including the statement that Lemma NV, Lemma PR(ii) and Baba–Granath's `j` use one
   `ℚ`-structure. Polarization uniqueness: §1 A4 input 2.

### 2.2 Repository arguments with no independent review

None, after rv-h-b1 and rv-h-trust. C3's lemma now has a second model review (rv-h-c3), A9's
Milne paragraph and C9's Li–Shimura sentence one each (rv-h-a9c9), and C8 a review on the N5
text (rv-h-c8).

### 2.3 Repository scripts (exact computations)

| Script | Output | Used in | Rerun |
| --- | --- | --- | --- |
| `scratch/h-v14/form_check.py` | `form_check.output.txt` | A1, A3 | identical (h-trust, rv-h-trust) |
| `scratch/h-v14/igusa_check.py` | `igusa_check.output.txt` | A7, F1 | identical (h-trust, rv-h-trust, h-v16-adopt) |
| `scratch/rv-up/endo24.py`, `theta24.py` | `endo24.output.txt`, `theta24.output.txt` | A2, F1 (P₋₂₄: QM datum, commutant `ℤ[√−6]`, `j_θ = −16/27`) | identical (h-v16-adopt) |
| `scratch/h-b1/b1_checks.py` | `b1_checks.output.txt` | A3, A5 | identical (h-trust, rv-h-b1, rv-h-trust) |
| `scratch/rv-h-b1/rv_checks.py` | `rv_checks.output.txt` | A4, A5 (R1 form, R2 elliptic enumeration, R6 neatness) | identical (h-b1-fix) |
| `scratch/h-map/beckmann_check.py`, `o3_units.py` | `.output.txt` | A5, A3 | not rerun (subsumed by `b1_checks.py`) |
| `scratch/rv-h-cm/check.py` | `check.output.txt` | A10 | identical (h-trust, rv-h-trust) |
| `scratch/rv-h-novel/c1_constants.py` | none committed; rerun saved in `scratch/h-trust/reruns/` | B3, D2, E3, E4 | agrees with rv-h-novel's log; identical in rv-h-trust |
| `scratch/rv-h-novel/c2_sqrt_criterion.py` | as above | B2 | agrees (135 characters, 0 mismatches) |
| `scratch/rv-h-novel/c3_breaks.py` | none committed | D1, D3 | "ALL OK: True" on 15 local Galois extensions (rv-h-trust) |
| `scratch/rv-h-trust/branch_check.py` | `branch_check.output.txt` | A5, A7 (`J(u)` not a branch value) | written and run by rv-h-trust |

That is the nine scripts of the original eight rows, plus `rv_checks.py`, `branch_check.py`
and rv-up's `endo24.py` and `theta24.py`.

### 2.4 Unrefereed editions cited by N5, with refereed replacements (citation swaps only)

| N5 key | Used at | Replacement | Statement change |
| --- | --- | --- | --- |
| `milne-av` (course notes v2.00, 2008) | A9 (L564, Part I Thms 2.8-2.9), C3 (L10968, Part I Thm 12.1(a)) | Mumford, *Abelian varieties* (1970), §§1-3 with GAGA (A9), §§19-20 (C3); Milne in Cornell–Silverman (1986), §1 (A9), §15 (C3) | none; the bibliography entry (N5 L11024-11026) names only Thm 12.1(a), so the A9 locator must be added there (rv-h-a9c9 R-A9-1) |
| `brinon-conrad` (CMI notes, 2009) | C3 | Fontaine, *Représentations p-adiques semi-stables*, Astérisque 223 (1994), 113-184, Thm 3.8, p. 142 (V16's citation; content UNVERIFIED) | none |
| `babagranath` (MPI preprint, 2005) | A2, A7 | Canad. J. Math. 60 (2008) | numbering to compare; the "local index slip" of Lemma 3.1 is not used (A3 is proved in N5) |
| `linyang` (arXiv v1, 2018) | A1, A2, A7, F1 | Math. Z. 295 (2020) | equation and example numbers to compare |
| `buzzard` (author version, 2002) | N5 L444 | deleted by B1 | — |

The row `conrad-local-characters` (preprint, 2011; C8, replacement Serre 1968 Ch. III or Tate
1967 §3.3) is gone: C8's determinant argument (task h-v16-adopt, V16 L660-667) no longer uses
local algebraicity of Hodge–Tate characters.

### 2.5 Locators not read, and where to check them

Every published locator in §1 is UNVERIFIED unless §1 says it was read. Read in arXiv, in this
repository: Pan v2 Thm 1.0.4, Berger v3 Thm 0.6/5.19, González–Rotger §5, Lin–Yang v1 Ex. 29 (formerly cited as Ex. 30) and
eqs. (2), (13), (14) (eq. (2) read but not used; see F1), and Scholze's introduction.

*Locator audit (2026-11-12, `docs/research/locators.md`).* AI agents with web access read the
primary texts of: Baba–Granath (journal), Lin–Yang arXiv v1 (the discriminant-6 example is
**Example 29**, not 30), González–Rotger (arXiv v1, v2, journal; Prop. 5.6 has the orientation
factor), Silverberg–Zarhin (`m = 3` boundary unreadable), Scholze (v2, journal, corrigendum),
Berger (v3 and published), Pan v2 (JAMS number still unread), Kato 2004, Deligne exp. 355,
Deligne–Serre, Shimura 1973, Carayol (covers `p | N`, `ℓ = 2`), Javanpeykar, Gaudron–Rémond,
Pazuki (Deligne metric, `+log π`), Chia-Fu Yu 2013 (QM dichotomy). They could not read:
Shimura 1967, Kottwitz 1992, Serre–Tate 1968, Faltings 1983 (only the erratum), SGA 7, Igusa's
decisive displays, Saito 1997, Shimura 1971, Bost's displays, Lin–Yang's journal body, Pan's
JAMS text. Item 1 below stays open (Pan's JAMS text unread). Items 2 (Carayol), 3 (the Kato
option and Deligne–Serre), 4 (Shimura 1973 Thm 1) and the Baba–Granath half of 10 are answered by
the audit as far as stated in the notes of §1; they stay listed because no human has read them.

**ASTRA-READ** (a model opened the primary source; rv-h-trust §4 item 2). These are not
UNVERIFIED in the sense above, but no human has read them:

| Source | Places read | Astra record |
| --- | --- | --- |
| Faltings 1983 | Satz 3, Satz 4, Kor. 1, pp. 360-361 | descent/AUDIT |
| Silverberg–Zarhin | Thm 3.5, p. 406, `n ≥ 3` | conductor/AUDIT |
| Berger | Thm 0.7 / Cor. 5.22 (published), Thm 0.6 / 5.19 (arXiv v3) | descent/ADDENDUM |
| Javanpeykar | Thm 1.1.1, p. 90; §2.3, p. 98; original Faltings metric | height/AUDIT, whole/REPORT |
| GR14 | Thm 1.4 (exact `κ(A)`, original stable Faltings normalization, both directions); §9 (Bost's `−3 dim/2`); pp. 2058-2060, 2098, 2101-2102 | height/AUDIT |
| Pazuki | §2.3, Cor. 1.3(2), the `log π` shift for `g = 2` | whole/REPORT |
| Baba–Granath (MPI preprint) | §2.1 Thm 1, §3.2 | whole/REPORT |
| Pan | arXiv v2 | descent/AUDIT, whole/REPORT |
| Milne ADT | Ch. I | descent/AUDIT, whole/REPORT |
| Buzzard (N5's fallback route for A5-A6 only) | Thm 2.1, Cor. 2.3 | whole/REPORT |

**AUDIT-READ** (the upstream theorem-application audit reports reading the page scan; recorded
by rv-h-a9c9, which had no copy): Milne's course notes, Part I Thms 2.8-2.9, printed p. 14 (A9;
`parallel-geometry-report.md`); Shimura 1973, Thm 1, p. 526 (the Fricke hypothesis and the
`K_f`-action) and §4, (4.1), p. 531 (twists) (C9; `parallel-galois-height-report.md`); Li 1975,
p. 296, paragraph before Lemma 6 (the Fricke formula) (C9;
`parallel-geometry-a011-fricke-review.md`). No one in this repository has read these places.

**UNVERIFIED** checks, in order of weight:

1. **Pan, JAMS 35 (2022)**: that Theorem 1.0.4 is numbered and worded as in arXiv v2 (the arXiv
   text is ASTRA-READ; the JAMS text has been read by no one). Check the AMS text,
   pp. 1031-1040.
2. **Carayol 1986, Théorème (A)**: its coverage of `F = ℚ`, weight 2, every `p ≠ ℓ`. Check the
   statement in §0 of the paper (Numdam ASENS_1986_4_19_3_409_0); N5 L9778 already gives
   §§0.3-0.7, pp. 409-411.
3. **The C8 supplier** (HT): Saito, Invent. Math. 129 (1997), or Scholl, Invent. Math. 100
   (1990) with Scholze 2013 Cor. 1.8: that the `p`-adic representation of a weight-`k` eigenform
   is Hodge–Tate with weights `{0, 1−k}` (Tate-module normalization), **at every level,
   including `p | N`** (rv-h-c8 R3). Faltings, Math. Ann. 278 (1987): whether it covers `p | N`.
   Scholl with Faltings 1989 covers only `p ∤ N`, and Scholl with Tsuji 1999 needs de Jong 1996.
   For `k = 1`: Deligne–Serre 1974, Thm 4.1 (rv-h-c8 R2). Third all-levels option (from
   Version 14 on, V16 L618-650): Kato, Astérisque 295 (2004), §9.4, p. 188, with §6.3,
   §§5.4, 8.3 and (14.10.2)-(14.10.3), p. 240; check that §9.4's filtration statement covers
   `5 | N`, as V16 L630-632 asserts.
4. **Shimura 1973, Thm 1** (C9): its hypothesis on the span. No longer decisive (rv-h-a9c9
   §2.2): the conjugate span meets it whatever its exact form (Hecke, `Aut(ℂ)` or Fricke
   stability); the Fricke form, p. 526, is AUDIT-READ; and the `K_f`-linear Eichler–Shimura route
   of §1 C9 does not need it. Check p. 526 to turn AUDIT-READ into a read locator.
5. **SGA 1 X 3.1, XIII 5.3; SGA 7 IX 3.6, IX 4.7**, and **Serre–Tate 1968, Thms 1-2**: for
   Lemma PR. These are classical, and the numbering is the risk.
6. **Deligne 1971 (Bourbaki 389) §3, Prop. 1.15, Thm 4.7, §§4.8-4.17, Thm 4.21, Cor. 5.7,
   Ex. 5.8; Deligne 1979 §2.7, §5, 2.2.5, 2.3.1; Shimura 1967; Kottwitz 1992 §§5,
   8; Rotger 2003/2004; Mumford §21**: reciprocity, the Hecke action, the moduli
   interpretation and its four inputs (A3-A5; h-b1 §4A).
7. **Faltings 1983**: Lemma 5 (§5), and the 1984 erratum (that it touches none of Satz 3, Satz 4,
   Korollar 1, Lemma 5).
8. **Scholze, Forum Math. Pi 1 (2013), Cor. 1.8 and Thms 9.1, 9.3**, and the corrigendum (C3,
   and C8 on the Scholl route).
9. **Li 1975** (main theorem, Thm 5; p. 296, AUDIT-READ); **Shimura 1971 §3.6 / Atkin–Li 1978**
   (twists of eigenforms); **Shimura 1971 Thm 3.52, §7 and Thm 7.9, Ribet 1977, Diamond–Im 1995
   §12.5, Diamond–Shurman Thm 8.7.2** (newness Galois-stable; the `K_f`-linear Eichler–Shimura
   relation, C9); **Mumford §§1-3, Serre GAGA, Milne 1986 §1, Conrad 2006 §3** (A9).
10. **Baba–Granath 2008** and **Lin–Yang 2020**: compare the journal numbering with the preprint
    numbering N5 uses.
11. **Vignéras LNM 800** (local normalizers, embedding condition); **Reiner** (Skolem–Noether);
    **Mumford §19** (Thms 1, 3, 4); **BLR §1.2**; **Serre, *Local fields* III §6, IV §§1-3**,
    and ***Corps locaux* VI §2** (upper-numbering conductor, D4); **Fontaine, Astérisque 223,
    pp. 113-184, Thm 3.8, p. 142** (C3); **Washington 1997, Thm 14.1, p. 321** (Kronecker–Weber,
    C8); **Mumford §§20, 23** (Weil pairing, C8); **CMH 2014 §2.3, Cor. 8.4** (E4, second
    locator, read by upstream's V16 reviewer only); **Tate in Cassels–Fröhlich Ch. VII**.

### 2.6 Policy items (not gaps)

- **Inside Pan.** Pan's proof cites Skinner–Wiles, Kisin, Hu–Tan and Khare–Wintenberger
  (rv-h-a011 F2). The leaf is the stated theorem.
- **Inside Berger.** Berger's theorem rests on André, Kedlaya and Mebkhout (rv-h-a011 F3). All
  are refereed. This is not a residual.
- **Conventions.** Hodge–Tate sign, Frobenius and reciprocity normalizations were checked to be
  immaterial (rv-h-a011 §2; h-b1 §6 item 3). The normalization of the eigenform representation in
  C8 changes only the twisting character, not the conclusion (rv-h-c8 §5), once C8 fixes it.
- **Height normalizations.** Javanpeykar and GR14 both use the original stable Faltings height
  (ASTRA-READ); Pazuki's Deligne normalization is handled explicitly by `X_D` (N5 L939-941); and
  rv-h-novel step 9 shows that `O(g)` shifts are absorbed. No residual (rv-h-trust §4 item 7).
- **Vestigial constant.** `C_cm` stays in `H₆` after NoCM deletes the CM branch; the max only
  weakens the bound.

### 2.7 Residual list in one line each

Outside refereed sources, H rests on:

- (i) N5's novel arguments and bookkeeping (§2.1 item 1), reviewed by models only;
- (ii) NoCM (model-reviewed, rv-h-cm);
- (iii) Lemma PR and the moduli identification (model review rv-h-b1; citations per rv-h-b1 §7,
  written out in h-b1 §4A);
- (iv) nine exact scripts (§2.3), plus `rv-h-b1/rv_checks.py`, `rv-h-trust/branch_check.py`,
  `rv-up/endo24.py` and `rv-up/theta24.py`;
- (v) four citation swaps (§2.4; the fifth, Conrad's preprint, is no longer needed);
- (vi) the locator checks of §2.5 (the ASTRA-READ ones read by a model only);
- (vii) closed (task h-a9c9-fix): no N5 passage has a single model review. A9's Milne paragraph
  and C9's Li–Shimura sentence (rv-h-trust, rv-h-a9c9), C3's lemma (rv-h-trust, rv-h-c3) and C8
  (Astra on 11/4, rv-h-c8 on N5) each have two model reviews, with their repairs applied in §1.
  They stay in item (i): model reviews, not human refereeing.

No unpublished upstream proof supplement is used.

## 3. Docstrings and KERNEL_PLAN row (repaired; applied by task h-adopt)

These are the drafts as repaired after rv-h-trust §5 (items 1-5, the HeightMin paragraph and the
KERNEL_PLAN row). Task h-adopt applied them verbatim to the Lean files and to KERNEL_PLAN.md; the
definitions, statements, proofs and numerals are unchanged. Task h-c38 updated three items in the
drafts, the Lean docstring and the row alike, after rv-h-c3 and rv-h-c8: the C8 supplier (its
normalization, all levels, Deligne–Serre for weight one), the review count of the twist and weight
step, and that of the de Rham descent lemma. The `HeightMin.lean` texts needed no change. Task
h-a9c9-fix updated, after rv-h-a9c9, the review count of the other two passages new in the 11/5
text, the newform suppliers (the Eichler–Shimura relation, Shimura 1971) and GAGA, in the drafts,
the Lean docstring and the row alike; `HeightMin.lean` again needed no change. Task h-v16-adopt
added Kato 2004 to the C8 supplier and changed "Five citations" to "Four" (Conrad's preprint is
no longer cited), in the drafts, the Lean docstring and the row alike. Baba–Granath and Lin–Yang
stay named, since A2, A7 and F1 still use them (not Baba–Granath Props 3.7-3.10, not Lin–Yang
eq. (2)); `HeightMin.lean` again needed no change.

**`ZInQKernel/Hypotheses/Height.lean`**: the module docstring and the docstring of
`SixContactEstimate`.

```lean
/-!
# Hypothesis H: the six-contact height estimate

`SixContactEstimate` is Theorem 4.1 (`thm:height`) of the frozen 11/5 manuscript
`diophantine_zq.tex` (sha256 `cb1148cd…`), with the manuscript's numerals. The statement
concerns only rational numbers, but its proof needs Shimura curves, modularity and Arakelov
geometry, none of which is in Mathlib. It therefore enters the main theorems as an explicit
hypothesis, through its one used instance `SixContactMin` (`Hypotheses/HeightMin.lean`).

## Trust statement

The proof uses no unpublished upstream proof supplement. `docs/research/h-trust.md` §1 lists
every step with its supplier and status (review: `docs/research/rv-h-trust.md`). It rests
principally on the following.

* **Refereed theorems.**
  - The discriminant-six Shimura curve: its canonical model and moduli interpretation (Shimura
    1967; Deligne 1971, 1979; Kottwitz 1992), its branch data and Igusa coordinates
    (Baba–Granath 2008; Lin–Yang 2020; Igusa 1967; Lauter–Naehrig–Yang 2015), and its CM points
    (González–Rotger 2006).
  - Abelian varieties: Mumford's book (1970) with GAGA, Skolem–Noether, and the Brauer group of `ℚ`
    (Milne's *Arithmetic duality theorems*; Tate in Cassels–Fröhlich).
  - Reduction: tame specialization (SGA 1, Exp. X, XIII), semistable reduction (SGA 7, Exp. IX),
    and Néron–Ogg–Shafarevich (Serre–Tate 1968).
  - Galois representations: Faltings' finiteness theorems (1983); Scholze's de Rham comparison
    (2013, with its 2016 corrigendum); Berger's p-adic monodromy theorem (2002); Pan's
    Fontaine–Mazur theorem (J. Amer. Math. Soc. 35 (2022), Theorem 1.0.4 of
    arXiv:1901.07166v2); the p-adic Hodge theory of modular forms, in the Tate-module
    (arithmetic-Frobenius) normalization with weights `{0, 1−k}`, at every level including
    levels divisible by 5 (Saito 1997, Scholl 1990 with Scholze 2013, or Kato 2004), and
    Deligne–Serre 1974 for weight one; Li 1975, Shimura 1973 and the Eichler–Shimura relation
    (Shimura 1971) for newforms and `A_f`; Carayol's local–global compatibility (1986,
    Théorème A).
  - Local fields: local class field theory and ramification (Serre), and Raynaud's criterion
    (Silverberg–Zarhin 1995).
  - Heights: Javanpeykar 2014, the isogeny theorem of Gaudron–Rémond (2014, Theorem 1.4),
    Faltings' height variation, and Pazuki 2012.
  - Four citations of the manuscript to lecture notes or preprints are replaced by refereed
    editions (`docs/research/h-trust.md` §2.4).
* **Manuscript arguments reviewed by models only, never by a human referee.**
  - The scalar descent, the uniform conductor bound `N ≤ Q_R M²` and the transfer from
    `J₁(N)`: `docs/research/rv-h-novel.md`, plus four scoped Astra reviews of the 11/4 text
    (`docs/reviews/height-replacement/`).
  - The geometric bookkeeping: the level-three degree and the conjugates, the Hom field and the
    endomorphism dichotomy (Astra "whole").
  - Oddness (Astra "descent", on the 11/4 text), and the twist and weight argument (Astra
    "descent" on the 11/4 text and `docs/research/rv-h-c8.md` on the 11/5 text).
  - The theta-height comparison and the return to `u` (Astra "height").
  - The application of Pan's theorem: Astra "descent" and "whole" on the manuscript's text, and
    `docs/research/rv-h-a011.md`.
  - Three passages are new in the 11/5 text, and each has two independent model reviews: the
    de Rham descent lemma (`lem:de-rham-descent`; `docs/research/rv-h-trust.md` and
    `docs/research/rv-h-c3.md`), and the paragraph on Hodge endomorphisms in the dichotomy and
    the Li–Shimura sentence on the newform (`rv-h-trust.md` and `docs/research/rv-h-a9c9.md`).
* **Repository arguments that replace manuscript text.**
  - The CM branch is empty for rational `u` (`docs/research/h-cm.md`; model review
    `rv-h-cm.md`).
  - The fibre field is unramified outside `S ∪ supp M_S(u)`, and the fibre surface has good
    reduction away from 3. Both come from tame specialization and a vertical-ramification
    lemma, with no integral model of the Shimura curve (`docs/research/h-b1.md`, Lemma PR;
    model review `docs/research/rv-h-b1.md`: holds, and its repairs are bookkeeping). It uses
    the canonical model of the level-three curve as the PEL moduli scheme over `ℚ`, with one
    `ℚ`-structure for the vertical-ramification lemma, the good-reduction step and
    Baba–Granath's `j` (h-b1 §4A).
* **Exact computations** in `scratch/`, each with its saved output: the polarization form, the
  Igusa normalization, the ramification case analysis, the branch values and the constants.

None of the replacements changes the constant `H₆` or the exponent 24. Published locators
that could not be read when the trust statement was written are listed in
`docs/research/h-trust.md` §2.5; those read by a model only are marked ASTRA-READ there.
-/
```

```lean
/-- **Hypothesis H** (Theorem 4.1, the six-contact estimate). For every finite set `S` of
primes containing all primes at most `324`, every `R ≥ max(D, max S, 10¹²)` and every
`u ∈ ℚ \ 𝒞`, `h(u) ≤ H₆(S; R) M_S(u)²⁴`.

Not proved in Lean. Its proof rests on refereed theorems, together with manuscript and
repository arguments that have been reviewed by models but not refereed, and uses no
unpublished upstream proof supplement. See the module docstring and
`docs/research/h-trust.md`. The main theorems use only the instance `SixContactMin`. -/
```

**`ZInQKernel/Hypotheses/HeightMin.lean`**: keep the module docstring and append one paragraph;
replace the docstring of `SixContactMin`.

```lean
/-!
(… existing text unchanged …)

## Trust

`SixContactMin` is not proved in Lean. It is the instance `S = S_mul`, `R = D` of
`SixContactEstimate`, and `sixContactMin_of_sixContactEstimate` (`ZInQKernel/Main.lean`) derives
it in Lean. Its justification is therefore exactly that of Theorem 4.1, recorded in the module
docstring of `Hypotheses/Height.lean` and in `docs/research/h-trust.md`. The instance is
admissible because `S_mul` consists of primes, contains the primes `≤ 324`, `max S_mul ≤ D`, and
`10¹² ≤ D`; the proof of Theorem 4.1 uses `R` only through these lower bounds. H cannot be
narrowed further or removed (`docs/research/h-map.md` §§1, 3.1, 3.3): the two consumers need a
bound that is effective and uniform in `u`.
-/
```

```lean
/-- **Hypothesis H, minimal form.** For every `u ∈ ℚ \ 𝒞`, `h(u) ≤ H₆(D) · M_{S_mul}(u)²⁴`, where
`H₆(D) = A⁽⁰⁾_ht = 2·10¹³ max(1, C_cm, (D^(D E₀))¹⁷)`. This is the instance `S = S_mul`, `R = D`
of the six-contact estimate `SixContactEstimate`. It is the only form of H that the main theorems
assume. Its trust statement is that of Theorem 4.1: refereed theorems plus model-reviewed
arguments, with no unpublished upstream proof supplement (`Hypotheses/Height.lean`,
`docs/research/h-trust.md`). -/
```

**H row of the dependency table in KERNEL_PLAN.md** (T3 success criterion: the row names no
supplement as an input):

| H (Theorem 4.1) | refereed theorems (Shimura curve: Shimura, Deligne, Kottwitz, Baba–Granath, Lin–Yang, González–Rotger; SGA 1, SGA 7, Serre–Tate; Faltings 1983; Scholze; Berger; Pan's Theorem 1.0.4; p-adic Hodge theory of modular forms in the Tate-module normalization, at every level (Saito 1997, Scholl 1990 with Scholze, or Kato 2004), with Deligne–Serre 1974 for weight one; Li, Shimura 1973, Eichler–Shimura (Shimura 1971); Carayol; Serre's local fields; Silverberg–Zarhin; Javanpeykar; Gaudron–Rémond; Pazuki; Igusa), plus the manuscript's descent, conductor and transfer arguments (model reviews only: [rv-h-novel](docs/research/rv-h-novel.md), Astra), the manuscript's geometric, twist and theta-height bookkeeping (Astra; the twist and weight step also [rv-h-c8](docs/research/rv-h-c8.md); of three passages new in the 11/5 text, the de Rham lemma reviewed in [rv-h-trust](docs/research/rv-h-trust.md) and [rv-h-c3](docs/research/rv-h-c3.md), the other two in rv-h-trust and [rv-h-a9c9](docs/research/rv-h-a9c9.md)), NoCM ([h-cm](docs/research/h-cm.md), [rv-h-cm](docs/research/rv-h-cm.md)), and Lemma PR in place of the integral model ([h-b1](docs/research/h-b1.md); model review [rv-h-b1](docs/research/rv-h-b1.md)). No unpublished upstream proof supplement. Outline: [docs/research/h-trust.md](docs/research/h-trust.md) |

## 4. Next step

The review this section asked for is done: `docs/research/rv-h-trust.md` (this outline) and
`docs/research/rv-h-b1.md` (h-b1). Of its four checks:

- (1) line coverage, (2) the transfer of the Pan hypothesis check to N5 (C7) and (4) the moduli
  identification A4 are done (rv-h-trust §§1.1, 2.2; rv-h-b1 §7);
- (3) C8 is done, except that its new supplier (the p-adic Hodge theory of the eigenform, §1 C8)
  is a locator still to read. rv-h-c8 has since reviewed C8 on the N5 text (repairs R1-R3
  applied in §1 C8).

What remains are the network checks of §2.5. The most important are Pan's JAMS text,
Carayol's Théorème A at `F = ℚ`, the C8 supplier, and the hypothesis of Shimura 1973 Thm 1.
They decide whether any statement must change; the rest decide numbering only (SPECULATIVE).
(Shimura 1973 has since dropped out of this group: see the end of this section.)
For the C8 supplier the check is at `p | N`: Saito 1997 (or Scholl 1990 with Scholze's Cor. 1.8,
or Kato 2004 §9.4), and Deligne–Serre 1974 Thm 4.1 for weight one. For C3, read Fontaine's
Thm 3.8 (Astérisque 223, p. 142); the exposé question of rv-h-c3 R2 is settled by V16's
citation (pp. 113-184). The second model reviews of the three N5-only passages are done
(rv-h-c3 for C3's lemma; rv-h-a9c9 for A9's Milne paragraph and C9's Li–Shimura sentence).
Since rv-h-a9c9, the hypothesis of Shimura 1973 Thm 1 no longer decides any statement: the
conjugate span meets it in any form, and the `K_f`-linear Eichler–Shimura route of §1 C9 avoids
it. Reading Shimura 1973 p. 526 and Li 1975 p. 296 would turn their AUDIT-READ marks into read
locators; Shimura 1971 Thm 7.9 and §7 are the locators of the route actually used.

## Changelog

Task h-adopt (2026-11-11), applying `docs/research/rv-h-trust.md` §6. Bookkeeping and citations
only: no argument and no constant changes, and no unpublished supplement becomes an input.

1. **Header and marks.** h-b1 (with rv-h-b1, repairs applied) and rv-h-novel are cited on main;
   rv-h-trust added as a source. New mark ASTRA-READ; UNVERIFIED now means read by no one. The
   status rule says statuses are local and downstream steps inherit (O12).
2. **Summary (S1-S4).** Counts 7 / 5 / 24 / 0 unchecked; A4-A6 model-reviewed (rv-h-b1); D1's
   reason qualified (rv-h-trust §3) with the Fontaine / Faltings / Tsuji fallback; nine scripts
   plus `rv_checks.py`; rv-h-novel step 4 line range (L797-818 → L776-795).
3. **Outline (O1-O11).** A1: polarization uniqueness needed in A4. A2: Baba–Granath preprint
   ASTRA-READ. A3: rv-h-b1 status; N5 prints `≤ 81`. A4: [M] (rv-h-b1 §7), its four inputs and
   the elementary uniqueness proof (O1). A5, A6: [M] (rv-h-b1); `J(u)` not a branch value
   (`branch_check.py`); N5's integral-model route as a fallback (O2). A9: Milne paragraph
   reviewed only by rv-h-trust (O3). B2: Milne ADT ASTRA-READ. C2, E1: Faltings Satz 3 / Satz 4
   / Korollar 1 (ASTRA-READ), Korollar 1 for Hom (O11); erratum check. C3: "[M] (rv-h-trust
   only)" (O4). C4: Berger Thm 0.7 / Cor. 5.22 published (O5). C6, D4: inheritance wording. C7:
   Astra descent and whole as the N5-direct check (O6). C8: the eigenform supplier (Faltings
   1987; Scholl 1990 with Faltings 1989 or Tsuji 1999; Saito 1997) (O7). C9: twists of
   eigenforms, Li's newform theorem, Shimura's hypothesis; Li–Shimura sentence rv-h-trust only
   (O8). C10: Faltings Satz 3 for semisimplicity, Serre–Tate specialization, Milne Prop. 10.20
   noted (O9). D1: c3_breaks rerun. D2, E2-E4, F3: ASTRA-READ locators. D4: *Corps locaux* VI §2;
   D5: N5's own Carayol locator (L9778) (O10).
4. **Residuals (R1-R6).** §2.1 gains Lemma PR, A4 and the three N5-only passages; §2.2 is empty;
   §2.3 adds `rv_checks.py`, `branch_check.py` and the c3_breaks rerun; §2.5 splits ASTRA-READ
   from UNVERIFIED and adds the C8 supplier, Shimura 1973's hypothesis and the A4 inputs; §2.6
   adds height normalizations and the vestigial `C_cm`; §2.7 updated, with item (vii).
5. **Drafts (D1-D3).** §3 repaired per rv-h-trust §5 and applied to `Hypotheses/Height.lean`,
   `Hypotheses/HeightMin.lean` and KERNEL_PLAN.md.
6. **Next step (N1-N3).** §4 rewritten.

Task h-c38 (2026-11-11), applying `docs/research/rv-h-c3.md` R1-R3 and
`docs/research/rv-h-c8.md` R1-R3 (with R4-R5 where they are bookkeeping). Wording, citations and
review counts only: no argument, constant or Lean statement changes.

1. **Header, marks, Summary.** rv-h-c3 and rv-h-c8 added as sources; C3's lemma now has two
   model reviews (Summary items 1 and 3, D1); rv-h-c3's citation-only pst route noted under D1;
   route table row L719-795 names the C8 normalization, all levels and Deligne–Serre.
2. **C3.** rv-h-c3 R1 (the restriction step "de Rham over `F` ⇒ over `F'`"), R2 (Milne's notes →
   Mumford §§19-20 / Milne 1986 §15; Brinon–Conrad → Fontaine, Astérisque 223, with the
   "Exp. VIII" locator flagged as suspect; Faltings 1989 / Tsuji 1999 as fallback for Scholze),
   R3 (pointer to C8); the shorter route of rv-h-c3 §3.2. Status: "[M] (rv-h-trust, rv-h-c3: two
   independent model reviews)". C7: C3's hypothesis also covered by rv-h-c3 §3.3.
3. **C8.** rv-h-c8 R1 = rv-h-c3 R3: `ρ_g` fixed in the Tate-module (arithmetic-Frobenius)
   normalization, `det ρ_g = ε_g χ^{k−1}`, weights `{0, 1−k}`; in Pan's geometric normalization
   the weights are `{0, k−1}` and the twist is `χ¹`, with the same conclusion for `k = 2`.
   Supplier stated as (HT), Hodge–Tate sufficing. R2: Deligne–Serre 1974, Thm 4.1 for `k = 1`.
   R3: the supplier must cover `5 | N`; Saito 1997, or Scholl 1990 with Scholze 2013 Cor. 1.8,
   named for all levels; Scholl with Faltings 1989 only for `5 ∤ N`, with Tsuji 1999 only with de
   Jong 1996; Faltings 1987's level coverage UNVERIFIED. R4: the two elementary uncited steps
   (in C8) and "duality preserves the conductor" (in C9). R5: status "[M] (Astra on 11/4,
   rv-h-c8 on N5: two model reviews)", supplier [R] with the corrections.
4. **Residuals.** §2.1: C3 and C8 each have two model reviews; the single-review N5 passages are
   A9's and C9's. §2.2 note updated. §2.4: Milne 1986 §15, the Fontaine exposé flag, Tate 1967.
   §2.5 item 3 (C8 supplier at `p | N`, Deligne–Serre), item 8 (Scholze also for C8), item 11.
   §2.6 conventions: C8's normalization. §2.7 (vii) updated.
5. **Drafts and Lean comments.** §3 and the module docstring of `Hypotheses/Height.lean`: the C8
   supplier with its normalization, all levels and Deligne–Serre; the review counts of the twist
   and weight step and of the de Rham lemma. Same in the H row of KERNEL_PLAN.md.
   `HeightMin.lean` unchanged.
6. **Next step.** §4: C3's second review done; the C8 locator check is at `p | N`; Fontaine's
   exposé numbers.

Task h-a9c9-fix (2026-11-11), applying `docs/research/rv-h-a9c9.md` §§1.4, 2.4 and 4 (repairs
R-A9-1, R-A9-2, R-C9-1 to R-C9-3). Citations, the stated reason in C9, and review counts only:
no constant, status or Lean statement changes.

1. **Header, marks, Summary.** rv-h-a9c9 added as a source; new mark AUDIT-READ (the upstream
   theorem-application audit's reading, recorded by rv-h-a9c9); the [M] definition and Summary
   item 1 name rv-h-a9c9 as the second review of A9's and C9's N5-only passages; item 4(f)
   mentions the AUDIT-READ locators; the route-table row L719-795 names the `K_f`-linear
   Eichler–Shimura relation.
2. **A9.** R-A9-1: Riemann plus GAGA (or Chow), with Mumford 1970 §§1-3 and Serre's GAGA, or
   Milne 1986 §1, in place of the course notes (p. 14 AUDIT-READ); the `milne-av` bibliography
   entry names only Thm 12.1(a), so the in-text locator Thms 2.8-2.9 is to be kept. R-A9-2: the
   descent fact (fixed by `Aut(ℂ/ℚ̄)` ⇒ defined over `ℚ̄`, or the rigidity bijection; Conrad
   2006 §3). The centralizer step VERIFIED by rv-h-a9c9. Status [M], now with two model reviews.
3. **C9.** R-C9-1: the Euler-factor inference replaced by the `K_f`-linear Eichler–Shimura
   relation (`V_ℓ(A_f)` free of rank 2 over `K_f ⊗ ℚ_ℓ`, `tr Frob_p = a_p`; Shimura 1971 §7 and
   Thm 7.9, Ribet 1977, Diamond–Im §12.5, Diamond–Shurman Thm 8.7.2), then Chebotarev,
   Brauer–Nesbitt and Faltings' semisimplicity; the Klein-four example of why the identity alone
   does not suffice; the Hodge–Tate side check. R-C9-2: Galois-stability of newness (Shimura 1971
   Thm 3.52 with strong multiplicity one) and the conductor invariance under duality (*Corps
   locaux* VI §2, Deligne 1973 §8). R-C9-3: "primitive newform" is Li's normalized newform, not
   twist-minimal; `g` normalized. Shimura 1973 Thm 1: its hypothesis is met for the conjugate
   span whatever its form (Hecke, `Aut(ℂ)` or Fricke stability), the Fricke form AUDIT-READ, and
   not needed on the `K_f`-linear route. Status [R], application [M], now with two model reviews.
4. **Residuals.** §2.1 item 1: all three N5-only passages have two model reviews. §2.2 note.
   §2.4 `milne-av` row: both locators and the bibliography fix. §2.5: AUDIT-READ paragraph;
   item 4 (Shimura 1973) no longer decisive; item 9 adds the C9 and A9 locators. §2.7 (vii)
   closed.
5. **Drafts and Lean comments.** §3, the module docstring of `Hypotheses/Height.lean` and the H
   row of KERNEL_PLAN.md: the review count of A9's and C9's passages (rv-h-trust and
   rv-h-a9c9), the Eichler–Shimura relation (Shimura 1971) among the newform suppliers, and GAGA
   with Mumford. `HeightMin.lean` unchanged (it states no review counts or C9 suppliers).
6. **Next step.** §4: second reviews done; Shimura 1973's hypothesis no longer decisive.

Task h-v16-adopt (2026-11-11), applying `docs/research/rv-up.md` §3.5 items 1-4 and the proposal
"h-v16-adopt" of `docs/research/up-h.md` §§2, 4 (checked in rv-up §2.3). No constant, status,
count of §1, or Lean statement changes.

1. **F1, A2, Summary 2, §2.5 (rv-up §3.5).** F1's suppliers no longer include Lin–Yang eq. (2)
   (attributed by Lin–Yang to Baba–Granath, whose Prop. 3.9 rests on Prop. 3.7, whose printed
   proof has a defect recorded upstream): Example 30's divisors, eqs. (13)-(14), the theta
   expressions (LNY, Igusa), `igusa_check.py`, and `scratch/rv-up/endo24.py` and `theta24.py`
   for the constant at P₋₂₄ (all three rerun, identical). A2's Baba–Granath locator narrowed to
   Thm 2.1, Lemma 3.1 and the §3 datum. Summary 2 names what is used of each paper. §2.5: eq. (2)
   read but not used. §2.3 gains the rv-up row.
2. **C8.** The finiteness of the twist is Version 14's determinant argument (V16 L660-667),
   written out in four steps; the local-algebraicity step and the `conrad-local-characters` row
   of §2.4 are gone, and so is rv-h-c8 R4's inertia remark. Kato 2004 (§9.4, p. 188, with §6.3,
   §§5.4, 8.3, (14.10.2)-(14.10.3)) added as an all-levels (HT) supplier; Kronecker–Weber cited
   (Washington Thm 14.1). (HT) and Kronecker–Weber remain (rv-up §2.3).
3. **C3.** `F` chosen Galois over `ℚ` (V16 L536-537), so R1 is not needed; Fontaine,
   Astérisque 223, pp. 113-184, Thm 3.8, p. 142, replaces "exposé to be checked".
4. **A4, E4.** Deligne 1971 locators of V16 L979-1101 replace "§§4-6"; CMH 2014 §2.3 and
   Cor. 8.4 added as a second locator for E4.
5. **Bookkeeping.** Header and sources; Summary 4(d)-(e) (scripts; four citation swaps); route
   table row L719-795; §2.1 item 1 (C8); §2.5 items 3, 6, 11; §2.7 (iv)-(v); §3 drafts, the module
   docstring of `Hypotheses/Height.lean` and the H row of KERNEL_PLAN.md (Kato 2004; "Four
   citations"); §4 (Kato, Fontaine Thm 3.8). `HeightMin.lean` unchanged.

Task hsyn-fold (2026-11-12), step A6 only, applying `docs/research/rv-a6-route.md` §5. A6's
suppliers line is now the Raynaud route (A4; Raynaud SGA 7 IX 4.7 + 3.5; Serre–Tate Thm 1;
Mumford §4; `B ⊗ ℚ₃` division), with h-b1's argument (Grothendieck's semistable reduction and the
toric-part argument) kept as a second route. The Lean proof of the Raynaud route from its three
leaves (glue-a6-alg, `QuatUnipotentTrivial` proved) is cited. No status, count, constant or other
step changes.
