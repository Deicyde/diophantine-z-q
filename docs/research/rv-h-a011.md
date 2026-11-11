# rv-h-a011: adversarial review of the audit record A011-V14 (`docs/research/h-a011.md`)

Status: review record (task rv-h-a011, 2026-11-10). It reviews `h-a011.md` at commit `f9ec06b`.
That record applies Pan's Theorem 1.0.4 directly to the representation `r₅` of Version 14's
Lemma `lem:qm-modularity-descent`.

**Verdict: proved after the listed repairs.** No mathematical gap was found. Every hypothesis of
Pan's Theorem 1.0.4 is discharged for the right representation, at the right prime and over the
right field. This holds relative to the sources that neither h-a011 nor this review could read
(listed in §6). The repairs (§1) correct overstated evidence, descriptions and wording. None of
them changes an argument or a constant.

Marks, as in `h-a011.md`:

- **VERIFIED**: checked here against a text, or an elementary argument checked step by step.
- **STANDARD**: a published theorem whose exact statement was checked here.
- **SPECULATIVE**: an assessment, not proved.
- **UNCHECKED**: the source could not be read here.

**Line numbers.**

- "V14 L" is upstream's published Version 14 TeX with carriage returns removed. That stripped
  copy is kept outside the worktree. The line numbers h-a011 cites agree with it, up to ±1 in
  two places (F9).
- "FM.tex L" is Pan, arXiv:1901.07166v2, TeX source.
- "h-a011 §" refers to the record under review.

**Sources read for this review.**

- The record in full, `h-v14.md` §§3.3, 4 and 7, and `h-leaves.md` §3.3.
- V14 L448-690, L1208-1214, L1393-1546, L8140-8205, L10360-10400 and L13280-13300, and the
  bibliography entries `pan2022`, `berger2002`, `silverbergzarhin`, `calegari-icm2022` and
  `direct-p5-modularity-project`. I also grepped all V14 citations of project supplements.
- Pan's TeX: FM.tex L150-275 (the introduction and the notation section); the statements of
  Theorem 7.1.1 (L3969-3981), Theorem 8.0.1 and Remarks 8.0.2-8.0.4 (L4428-4456), Theorem 9.0.1
  and Remarks 9.0.2-9.0.3 (L4763-4790); Corollary `classicality` (L1192-1198).
- Breuil, arXiv:math/0009252v1, the typeset Annals text: pp. 489-493 and 543-549. These cover
  the setting, Corollaire 1.6, Lemme 5.2.1, Théorème 5.3.2, Corollaire 5.3.4 with its proof,
  Remarque 5.3.5, and the bibliography.
- Berger, arXiv:math/0102179v3: the header, Théorème 0.6 with its context (TeX L405-423), and
  Théorème 5.19 (L3633).
- Berger04 (arXiv:math/0210184v1), TeX L385-392, L1216-1226 and L1255-1260.
- Bhatt–Morrow–Scholze, arXiv:1602.03148v3, Theorem 1.1.
- Coleman–Iovita, arXiv:math/9701229v1, pp. 1-3 and 21-22.
- Silverberg–Zarhin, *Semistable reduction of abelian varieties over extensions of small
  degree*, arXiv:alg-geom/9702004v2. It was read only for the way these authors cite their 1995
  paper and Raynaud's criterion.
- Crossref metadata for DOI `10.1090/jams/991`, and the arXiv abstract page of 1901.07166
  (submission history and comment).

**Not readable here.** The AMS journal text of Pan's paper (the AMS site could not be reached),
and Silverberg–Zarhin 1995 (the Numdam site could not be reached). Everything else that is
UNCHECKED in h-a011 §8 also stays UNCHECKED.

## 1. Findings, by severity

No finding is a gap: none leaves a hypothesis of Pan's theorem undischarged.

**F1 (moderate: overstated evidence; it affects the proposed citation).**

- *Where.* h-a011 Summary item 1 lists as evidence for the JAMS numbering that "Version 14's own
  bibliography cites it as 'Theorem 1.0.4, p. 5' (VERIFIED, V14 L23910-23913)".
- *What is wrong.* That entry cites **arXiv:1901.07166v2** explicitly: "arXiv:1901.07166v2,
  Theorem 1.0.4, p. 5, the historical author-proof version. Published in Journal of the American
  Mathematical Society 35 (2022), 1031--1169" (VERIFIED, V14 L23910-23913). So it says nothing
  about the journal's numbering, and the evidence item is circular.
- *Knock-on effect.* The proposed manuscript text (h-a011 §5) and the proposed leaf wording
  (h-a011 §7) cite "[Pan, J. Amer. Math. Soc. 35 (2022), Theorem 1.0.4]". That asserts a
  journal numbering which is UNCHECKED.
- *Repair R1.*
  - Delete the evidence item.
  - Cite the theorem the way V14's bibliography already does: "Pan, arXiv:1901.07166v2,
    Theorem 1.0.4 (published in J. Amer. Math. Soc. 35 (2022), 1031-1169)".
  - Keep "JAMS numbering UNCHECKED" as the one bibliographic open point.
- *What was rechecked.* The other evidence items were rechecked and hold (VERIFIED): the v2
  date 3 September 2021 with the comment "137 pages; v2, revised version"; Crossref's vol. 35,
  no. 4, pp. 1031-1169, online 15 November 2021; and the published abstract, including the
  "p ≥ 5" sentence.

**F2 (minor: inaccurate description in a passage marked VERIFIED, h-a011 §1.2).**

- *What the record says.* §1.2 describes Theorem 8.0.1 as "residually irreducible with
  `ρ̄|G_{ℚ(ζ_p)}` irreducible, which reproves Kisin 2009 and Hu–Tan 2015".
- *What Pan's text says.*
  - Theorem 8.0.1 also assumes that `ρ|G_{F_v}` is **absolutely irreducible** for every `v | p`,
    that is, the non-ordinary case (FM.tex L4437).
  - Remark 8.0.3 (L4450) sends the ordinary case to Skinner–Wiles 2001.
  - Remark 9.0.2 (L4782) says that SW01 needs `ρ̄|G_{F_v}` not of the form
    `(η *; 0 η)`, and that this excluded case "was known by the work of [Kis09a], [HT15]".
  - Section 8 opens: "This was previously known by the work of Kisin, Hu-Tan and Emerton. Our
    treatment is more uniform" (L4428).
- *Consequence.* Pan's paper does not itself prove every case of Theorem 1.0.4. The ordinary
  cases in both residual regimes rest on SW99/SW01 (with Pan's own §7 for the case
  `χ̄₁/χ̄₂|G_{ℚ_p} = 1`), and one residually irreducible subcase rests on Kisin and Hu–Tan, as
  the introduction says ("combining the work of Skinner-Wiles, Kisin, Hu-Tan", FM.tex L224)
  (VERIFIED).
- *Effect on the verdict.* h-a011 treats these as internal to a refereed numbered theorem.
  That is a policy, and V14's scope paragraph uses the same one (L673-675: "his ordinary
  inputs"). So the verdict stands.
- *Repair R2.* Correct the description, and state the policy explicitly: the leaf is Pan's
  stated theorem, and the cited works inside its proof are not leaves.

**F3 (minor: overstated removal claim).**

- *Where.* h-a011 Summary item 5, §7 and the success criterion say that routes (a) and (b)
  remove "the hidden use of Berger's theorem".
- *What is right.* The removal holds at the interface. The hypothesis "pst" is supplied
  directly. Pan's body theorems are stated with "de Rham": Theorems 7.1.1, 8.0.1, 9.0.1 and
  Corollary `classicality` (FM.tex L3976, L4437, L4774, L1195; VERIFIED). Passing from pst to
  de Rham is the elementary direction. So checking the leaf needs no Berger.
- *What was not examined.* Whether Pan's proof uses dR ⇒ pst internally, for instance through
  the classicality step and Colmez–Paškūnas, was not examined by h-a011 or here (SPECULATIVE).
  The same remark applies to route (c): Berger's Théorème 0.6 rests on André's quasi-unipotence
  theorem (Berger v3, TeX L415: "Andr\'e a r\'ecemment montr\'e qu'un tel module est
  quasi-unipotent"; VERIFIED wording).
- *Repair R3.* Say "removed from the hypothesis check", not "removed".

**F4 (minor: attribution of the direction of Breuil's corollary that is used).**

- *What holds.* Breuil's Corollaire 5.3.4 is quoted exactly, and its setting is right (§3
  below). The record's caveat is correct: Breuil proves only representation ⇒ reduction, and
  calls the converse "classiques et bien connues (et dues à Fontaine)", without a reference
  (VERIFIED, p. 547).
- *Two corrections to h-a011 §3.4.*
  - The record calls Coleman–Iovita's attribution "VERIFIED". Their p. 3 says: "The only if
    part of this statement is known by work of J.-M. Fontaine [Fo-BT] and the if part was
    conjectured by J.-M. Fontaine in [Fo-MGF]". Read literally, for "T_p(A) is crystalline if
    and only if A has good reduction", that attributes crystalline ⇒ good to [Fo-BT]. The
    content makes clear that the words are swapped: the conjecture, proved for `e < p − 1` and
    by Mokrane, is crystalline ⇒ good. The record's reading is the intended one, but it is an
    interpretation (VERIFIED wording).
  - The arXiv file has no bibliography (pp. 21-22 end in the body of Chapter I). So
    "[Fo-BT] = Fontaine, Ann. of Math. 115 (1982)" is inferred from the key; it was not read.
    Mark it UNCHECKED.
- *Effect on the verdict.* Criterion 1 of h-v14 §7 asks for a numbered published statement,
  and Corollaire 5.3.4 is one. The point is that the published support for the direction used
  is an unreferenced attribution inside that corollary's proof.
- *Repair R4.* Add that caveat next to "STANDARD" in the Summary (item 2(b)) and in §7, not
  only in §3.4 and §8.

**F5 (informational, SPECULATIVE: the record undersells route (a)).**

- *What the record says.* h-a011 §7 says Scholze must stay, because removing it "needs
  `D_dR(V₅(A)) = H¹_dR(A)^∨` with its Hodge filtration".
- *What the kept argument actually consumes.* V14 L561-666 uses only two things:
  - that `r₅` is de Rham over `ℚ₅`;
  - the multiset of its Hodge–Tate weights, `{0, −1}`.

  It does not use the filtration on `H¹_dR`.
- *A possible replacement.*
  - Under route (a), `A_{K'}` has good reduction. Tate's Hodge–Tate decomposition for
    `p`-divisible groups (Tate, *p-divisible groups*, Driebergen 1967) would give weights
    `0, 0, −1, −1` for `V₅(A)|G_{K'}`, since the `p`-divisible group and its dual both have
    dimension 2.
  - The de Rham property over `ℚ₅` follows from pst at 5 by the Galois descent that V14
    already writes out (L542-546).
  - With the determinant check, which needs only `a + b = −1` and weights in `{0, −1}`, this
    would remove Scholze, the erratum and Milne 1986 Thm 15.1(a) from H.
- *Status.* SPECULATIVE. Tate 1967 is UNCHECKED, and its exact locator is not pinned. This is
  a follow-up, not a defect.

**F6 (minor: the proposed manuscript edit is incomplete).**

- *Where.* h-a011 §5 replaces V14 L506-509 and L669-680 only.
- *What it misses.* V14 cites the same survey sentence and supplement for the same lemma twice
  more (VERIFIED):
  - at L10386-10389 (§`sec:v4-inherited`: "the published prime-five statement in
    [calegari, p. 624] … The source-status map in [direct-p5-modularity-project]");
  - in the "Height" row of the table "Primary theorem applications" (L13296-13300, citing
    `calegari-icm2022`). h-v14 §5.1 already quotes that row.
- *What still holds.* For H only the proof of Theorem 4.1 counts, so the trust-leaf delta of
  h-a011 §7 is right. Within V14 §4 (L448-1680) the only project supplements cited are the five
  that h-v14 lists, and `direct-p5` only at L680 (VERIFIED by grep).
- *Repair R5.* List L10386-10389 and L13296-13300 as places that a manuscript edit must
  update too.
- *Related.* V14 already carries an uncited bibliography entry `berger2002` (L23906-23909,
  "p-adic monodromy theorem"). Route (c) would cite it.

**F7 (informational: choices of embedding).**

- *Where.* h-a011 §3.4 fixes "the place `w` of `F` determined by the fixed embedding
  `Q̄ ↪ Q̄₅`".
- *What V14 fixes.* Only an embedding of the number field `C` into `Q̄₅` (L496-497). One has to
  choose an extension `Q̄ ↪ Q̄₅`. Any choice works, because decomposition groups at 5 are
  conjugate and pst is invariant under conjugation (VERIFIED as an argument).
- *Similarly in §4.* Pan's `ρ_g` is attached through his fixed `ι_p` (FM.tex L253). V14's
  `U_g` uses its own coefficient embedding. If the two differ, replace `g` by a conjugate
  `g^σ`, `σ ∈ Aut(ℂ)`. That is again a cuspidal eigenform of the same weight, and V14 L577
  already extends embeddings compatibly.
- *Repair.* None needed; a sentence would help.

**F8 (informational: "exactly the same application").**

- h-a011 §3.4 route (b) says V14 makes "exactly this application at L1501-1503". There V14
  takes `F = L_v` with `L` the field of the application (L1501). The record uses the lemma's
  `F_w`. It is the same criterion (full rational 3-torsion, residue characteristic 5) over a
  different base field. That is harmless, but "exactly" overstates it.
- *The content of Silverberg–Zarhin 1995, Thm 3.5.*
  - That it is Raynaud's criterion is consistent with V14 L8197-8198 ("full rational
    11-torsion gives semistable reduction … [Theorem 3.5, p. 406]").
  - The same authors cite this criterion in 1997 as "a theorem of Raynaud (see Proposition 4.7
    of [SGA 7 IX])" (alg-geom/9702004v2, TeX L518-520; VERIFIED wording). They do not cite it
    there as their 1995 Theorem 3.5. That is neither evidence for nor against the 1995
    numbering.
  - SZ 1995 Thm 3.5 stays UNCHECKED, as in A013.

**F9 (trivial: line references).**

- The polarization line is V14 L636-637, not L634-636 (h-a011 §3.6 and §4).
- "r₅ ≅ U_g ⊗ δ" is at L561-563, and the k = 1 paragraph is L579-591. Both match the record.
- The other spot-checks agree with the record.

## 2. Pan's Theorem 1.0.4: statement, hypotheses, conventions (item 1 of the task)

| Claim of h-a011 | Check | Mark |
| --- | --- | --- |
| Conjecture 1.0.1 quoted exactly (FM.tex L167-177): continuous, irreducible `ρ : Gal(Q̄/ℚ) → GL₂(Q̄_p)`, finitely many ramified places, pst at the decomposition group at `p` "in the sense of Fontaine", odd (`det ρ(c) = −1` for every complex conjugation) | read at L167-177; the conclusion there says "arises", while Theorem 1.0.4 says "comes" | VERIFIED |
| Theorem 1.0.4 quoted exactly (L226-233): `p` odd; distinct Hodge–Tate weights of `ρ\|G_{ℚ_p}`; at `p = 3` only, `(ρ̄\|G_{ℚ_p})^{ss}` not of the form `η ⊕ ηω`; conclusion "comes from a cuspidal eigenform up to twist" | read at L226-233 | VERIFIED; STANDARD for arXiv v2 |
| No other hypothesis: no Taylor–Wiles or big-image condition, no residual irreducibility or modularity, no ordinarity split | none in L226-233; the residual modularity of Theorems 8.0.1/9.0.1 is automatic over `ℚ` by Khare–Wintenberger (Remark 8.0.4, L4453-4455) and is internal to the proof | VERIFIED |
| Numbering 1.0.x in the compiled arXiv v2 PDF | `scratch/h-a011/numbering.output.txt` (header lines p. 2-5) | VERIFIED (h-a011's output; not rerun) |
| JAMS numbering | AMS text not readable | UNCHECKED (see F1) |
| Pan's conventions: `ε` has HT weight `−1`; `Frob_v` geometric; local class field theory sends uniformizers to geometric Frobenius; `ι_p : Q̄_p ≅ ℂ` fixed | FM.tex L253, L268, L270 | VERIFIED |
| Same HT convention as V14 ("`ℚ₅(1)` has weight `−1`", L537) | read | VERIFIED |
| The conventions do not matter for the hypotheses | "distinct" does not depend on the sign; oddness does not depend on Frobenius | VERIFIED as an argument |
| The conclusion feeds V14 L561-666 under either Frobenius convention: if `ρ_g ≅ U_g^∨`, then `U_g^∨ ≅ U_g ⊗ (det U_g)^{−1}` because `dim = 2`, so `r₅ ≅ U_g ⊗ δ` with `δ` continuous | checked. Traces of `Frob_geo` on `ρ_g` equal traces of `Frob_arith` on `U_g`, so `ρ_g ≅ U_g^∨` by Chebotarev and semisimplicity in characteristic 0. V14 needs no more than "classical cuspidal eigenform of positive weight" and a continuous `δ`: primitivity at L565-577, `k = 1` excluded at L579-591, finiteness of `δ` at L635-642 | VERIFIED as an argument |
| How 1.0.4 is proved (h-a011 §1.2) | description partly inaccurate | see F2 |

The task's question "pst or de Rham?" deserves a separate answer. Pan's Theorem 1.0.4 asks for
**pst** (through Conjecture 1.0.1), while his body theorems ask for "de Rham". The record
supplies pst (routes (a) and (b)), or de Rham plus Berger (route (c)). Both match the stated
hypothesis (VERIFIED).

## 3. The discharges (items 2 and 3 of the task)

### 3.1 Representation, prime and field for each hypothesis

| Hyp. | Representation and group | Prime / field | Verdict | Mark |
| --- | --- | --- | --- | --- |
| H1 continuity | `r₅` on `G_ℚ`, through the open subgroup `G_F` and its finitely many cosets. On `G_F`, `ρ₅` is the Tate action tensored with `E` (V14 L511-521: `t` and `μ` are trivial on `G_F`) | — | correct | VERIFIED as an argument |
| H2 irreducibility | `r₅\|G_F` absolutely irreducible ⇒ `r₅` absolutely irreducible on `G_ℚ` ⇒ irreducible over `Q̄₅` | `E ⊂ Q̄₅` | correct. The commutant count gives `M₂(End_{G_F}(r)) = M₂(E)`, so `End = E`; that persists after extension, and semisimplicity persists in characteristic 0 | argument VERIFIED; Faltings 1986 UNCHECKED |
| H3 finite ramification | `r₅` on `G_ℚ`. For `q` unramified in Galois `F`, every inertia group at `q` lies in `G_F`, where the action is the Tate action, unramified at good places prime to 5 | `q ∉ S₀` | correct; the spreading-out is uncited in V14, as the record says | argument VERIFIED; Serre–Tate UNCHECKED |
| H4 pst | `r₅\|G_{K'}`, `K' = F_w(A[3]) ⊇ F_w`, so `G_{K'} ⊂ G_F`. There `V₅(A) ⊗ E ≅ r₅ ⊕ r₅` as `ℚ₅[G_{K'}]`-modules | 5; `K'` finite over `ℚ₅` | correct for routes (a), (b) and (c); details in §3.2 | see §3.2 |
| H5 oddness | `r₅(c)` for `c ∈ G_ℚ`, which in general is not in `G_F`. V14 works with `ρ₅(c) = t_cμ_c c`, which is right. The Betti trace `t_c · tr(μ_c c) = 0` does not depend on which embedding of `t_c` is used. `r₅(c)² = r₅(c²) = 1` because `t₁ = 1` and `μ₁ = 1` | — | correct | argument VERIFIED; Milne 2005 UNCHECKED |
| H6 distinct HT weights | `r₅\|G_{ℚ₅}`. HT weights do not change under restriction to `G_{F_w}`. For a `ℚ₅`-representation `V`, `(V ⊗ E) ⊗_{E,τ} Q̄₅ = V ⊗ Q̄₅` for every `τ` | 5 | correct (V14 L532-547), plus the determinant check of §3.3 | VERIFIED as present / as an argument |
| H7 `p = 3` clause | — | `p = 5` | vacuous | VERIFIED |

### 3.2 Route (b) in detail, and routes (a) and (c)

**Breuil, Corollaire 5.3.4 (p. 547).** The quotation in h-a011 §3.4 is exact; I compared it with
p. 547 and with its announcement as Corollaire 1.6 on p. 493.

- *Setting (p. 490).* `k` is perfect of characteristic `p`, `K₀ = Frac W(k)`, and `K` is "une
  extension finie totalement ramifiée de `K₀` de degré `e ≥ 1`". Any finite `K'/ℚ₅` is of this
  form, with `k` its residue field and `K₀` its maximal unramified subfield.
- *The hypothesis `k ⊆ F̄_p`.* The bar is lost in the extracted text, but the proof of
  Lemme 5.2.1 reads "Si `k` est fini … Si `k ⊂ F̄_p` n'est pas fini" (p. 544). So finite residue
  fields are covered.
- *Which direction is proved.* The proof proves only representation ⇒ reduction:
  crystalline ⇒ good, through Théorème 5.3.2 and SGA 7 IX Cor. 5.10; semistable non-crystalline
  ⇒ semistable, through SGA 7 IX Prop. 5.13(c). The direction that is used, reduction ⇒
  representation (semistable ⇒ semistable, good ⇒ crystalline), is "classiques et bien connues
  (et dues à Fontaine)", with no reference.
- *Earlier cases.* Remarque 5.3.5 says the corollary was known for `e ≤ p − 1` from Laffaille,
  and in the good-reduction case from Mokrane and Coleman–Iovita.
- *Marks.* The statement is STANDARD in the published text. The direction used is unproved in
  that paper (see F4).

**Silverberg–Zarhin Theorem 3.5.** Applied to `A_{F_w}` with `n = 3`, `3 ≥ 3` and `5 ∤ 3`. Over
`K' = F_w(A[3])` all 3-torsion is rational, so Raynaud's criterion gives semistable reduction in
the SGA 7 sense. That is the sense of "réduction semi-stable" in Breuil's proof (SGA 7 IX
5.13). The application is correct as an argument. The source is UNCHECKED (F8).

**The summand lemma (h-a011 §3.4).** VERIFIED as an argument.

- `D(V) = (𝐁 ⊗ V)^{G_{K'}}` is additive.
- `V₅(A) ⊗_{ℚ₅} E ≅ V₅(A)^{[E:ℚ₅]}`, since `E` is a free `ℚ₅`-module with trivial action. So
  `dim_{K'₀} D` of it is `[E:ℚ₅] · 4` when `V₅(A)` is admissible.
- As `ℚ₅[G_{K'}]`-modules it is `r₅ ⊕ r₅`, where `r₅` has `ℚ₅`-dimension `2[E:ℚ₅]`.
- `D(r₅ ⊕ r₅) = D(r₅)²`, so `dim D(r₅) = 2[E:ℚ₅] = dim_{ℚ₅} r₅`, which is admissibility.
- This needs neither the inequality `dim D(W) ≤ dim W` nor any regularity of the period ring
  beyond the definition of admissibility. Pst of a `Q̄_p`-valued `ρ` means pst of an `E`-model
  viewed as a `ℚ_p`-representation, the usual convention.

**Route (a).** Lemma PG's steps are correct for `B = (2, −3)`, the algebra of V14 L689.

- `hilbert_check.py` confirms that `(2, −3)` is ramified exactly at `{2, 3}` among
  `∞, 2, 3, 5, 7`. So `B ⊗ ℚ₃` is a division algebra, its modules have `ℚ₃`-dimension divisible
  by 4, and `V₃(A)^I = V₃(A)` (VERIFIED by script and as an argument).
- The endomorphisms are defined over `F ⊆ K'` by the lemma's own hypothesis (V14 L511-514), so
  NoCM is not needed (VERIFIED).
- The record's remark on the general lemma (a definite `B` is not covered) is correct and marked
  SPECULATIVE.

**Route (c).** Berger's Théorème 0.6 (TeX L423) = Théorème 5.19 (L3633), "Si V est une
représentation p-adique de de Rham, alors V est potentiellement semi-stable". The header (L4)
reads "version revisee (1ere revision) pour Inventiones Mathematicae". STANDARD for that version;
the journal numbering is UNCHECKED, as the record says.

### 3.3 The determinant check (h-a011 §3.6)

VERIFIED as an argument.

1. On `G_F`, `(det_E r₅)² = det_E(r₅ ⊕ r₅) = det_E(V₅(A) ⊗ E) = det_{ℚ₅} V₅(A) = ε₅^g` with
   `g = 2`. That is the Weil pairing, or V14's "polarization pairing" (L636-637).
2. So `det r₅ = α ε₅` with `α² = 1` on `G_F`, and `α` has finite order.
3. `r₅|G_{ℚ₅}` is Hodge–Tate with integer weights `a, b`: pst ⇒ dR ⇒ HT, or directly from V14
   L532-547. The weight of `det` is `a + b`, and the weight of `α ε₅` on `G_{F_w}` is
   `0 + (−1)`. So `a + b = −1`, which is odd, hence `a ≠ b`.
4. Consistency: the weights of `V₅(A)`, `0, 0, −1, −1`, sum to `−2`, the weight of `ε₅²`.

The check needs the Hodge–Tate property, which comes from §3.4 or from V14 L532-547; the record
says so. It does not give `{0, −1}` itself, and the record says that too.

## 4. Removals, additions and constants (item 4 of the task)

| Claim of h-a011 | Check | Mark |
| --- | --- | --- |
| The survey sentence is removed as supplier | true for the proof of Theorem 4.1. Two other V14 places still cite it for the same lemma (F6) | VERIFIED, with F6 |
| `direct-p5-modularity` is removed; five supplements become four (`a001`, `ly-d6`, `b11`, `igusa-theta`) | the only §4 citations of project supplements are at L680 (`direct-p5`), L723 (`a001`), L756/L1179/L1609 (`ly-d6`), L785/L808/L912/L1117 (`b11`) and L1623 (`igusa-theta`). The `pan-p5-sw99`, `pan-local-rings` and `pan-utility` entries (L24274-24292) are not cited anywhere | VERIFIED |
| The hidden Berger dependency is removed (routes (a), (b)) | at the interface only (F3) | VERIFIED, with F3 |
| Added: Pan Thm 1.0.4 (change of role), Breuil Cor. 5.3.4, SZ Thm 3.5 reused, Lemma PG under (a), Berger under (c) | complete. Two qualifications: Breuil's used direction rests on an unreferenced attribution (F4), and Pan's proof cites SW99/SW01/Kisin/Hu–Tan (F2) | VERIFIED |
| No constant of `H₆(S;R)` changes | the constants block V14 L454-475 involves only `F₀`, `D`, `G₀`, `E₀`, `Q_R`, `B_cm`, `C_cm`. The lemma is qualitative (L502). `K' = F_w(A[3])` is local and enters no bound. The conductor bound L1483-1546 uses `r_ℓ`, Carayol and its own local fields `L_v(A[3])` | VERIFIED |

## 5. Repairs, collected

- **R1** (F1): cite Pan as arXiv v2, Theorem 1.0.4, published in JAMS 35 (2022). Drop the
  V14-bibliography evidence item. Keep the JAMS numbering UNCHECKED.
- **R2** (F2): correct the description in §1.2. Theorem 8.0.1 is the non-ordinary case; the
  ordinary cases go through SW99/SW01; Kisin and Hu–Tan cover SW01's excluded case. State the
  "internal to a refereed theorem" policy.
- **R3** (F3): "removed from the hypothesis check", not "removed".
- **R4** (F4): put the Breuil/Fontaine caveat next to every "STANDARD" for Cor. 5.3.4. Mark
  Coleman–Iovita's attribution as an interpretation of swapped wording, and
  "[Fo-BT] = Ann. Math. 115" as UNCHECKED.
- **R5** (F6): list V14 L10386-10389 and L13296-13300 among the places a manuscript edit must
  update.
- Optional: F5 (Tate 1967 as a possible replacement of Scholze under route (a)), F7 (a sentence
  on the choice of embeddings), F8, F9.

## 6. UNCHECKED here

- Pan's JAMS text: the numbering, and any proof paragraph added in the journal.
- Silverberg–Zarhin 1995, Thms 3.3 and 3.5.
- Fontaine 1982 and Fontaine's semistable case: the primary sources of the direction of
  Corollaire 5.3.4 that is used.
- Berger's *Inventiones* numbering.
- Faltings 1986; Serre–Tate 1968; Milne 1986 and 2005; Fontaine 1994; Scholze's journal version
  and erratum.
- Deligne–Serre, Kato, Washington, Shimura, Li.
- Tate 1967 (F5 only).

## 7. Scripts

- `scratch/rv-h-a011/hilbert_check.py [a b]` computes the Hilbert symbols of `(a, b)` at
  `∞, 2, 3, 5, 7` (Serre, *Cours d'arithmétique*, III Thm 1). Output:
  `scratch/rv-h-a011/hilbert_check.output.txt` (`(2,−3)` ramified at `[2, 3]`). As a sanity
  check, `(−1, −1)` gives `[∞, 2]`.
- `scratch/rv-h-a011/log.md` is the work log.
- h-a011's `pdf_page.py` and `pdf_grep.py` were used for reading. Downloaded files, and the
  carriage-return-stripped copy of V14, are kept outside the worktree.
