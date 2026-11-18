Recorded from the statement-check sweep of 2026-11-18 (AI-READ): a literature search, not a check of an open row. It concerns the leaf `ZInQ.Manuscript.KolyvWeil.BCDTThmA6` (`ZInQKernel/Contrib/OneProof/KolyvWeil/Leaves.lean` on branch `wip/kolyv-weil` at commit `cfe47c6e7d64587f00af0f091100e6bd7c6e63a0`). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Printed statements of conductor-level X₀ modularity

Verified 18 November 2026. Scope: nonconstant morphisms from \(X_0(N_E)\) to a specified elliptic curve \(E/\mathbb Q\), with \(N_E\) its conductor and the morphism defined over \(\mathbb Q\).

## 1. Recommended printed sources

**Two directly inspected printed sources support the requested statement without strengthening their wording.** Darmon supplies a numbered nonconstant-map theorem; Dummigan supplies a refereed-journal statement of a finite morphism, explicitly citing BCDT. Neither requires semistability, an analytic-rank bound, or replacement of the given curve by its optimal representative.

### 1.1 Darmon: a numbered theorem with exactly the required level and field

Henri Darmon, “Rational points on curves,” in *Arithmetic Geometry*, Clay Mathematics Proceedings **8**, AMS/Clay Mathematics Institute, 2009, §5.1, **Theorem 5.4, printed p. 43**.

- Official complete-volume PDF: https://www.claymath.org/wp-content/uploads/2022/03/cmip08c.pdf
- SHA-256: `2509ba088488ca73eb07c05fde39b8ff5bb8a9fd4848c14a1dab81c0ff7fba2a`
- Location: **PDF p. 50 of 570 = printed p. 43**. The title and copyright leaves identify the published AMS/CMI volume, not an author preprint.

The setup in §5.1 reads:

> Let \(E\) be an elliptic curve over \(\mathbb Q\) of conductor \(N\).

The theorem reads:

> Theorem 5.4. There exists a nonconstant map of curves over \(\mathbb Q\)
> \[
> \varphi:X_0(N)\longrightarrow E.
> \]

The proof on the same page constructs this map through the Jacobian and a rational isogeny, ending:

> The modular parametrisation \(\varphi\) is defined by setting \(\varphi(x):=\Phi((x)-(\infty))\).

**Classification: (a), conductor-level X₀, with explicit rational definition.** The proof gives a morphism on the projective curve, not merely a formula on an unspecified open subset. Although the preceding prose calls it a dominant rational map, the displayed theorem and its construction give the regular map required here.

**Scope checked:** the rank bound belongs to Theorem 5.3, not Theorem 5.4. The historical Theorem 4.6 is semistable, but its extension to *all* elliptic curves by [BCDT01] is explicitly stated on printed p. 40 (PDF p. 47) and reiterated on p. 43 before §5.1. The proof's abbreviated citation to Theorem 4.6 must be read with that explicitly stated extension. No semistability hypothesis is silently removed.

### 1.2 Dummigan: a one-sentence refereed-journal statement citing BCDT

Neil Dummigan, “On a conjecture of Watkins,” *Journal de Théorie des Nombres de Bordeaux* **18** (2006), no. 2, 345–355, **§1, printed p. 345**. DOI: https://doi.org/10.5802/jtnb.548.

- Numdam journal PDF: https://www.numdam.org/item/10.5802/jtnb.548.pdf
- Bibliographic page: https://www.numdam.org/item/JTNB_2006__18_2_345_0/
- SHA-256: `fa5f3da5d4a30c7f079396fcc850374897f31349370beab8496748e15cfaa7a2`
- Location: **PDF p. 2 of 12 = printed p. 345**, following the distribution cover.
- A second legitimate journal copy was read directly: https://www.maths.tcd.ie/EMIS/journals/JTNB/2006-2/article04.pdf
- Second-copy SHA-256: `45f50194216d7c611a643588af02b42801ce22b0e759e09d2d14f37cb35554b6`
- Second-copy location: **PDF p. 1 of 11 = printed p. 345**. No byte identity between the two files is asserted.

Verbatim opening sentence:

> For any elliptic curve \(E\) defined over \(\mathbb Q\), of conductor \(N\), there exists a finite morphism \(\Phi:X_0(N)\to E\), defined over \(\mathbb Q\), where \(X_0(N)\) is the modular curve parametrising elliptic curves and cyclic subgroups of order \(N\) [BCDT].

Reference [BCDT], printed p. 355 (Numdam PDF p. 12), is Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over Q: wild 3-adic exercises*, JAMS **14** (2001), 843–939.

**Classification: (a), conductor-level X₀, explicit rational morphism, universal for the specified E.** The literal word is **finite**; it has not been replaced inside the quotation by “nonconstant” or “surjective.” A finite morphism between these nonempty integral projective curves is necessarily nonconstant and surjective. Thus the requested nonconstant-morphism assertion is weaker than this printed assertion. The following optimality discussion and the special assumptions introduced in §2 concern minimal modular degree and Watkins's conjecture, not the universal opening sentence.

### Citation recommendation for the pending leaf

Use **Darmon, Theorem 5.4, p. 43, with its §5.1 conductor setup**, as the direct numbered geometric citation. Add **Dummigan, §1, p. 345**, as independent printed corroboration with all conductor and field clauses in one sentence and BCDT expressly cited. Do not describe BCDT Introduction condition (6) as an X₀ statement.

## 2. Classification and quotation conventions

- (a): X₀ at the explicitly identified conductor.
- (b): X₀ at a level not explicitly identified as the conductor.
- (c): X₁ in the geometric parametrization formulation.
- (d): the quoted universal formulation is a modular-form, eigenform, q-expansion, or representation formulation, not an explicit X₀ morphism.
- J: a Jacobian quotient statement. This supplementary label prevents calling a literal \(J_0\)-quotient sentence a literal \(X_0\)-morphism sentence.
- Unverified: the relevant mathematical text was not legitimately obtained. Index entries and bibliographic metadata do not determine its classification.

Rational definition, theorem/conjecture status, restrictions, and edition identity are recorded separately. A source can have different classifications for different passages. Quotations preserve words and hypotheses; line wrapping, discretionary hyphenation, and mathematical typography are normalized. A quoted fragment is identified as such. PDF pages are one-based physical positions; printed pages are the labels actually read, never an assumed offset into an unavailable edition.

Surjectivity here is geometric surjectivity. It is **not** a claim that \(X_0(N)(\mathbb Q)\to E(\mathbb Q)\) is surjective. Likewise, rational source and target curves alone do not make a particular map rational. The forgetful map \(X_1(N)\to X_0(N)\) lets an X₀ parametrization produce an X₁ parametrization by composition, not conversely without a descent argument.

## 3. Kolyvagin: N is explicitly the conductor

V. A. Kolyvagin, *On the Mordell-Weil group and the Shafarevich-Tate group of modular elliptic curves*, **MPI/90-69** (1990).

- Official archive PDF: https://archive.mpim-bonn.mpg.de/id/eprint/325/1/preprint_1990_69.pdf
- SHA-256: `bacdf23d05d5120defe923c8dcccd7c5bc525fe7b32239552b04fd6567726f2f`
- Location: **printed p. 3 / PDF p. 5 of 17**. Printed pp. 2–3 were read; the defining sentence is at the top of p. 3 and was checked against the scan.

Defining sentence:

> Let \(N\in\mathbb N\) be the conductor of \(E\).

The assumption later on the same page:

> Assume that \(E\) is modular, that is there exists a weak Weil parametrization \(\gamma:X_0(N)\longrightarrow E\) [12]. Here \(X_0(N)\) is the modular algebraic curve over \(\mathbb Q\) parametrizing classes of isogenies of elliptic curves with cyclic kernel of order \(N\).

**Classification: (a), explicitly conductor-level, as an assumption.** Universal modularity is still a conjecture in this 1990 text. These sentences use the technical term “weak Weil parametrization”; they do not separately spell out nonconstancy or rational definition of \(\gamma\). The words “over Q” in the quoted explanatory sentence modify \(X_0(N)\), not \(\gamma\). No missing qualifier has been inserted into the quotation. Reference [12], printed p. 14 / PDF p. 16, is Mazur–Swinnerton-Dyer, *Arithmetic of Weil curves*, Invent. Math. **25**, 1–61 (1974).

## 4. Requested standard references and historical sources

### 4.1 Diamond–Shurman, *A First Course in Modular Forms*

GTM **228**, Springer, DOI https://doi.org/10.1007/978-0-387-27226-9.

**Access-limited:** no permitted free complete book was obtained. Publisher front matter, back matter, and chapter previews were obtained. The front matter identifies the corrected **fourth printing, 2016**, not an authenticated first-printing copy.

- Front matter: https://link.springer.com/content/pdf/bfm:978-0-387-27226-9/1
- SHA-256: `e964d8fc27b260bb5e4819d49ad927c82d379fac67630617ec2d08e3cbb73696`
- Printed p. **xiii / excerpt PDF p. 11**:

> By analogy to the situation from elementary number theory, the Modularity Theorem associates to the equation \(E\) an eigenform \(f=f_E\) in a vector space \(V_N\) of weight 2 modular forms at a level \(N\) called the conductor of \(E\).

This is **(d)**, introductory eigenform/conductor wording. On printed p. **xiv / excerpt PDF p. 12**:

> The formulations of Modularity already in play rephrase algebraically to statements about objects and maps defined by polynomials over \(\mathbb Q\),
> \[
> X_0(N)_{\rm alg}\to E,\quad J_0(N)_{\rm alg}\to E,\quad A_{f,\rm alg}\to E.
> \]

This is an introductory **(b)**-type map display over Q, not a complete conductor-level nonconstant-map theorem. The conductor identification for this map was not established from the obtained pages. The index separately distinguishes analytic and algebraic conductor; their equality was not reconstructed from an index.

- Back matter: https://link.springer.com/content/pdf/bbm:978-0-387-27226-9/1
- SHA-256: `ef26b6c5e4021b0d9467e4bf700d034df0e0c7c8b9337975d76a3027010cb6c1`

The contents and index give **locators, not theorem text**:

| Requested version | Verified printed locator | Locator evidence | Mathematical statement |
|---|---|---|---|
| §2.5, Version \(X_{\mathbb C}\) | p. 63 | Contents p. vii / front PDF p. 6; index p. 444 / back PDF p. 31 | Not obtained; unverified |
| §7.7, Version \(X_{\mathbb Q}\) | section p. 294; version p. 296 | Contents p. viii / front PDF p. 7; index p. 444 / back PDF p. 31 | Not obtained; cannot quote its level or conductor clause |
| §8.8, Version \(a_p\) | section p. 360; version p. 361 | Contents p. ix / front PDF p. 8; index p. 443 / back PDF p. 30 | Not obtained; complete conductor formulation unverified |

The full-book request returned publisher no-access HTML, not a PDF. No hash or theorem quotation is invented for it. Author's page: https://people.reed.edu/~jerry/. Supplementary legitimate previews and errata are inventoried below.

### 4.2 Darmon, CBMS 101 (2004)

Henri Darmon, *Rational points on modular elliptic curves*, CBMS **101**, AMS, 2004.

- Author-linked complete copy: https://www.math.mcgill.ca/darmon/pub/Articles/Research/36.NSF-CBMS/chapter.pdf
- Author's publication listing: https://www.math.mcgill.ca/darmon/pub/pub.html
- SHA-256: `04f00c11cbb6767753a7f1509273dc81e8dc7950c88873a5d930d90e93d7b873`
- 139 PDF pages. The author links this typeset monograph as the published title; an AMS final-edition copy was not obtained for comparison.

**Theorem 2.12, printed p. 20 / PDF p. 30:**

> Theorem 2.12. Let \(E\) be an elliptic curve over \(\mathbb Q\) of conductor \(N\). Then there exists a newform \(f\in S_2(N)\) such that \(L(E,s)=L(f,s)\). Furthermore, \(E\) is isogenous to the elliptic curve \(E_f\) obtained from \(f\) via the Eichler-Shimura construction.

**(d)** for this numbered theorem, with an additional isogeny assertion. Here \(S_2(N)=S_2(\Gamma_0(N))\), as defined on printed p. 14 / PDF p. 24. Remark 2.13 explicitly credits the full extension to [BCDT01]. The theorem is not restricted to semistable curves.

The construction on printed p. 19 / PDF p. 29 gives \(X_0(N)\to E_f\); the unnumbered second corollary on printed p. 21 / PDF p. 31 gives the given target E:

> The second corollary is the existence of an explicit complex uniformisation \(\Phi_N:H^*/\Gamma_0(N)\to E(\mathbb C)\),

The same paragraph says to compose with a rational isogeny \(E_f\to E\). The proof of Theorem 3.6, printed pp. **33–34 / PDF pp. 43–44**, contains the exact fragment:

> the map \(X_0(N)\to E\) induced by \(\Phi_N\) is a map of algebraic curves defined over \(\mathbb Q\).

**Combined book evidence: (a)**, conductor-level rational geometric parametrization, but not one numbered geometric theorem. Do **not** quote Theorem 2.12 as though it literally contains the last sentence. For a single numbered printed statement, prefer the Clay Theorem 5.4 above.

### 4.3 Silverman, *The Arithmetic of Elliptic Curves*, second edition (2009)

GTM **106**, Springer. Author page: https://www.math.brown.edu/johsilve/AECHome.html. Publisher page: https://link.springer.com/book/10.1007/978-0-387-09494-6.

**The relevant theorem text was not legitimately obtained; classification unverified.** The public author excerpt contains preface, contents, and introduction, not Appendix C's body.

- Excerpt: https://www.math.brown.edu/johsilve/AEC/AECPrefaceTOCIntro.pdf
- SHA-256: `86a784ef135191371d665e033d2ca065c86b168b52783a42b0228d56e39a85f4`
- Contents, printed p. xiv / PDF p. 10:

> §13. Modular Curves 439
>
> §16. L-Series 449

- Author's second-edition changes: https://www.math.brown.edu/johsilve/AEC/AECChangedIn2ndEdition.pdf
- SHA-256: `1f999450ba8f3a532d9f8d733a8e9993314be3f54b03daf1d86b2e61d6f4f443`
- Printed/PDF p. 4:

> Appendix C, Theorem 13.6. Changed from a conjecture (credited to Taniyama and Weil) to a theorem (credited to Wiles et. al.), with a more precise statement. Added two paragraphs on the history of Wiles’s proof.

This gives an author-supported lead to **C.13.6**, not an exact theorem quotation and not evidence of a conductor or field clause. The section-start page 439 is not assigned as the theorem page. C §16 is L-Series. Publisher back matter was available but begins at actual printed p. 461 and does not contain the requested appendix, despite a broader landing-page range. No pirate copy or remembered theorem wording was used.

### 4.4 Wiles, Annals 141 (1995)

Andrew Wiles, “Modular elliptic curves and Fermat's Last Theorem,” *Annals of Mathematics* **141** (1995), 443–551.

- Publisher page: https://annals.math.princeton.edu/1995/141-3/p01
- DOI: https://doi.org/10.2307/2118559
- **Article PDF, SHA-256, introduction quote, and classification: unavailable/unverified.** No permitted free original was obtained. The publisher's public policy places the 1995 PDF outside its since-2003 open archive; no access workaround or non-author mirror was used.

A legitimate author bibliography was obtained, but is not the article:

- https://web.math.princeton.edu/WebCV/WilesBIB.pdf
- SHA-256: `e6f61f3cf51f63777b8484747a6fd5ced1e784ad1001dad180dd7d6370c7e627`
- Printed/PDF p. 2, item 15:

> Modular Elliptic Curves and Fermat’s Last Theorem, Annals of Mathematics, 141, (1995), 443-551.

This does not verify Wiles's definition of “modular.” DDT's report of Wiles is not substituted for reading Wiles.

### 4.5 Darmon–Diamond–Taylor, *Fermat's Last Theorem*

The author's listing identifies *Current Developments in Mathematics* 1 (1995), with a 1997 International Press reprint. The available author copy is dated **September 9, 2007**; exact identity and pagination relative to the 1997 printed reprint were not authenticated.

- Author PDF: https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf
- SHA-256: `254f6e29957f95219eff046c29478f5ee584615bee12c8aa8357f499c8cbe8b3`
- 167 PDF pages; quoted local printed and PDF numbers agree. They are not promoted to 1997 book page numbers.

**§1.8, local printed/PDF p. 47**, setup:

> Let \(E\) be any elliptic curve defined over \(\mathbb Q\), and let \(N\) denote its arithmetic conductor, defined as in section 1.1. Then we have:

**Proposition 1.53**, part (c):

> There is a non-constant morphism defined over \(\mathbb Q\), from \(X_0(N)\) to \(E\).

This is **(a)** as an equivalent characterization of modularity. The other equivalent conditions are newform/rational-isogeny statements. It does not assert that every E satisfies them. On local p. 48:

> Conjecture 1.54 All elliptic curves defined over \(\mathbb Q\) are modular.

On local p. **102**, **Theorem 3.48**:

> If \(E/\mathbb Q\) is a semistable elliptic curve, then \(E\) is modular.

The theorem plus Proposition 1.53 gives the conductor-level rational map for semistable curves. The source also reports results for curves semistable at 3 and 5, but the unrestricted assertion remains conjectural in the inspected text. A regenerated date does not upgrade its mathematics. Remark 1.55, local p. 48, points to Diamond–Im **§13** for more equivalent formulations; Diamond–Im itself was not read.

### 4.6 BCDT: author manuscript versus unavailable journal edition

Breuil–Conrad–Diamond–Taylor, *On the modularity of elliptic curves over Q: wild 3-adic exercises*, JAMS **14** (2001), 843–939.

- Read author manuscript: https://math.stanford.edu/~conrad/papers/tswfinal.pdf
- SHA-256: `13043cf6e9043a69dc7988882658cd92595efc88dfd4fd2f326ac3ef3cae8e06`
- 79 PDF pages. Its masthead has placeholder volume/page data; its local pages are not assumed to be journal pages.

**Theorem A, manuscript/PDF p. 1:**

> If \(E/\mathbb Q\) is an elliptic curve, then \(E\) is modular.

**Manuscript/PDF p. 2:**

> Let \(N(E)\) denote the conductor of \(E\). It is known that the following conditions are equivalent.

**Condition (2), manuscript/PDF p. 3:**

> The L-function \(L(E,s)\) of \(E\) equals the L-function \(L(f,s)\) for some eigenform \(f\) of weight 2 and level \(N(E)\).

**Condition (6), same page:**

> There is a non-constant morphism \(X_1(N(E))\to E\) which is defined over \(\mathbb Q\).

**Classification:** (c) for the geometric condition (6); (d) for condition (2). Condition (5) also uses X₁, at some positive integer level. The inspected elliptic-curve equivalence list ends at (6). Neither its wording nor the absence of (7) is asserted for an unread journal edition.

The publisher PDF request returned HTTP 403:

https://www.ams.org/journals/jams/2001-14-04/S0894-0347-01-00370-8/S0894-0347-01-00370-8.pdf

**Journal PDF hash and exact published introduction: unverified.** No access bypass was attempted. Work identity and bibliographic data do not prove edition-text identity. The author manuscript's (2) can support a conductor-level eigenform assertion; its (6) cannot be relabelled X₀.

### 4.7 Diamond–Im (1995)

Fred Diamond and John Im, “Modular forms and modular curves,” in *Seminar on Fermat's Last Theorem*, CMS Conference Proceedings **17** (1995).

**No qualifying free mathematical copy was obtained.** A third-party re-hosting was excluded. Exact wording, theorem page, and classification are unverified; no quote or PDF hash is invented. DDT Remark 1.55 supplies a bibliographic lead to **§13**, not the contents of that section. A pre-2001 conjecture or equivalence must not be upgraded to universal proved modularity.

### 4.8 Cremona, *Algorithms for Modular Elliptic Curves*

J. E. Cremona, second edition, Cambridge University Press, 1997. The author-authorized online text contains corrections; it is not an authenticated uncorrected first-printing scan.

- Author's book page: https://johncremona.github.io/book/
- Authorized full-text page: https://johncremona.github.io/book/fulltext/index.html
- Chapter II PDF: https://johncremona.github.io/book/fulltext/chapter2.pdf
- SHA-256: `432fa5290b2b2ac0d623169e9198d928e5dd75acb490db2d58775630d0f6ea94`
- 45 PDF pages, printed pp. 7–51.

**§2.15.1, printed p. 47 / chapter PDF p. 41:**

> An elliptic curve \(E\) defined over \(\mathbb Q\) is called a modular elliptic curve if there is a non-constant map \(\phi:X_G\to E\) for some modular curve \(X_G\).

Later in the same paragraph:

> According to the Shimura–Taniyama–Weil conjecture, this should be the case for every elliptic curve defined over \(\mathbb Q\), with \(G=\Gamma_0(N)\), where \(N\) is the conductor of \(E\).

**(a), but conjectural universally.** The explicit “defined over Q” modifies E, not the map. The historical result on printed p. 46 / PDF p. 40 retains the exact condition fragment:

> provided that \(N\) is divisible by neither 4 nor 25.

Its footnote dates the time of writing to October 1996. The forward construction of \(E_f\), including its rational definition and conductor N on printed p. 48 / PDF p. 42, does not prove the universal converse or separately state rational definition of the parametrizing map. Do not remove the restrictions or quote the conjecture as a theorem.

## 5. Additional surveys and corroborating passages

### 5.1 Darmon, ICM survey

“Heegner points, Stark-Heegner points, and values of L-series,” listed by the author in ICM Vol. II (2006), 313–345.

- Author copy: https://www.math.mcgill.ca/darmon/pub/Articles/Research/45.ICM-lecture/paper.pdf
- SHA-256: `87ac01f798fc66a2a13b20d62c87c7aca9743897e2fc5c1efd09c3615eb01da2`
- §2, local printed/PDF p. 3:

> Given an elliptic curve \(E/\mathbb Q\), let \(N\) denote its conductor.

- §2.1, equation (4), local printed/PDF p. 4:

> An equivalent formulation of the modularity property is that there exists a non-constant map of algebraic curves defined over \(\mathbb Q\),
> \[
> \Phi_E:X_0(N)\to E,
> \]
> referred to as the modular parametrisation attached to \(E\).

**(a), explicit rational map at conductor level**, with the full BCDT modularity result stated on local p. 3. This is equation (4), not Theorem 2.1. The EMS final chapter was subscription-marked and was not obtained; its final printed page for equation (4) remains unverified. Publisher page: https://ems.press/books/standalone/21/399.

### 5.2 Darmon, author version of the decisive Clay survey

- https://www.math.mcgill.ca/darmon/pub/Articles/Expository/12.Clay/paper.pdf
- SHA-256: `0fdad4ed8ea83ca009b1928660f2959bdb38208f515ddfc9a96d085b3eca844f`
- Dated April 11, 2008; 70 PDF pages.
- Theorem 5.4 and conductor setup, local printed/PDF p. **54**, reproduce the two short statements quoted in §1.1 above.
- **(a).** Local p. 54 is not the published p. 43. The official printed volume supersedes this copy for citation.

### 5.3 Darmon, historical Wiles survey

“Wiles' theorem and the arithmetic of elliptic curves,” listed in the 1997 Springer collection, 549–569.

- https://www.math.mcgill.ca/~darmon/pub/Articles/Expository/03.BU-FLT/paper.pdf
- SHA-256: `3c5a9c54c2c4f9e32344315a463cc75528a9f3e4244a37e1b7e35497273f82cc`
- §2 fixes E/Q of conductor N on local printed/PDF p. 6.
- **Theorem 2.6, local printed/PDF p. 9:**

> Suppose that \(E\) has good or semistable reduction at 3 and 5. Then the elliptic curve \(E\) is uniformized by the modular curve \(X_0(N)\), i.e., there is a non-constant algebraic map defined over \(\mathbb Q\): \(\phi:X_0(N)\to E\).

**(a), restricted**, not every E/Q. The author file was regenerated in 2007 but retains these historical hypotheses; final 1997 page mapping was not verified.

### 5.4 Darmon, historical encyclopedia article

“The Shimura-Taniyama Conjecture,” listed by the author as a 1999 encyclopedia article.

- https://www.math.mcgill.ca/darmon/pub/Articles/Expository/07.Encyclopedia/paper.pdf
- SHA-256: `ce00cf21f379413e441e923ca7f542237ed76ed0bfacebcdc226213e255874f5`
- Local printed/PDF pp. 1–2:

> Weil's refinement of the conjecture predicts that the integer \(N\) is equal to the arithmetic conductor of \(E\).

- Local p. 2, exact opening clause:

> The modularity of \(E\) can also be formulated as the statement that \(E\) is a quotient of the modular curve \(X_0(N)\) over \(\mathbb Q\);

The primary cusp-form definition uses some N. **(b)** for that geometric equivalence, with a separately conjectural **(a)**-type conductor refinement; **(d)** for the primary definition. The stated proved range excludes conductors divisible by 27. Final encyclopedia page location was not obtained; the file's 2007 regeneration date does not upgrade it to a post-BCDT universal statement.

### 5.5 Watkins (2002)

Mark Watkins, “Computing the modular degree of an elliptic curve,” *Experimental Mathematics* **11** (2002), no. 4, 487–502.

- Author PDF: http://magma.maths.usyd.edu.au/~watkins/papers/moddeg.pdf
- SHA-256: `7231eb529166e8db5484297452132941b4a70d42b1bd1adcbc7fa42236ed2efe`
- §1, **author-layout printed/PDF p. 1 of 19**; final journal page mapping not checked.

The passage begins with E over the rationals, then states:

> By the work of Wiles and others ([Wiles 1995, Breuil et al. 2001]), it is known that there is a surjective morphism (called a modular parametrisation) \(\phi:X_0(N)\to E\), where \(X_0(N)\) is the (compactification of the) standard curve classifying cyclic \(N\)-isogenies and \(N\) is the conductor of \(E\).

**(a), surjective and conductor-level, but the quoted passage does not explicitly attach “defined over Q” to the morphism.** It maps to the given E, not only the optimal curve. For an explicit field-of-definition quotation, use Darmon or Dummigan instead. The journal publication is refereed; its precise final typesetting was not read here.

### 5.6 Agashe–Ribet–Stein: conductor-level Jacobian quotients

**“The modular degree, congruence primes, and multiplicity one,”** in *Number Theory, Analysis and Geometry*, Springer, 2012, 19–49.

- First-author copy: https://www.math.fsu.edu/~agashe/math/moddeg4.pdf
- SHA-256: `e9a6d1215f3883728416c7815f7dbb5d2b6c773a71b77e339790403c87accbda`
- §1, local printed/PDF p. 1 of 23; not mapped to final Springer pagination.

> Let \(E\) be an elliptic curve over \(\mathbb Q\). By [BCDT01], we may view \(E\) as an abelian variety quotient over \(\mathbb Q\) of the modular Jacobian \(J_0(N)\), where \(N\) is the conductor of \(E\).

The subsequent text assumes optimality, after permitting an isogenous replacement, and displays the Abel–Jacobi composite defining modular degree. **J, conductor-level rational quotient for the original E.** The \(X_0\)-composite is literally discussed after the optimality assumption. For arbitrary E, composing with the rational-cusp Abel–Jacobi map is a short mathematical inference, not the literal universal X₀ sentence quoted above. It is therefore not counted as another exact match in §1.

**“The Manin constant,”** *Pure and Applied Mathematics Quarterly* **2** (2006), no. 2, 617–636.

- Journal-format author copy: https://wstein.org/papers/ars-manin/agashe-ribet-stein-the_manin_constant.pdf
- SHA-256: `083f95c0d7f8b942e5da84c937669cb85e6d8e1b4fe7151b3db7310ce113628e`
- §1, **printed p. 617 / PDF p. 1 of 20**:

> Let \(E\) be an elliptic curve over \(\mathbb Q\), and and let \(N\) be the conductor of \(E\). By [BCDT01], we may view \(E\) as a quotient of the modular Jacobian \(J_0(N)\).

The doubled “and and” is retained. **J**, explicit conductor, not a literal X₀ map; the sentence does not separately attach “over Q” to the quotient. Do not silently replace \(J_0\) by \(X_0\). Other legitimate copies are inventoried below.

### 5.7 Stein: eigenform/q-expansion statements

William Stein, *Modular Forms: A Computational Approach*, AMS GSM **79** (2007), author-hosted copy.

- https://wstein.org/books/modform/stein-modform.pdf
- SHA-256: `b50e81d48d2fb794948414fee625d1d3ca19c191a87430ca38c8713c8f466b75`
- Printed p. **37 / PDF p. 51**:

> This conjecture, which is now a theorem (see [BCDT01]), asserts that any q-expansion constructed as above from an elliptic curve over \(\mathbb Q\) is a modular form.

- §10.7, printed p. **187 / PDF p. 201**, exact fragment:

> the procedure of this section gives all elliptic curves (up to isogeny) of given conductor.

**(d)** for these universal passages, not a literal map to the given E. The inspected file's numbering is recorded; equality with the final AMS printing's pagination was not independently certified.

Stein, “An introduction to computing modular forms using modular symbols,” MSRI Publications **44**:

- Official volume chapter: https://library.slmath.org/books/Book44/files/20stein.pdf
- SHA-256: `ded58d67a6362aff4c2af0802dbb5d2eb06a2f62edd028473e72c33686b99235`
- **Printed p. 643 / PDF p. 3:**

> The Shimura–Taniyama conjecture, which is now a theorem (see [Breuil et al. 2001]) asserts that any q-expansion constructed as above from an elliptic curve over \(\mathbb Q\) is a modular form.

**(d)**. The quoted assertion does not itself state the conductor-level geometric parametrization.

### 5.8 Milne (2006)

J. S. Milne, *Elliptic Curves*, BookSurge, 2006, first edition, freely posted by the author; not the 2020 second edition.

- https://www.jmilne.org/math/Books/ectext6.pdf
- Author listing: https://www.jmilne.org/math/Books/index.html
- SHA-256: `14a89055a0a7f52b08fad1d53786c9165caba8be837491024b9b210afa384486`
- Chapter V §5, **Conjecture 5.1, printed p. 208 / PDF p. 216:**

> A Dirichlet L-series \(\sum c(n)n^{-s}\), \(c(n)\in\mathbb Z\), is the L-series \(L(E,s)\) of an elliptic curve over \(\mathbb Q\) with conductor \(N\) if and only if it is the L-series \(L(f,s)\) of a normalized newform for \(\Gamma_0(N)\).

- Later proof status, **printed p. 210 / PDF p. 218**:

> Breuil, Conrad, Diamond, and Taylor improved the theorem so that it now says that all elliptic curves \(E\) over \(\mathbb Q\) is modular.

The original “is modular” is retained. **(d)** for the universal formulation. Theorem 6.3, printed p. 215 / PDF p. 223, separately constructs \(X_0(N)\to E_f\) from a newform in a Q-construction. Combining this with modularity and isogeny gives the desired result mathematically, but these passages are not a literal universal map-to-the-given-E theorem. It is not counted as a direct match.

### 5.9 Additional arXiv passages not promoted to printed exact matches

Agashe, “The modular number, the congruence number, and multiplicity one”:

- https://arxiv.org/pdf/0810.5176
- SHA-256: `291e1b57e4556fb06b7bd2dbea671837cd6214c7d8dc86b47dc452e4f1c1f299`
- PDF p. 1:

> If \(f\) has integer Fourier coefficients, then \(A_f\) is an elliptic curve and by [BCDT01] any elliptic curve over \(\mathbb Q\) is isogenous to such an elliptic curve for some \(f\).

**(d)/isogeny formulation**, not a literal X₀ map to the given E and not an explicit conductor identification in this sentence. It is not classified as (a) or used as a direct printed citation.

Watkins, “Explicit lower bounds on the modular degree of an elliptic curve”:

- https://arxiv.org/pdf/math/0408126
- SHA-256: `29ede7ba9f5952dd0eee8cb71c38596ccb7d4044954de14d6bb2798c8ab0dfbf`
- PDF p. 1:

> Let \(E\) be a rational elliptic curve of conductor \(N\); by the work of Wiles [24] and others, it is known that there is a surjective map \(\phi\) from \(X_0(N)\) to \(E\) known as a modular parametrisation.

**(a)** in this arXiv passage, but rational definition of the map is not explicit, BCDT is not named in the sentence, and final refereed-edition identity was not checked. It is not used as a decisive printed exact match.

## 6. Supporting-copy and excerpt inventory

These documents were legitimately obtained and hashed. They support edition identity, locators, or comparison of copies, not additional universal parametrization theorems. “No theorem quote” below means no new relevant modularity assertion is attributed to that document; mathematical quotations are confined to the inspected passages above.

| Document / extent actually read | Source URL | SHA-256 | Role and page locator |
|---|---|---|---|
| Diamond–Shurman chapter 2 preview | https://page-one.springer.com/pdf/preview/10.1007/978-0-387-27226-9_2 | `063c67430af532662eeb40de2f99a0f0ad715e0f8db1dec0b9837569e259f3ff` | Printed pp. 45–46 / PDF pp. 1–2; does not reach §2.5; no theorem quote |
| Diamond–Shurman chapter 7 preview | https://page-one.springer.com/pdf/preview/10.1007/978-0-387-27226-9_7 | `8ba81674eeb2477355b360424a499bc750b3aa9e3d1942c2b064aea8a32040c0` | Printed pp. 253–254 / PDF pp. 1–2; does not reach §7.7; no theorem quote |
| Diamond–Shurman chapter 8 preview | https://page-one.springer.com/pdf/preview/10.1007/978-0-387-27226-9_8 | `1eb0ddb66b90197b5e12d57613b6af68ff69e1686aaee5013db2aea8e7068faf` | Printed pp. 313–314 / PDF pp. 1–2; opening eigenform discussion, not §8.8's theorem |
| Diamond–Shurman first-printing errata | https://people.reed.edu/~jerry/MF/errata1.pdf | `5dcb1bf1c928b3e4ce18e4c329298f40e96becda77fa3841614256f35ba7fa75` | PDF pp. 1–2; corrections, not the requested theorem text |
| Diamond–Shurman second-printing errata | https://people.reed.edu/~jerry/MF/errata2.pdf | `68a0188e91414132a4727608923f9552100a431f918dc2d1a480aa109bd70077` | PDF p. 1; no replacement modularity statement |
| Diamond–Shurman third-printing errata | https://people.reed.edu/~jerry/MF/errata3.pdf | `b3d2f00fbf10435a36520761cc5451ee2813b38b571581451df1382a014be8bc` | PDF pp. 1–10; pagination and §7.7 corrections; not a full Version X_Q quote |
| Diamond–Shurman fourth-printing errata | https://people.reed.edu/~jerry/MF/errata4.pdf | `b3d013dffa6a80aeed2342a780cde0d3ec05d7b1c7d05e0b596fc764bd5e82ac` | PDF pp. 1–8; document date May 27, 2026; no replacement requested theorem |
| Silverman current errata | https://www.math.brown.edu/johsilve/AEC/AECErrata.pdf | `6c2274403a32af5d4b075c1504a1aaa04c9b304c0f94b8dd337f9c72d51f6f34` | 36 PDF pages; title specifies second printing (2015); does not reproduce C.13.6 |
| Silverman publisher back matter | https://link.springer.com/content/pdf/bbm:978-0-387-09494-6/1 | `5fc708c1ac0b861a3bb567f693a42e81d79b8c2d32d89619ba2ac352aebfbd17` | Actual printed pp. 461–513 / PDF pp. 1–53; appendix body absent |
| Cremona chapter I | https://johncremona.github.io/book/fulltext/chapter1.pdf | `2b17478b2a92a9c2e281b1cf8e863540770b59076de7f62bb0acd5a67a051163` | Printed/PDF pp. 1–6; edition and historical scope, not a new universal theorem |
| ARS modular-degree third-author copy | https://wstein.org/papers/ars-congruence/current.pdf | `cbbe88759df9953bd14d3bc04f2e1fa09be6f9c7da5b6fab371581b8b98fd9c3` | Local/PDF p. 1; same Q-quotient conductor sentence as §5.6; different following optimality phrasing |
| ARS modular-degree departmental archive | https://www.math.fsu.edu/~aluffi/archive/paper278.pdf | `3ce55edf65dbf04261975d64ac8c25bd60fc3e0e9018d4e885578a4ae2da539b` | Local/PDF p. 1; same initial quotient statement; not a final-page mapping |
| ARS Manin-constant departmental archive | https://www.math.fsu.edu/~aluffi/archive/paper279.pdf | `3403e4bdc50c107718a40fae81b075b8ca3426d4dfe32bfb9a3827e2e65eabb0` | Local/PDF p. 1; same initial J₀/conductor statement; not another X₀ theorem |

All **38 PDF hashes** cited in this report were recomputed and matched the recorded downloads. The decisive Darmon, Dummigan, and Kolyvagin passages received independent checks; Dummigan's opening was checked visually in the unencrypted journal copy and compared with the Numdam text. No repository changes, builds, or human outreach formed part of this research.

## 7. Exact remaining gaps

- Diamond–Shurman: actual version statements at the indexed pp. 63, 296, and 361 were not obtained. The preface is not substituted for them.
- Silverman: C.13.6 is a verified author-supported locator, but its mathematical text, exact theorem page, and conductor/field clauses remain unread.
- Wiles: the original introduction and definition of modularity were not obtained from an allowed free copy.
- Diamond–Im: actual §13 text was not obtained; DDT's cross-reference is only a lead.
- BCDT journal edition: the publisher PDF was refused; whether its Introduction differs from the accessible author manuscript remains unverified.
- Author-edition comparisons: CBMS, ICM, DDT, and several author article copies were not silently identified with their final printed page numbering. The two decisive sources in §1 have directly inspected published-edition text and verified printed locators.

These are bounded access and edition-verification findings, not claims that an authorized copy cannot exist elsewhere. They do not weaken the conclusion: **the conductor-level rational X₀ parametrization needed by the leaf is already supported directly by the printed Darmon and Dummigan statements.**
