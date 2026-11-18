Recorded from the statement-check sweep of 2026-11-18: an AI-READ report written by an AI agent that the project runs (no person checked it), against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`. It clears no flag.

---

# Statement check: neronSchemeExtensionDedekind

**Verdict: UNVERIFIED.** The mathematical content is supported by the accessible global existence theorem in Conrad's notes. BLR's definition §1.2/1 was read, but the statement of BLR §1.4/3 was not available in the legitimate previews examined. A secondary source explicitly attributes global existence and quasi-compactness to that exact locator. This is not a verification of the unread theorem.

Date: 2026-11-18. **Evidence: AI-READ.**

## Field and commit

- Field: `HDec.HSyn.OpenResearchLeaves65.neronSchemeExtensionDedekind`.
- Proposition: `ZInQ.Contrib.GroupLawNeron.NeronSchemeExtensionDedekind`.
- Commit of the statement and OPEN.md: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
- Pinned [OPEN.md entry, lines 446–456](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L446-L456): published; strict GLUE; `unverified-locator`; packet R2.
- [Bundle field, TailZ91.lean:17–23](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/OneProof/H/TailZ91.lean#L17-L23).
- Checklist followed: [STATEMENT-CHECKS.md:49–75](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/STATEMENT-CHECKS.md#L49-L75). No BLR-specific entry was found in the pinned `locators.md`; its Néron-related hit concerns SGA 7, not this theorem.

## Edition, page, display

Cited print: S. Bosch, W. Lütkebohmert and M. Raynaud, *Néron Models*, Ergebnisse der Mathematik und ihrer Grenzgebiete (3), vol. 21, Springer, 1990; DOI `10.1007/978-3-642-51438-8`.

Primary pages actually read:

1. Publisher's chapter-1 preview: printed pp. 6–7, including §1.1's Dedekind-scheme convention; PDF pages 1–2.
2. Publisher-authorized Google Books ebook preview: printed p. 12, §1.2, **Definition 1**. The ebook listing identifies the 2012 electronic edition of the 1990 text; the publisher's front matter identifies the 1990 first-edition reprint. The page was read as an image, not reconstructed from a search snippet.
3. Publisher's front matter: bibliographic page and printed p. IX, table of contents. It places §1.2 at p. 12 and §1.4, “The Global Case: Abelian Varieties,” at p. 18, with §1.5 beginning p. 20.

Not read: the statement of §1.4, Theorem 3. Its exact theorem page was not confirmed. The chapter preview ends at p. 7; the direct publisher chapter-PDF request returned a subscription page, not the chapter PDF. The authorized ebook preview supplied p. 12 but did not supply the requested p. 19. No restricted page was retrieved by another route.

Secondary print read:

- Brian Conrad, *Néron models, Tamagawa factors, and Tate-Shafarevich groups*, dated October 14, 2015; notes taken by Tony Feng: **Theorem 1.1, printed/PDF p. 2**, Remark 1.3 continuing to p. 3, and the group-structure observation on p. 3.
- Matthieu Romagny, *Néron models of abelian varieties*, Summer School on SGA3, September 3, 2011: **Introduction and unnumbered Definition, printed/PDF p. 1**.
- Otto Overkamp and Takashi Suzuki, *Existence of global Néron models beyond semi-abelian varieties*, **arXiv:2310.14567v4, June 9, 2026**, §1.1, printed/PDF pp. 1–2, including footnote 1. This is the downloaded preprint, not a claim to have read its journal edition.

## Copy

Official publisher preview PDF and front matter; a page explicitly displayed by permission of Springer in Google Books; author-hosted university lecture notes; and an arXiv author preprint. No unofficial copy of the BLR book was downloaded. Downloads and exact byte hashes are recorded below.

## Quote

Mathematical subscripts, arrows and font distinctions are transcribed in standard notation; line breaks and line-end hyphenation are removed. Ellipses below mark omitted words. No quotation below is attributed to the unread BLR theorem.

### BLR: standing convention and definition

Printed p. 6, §1.1:

> “a noetherian normal scheme of dimension ≤ 1”

Printed p. 7, continuation of §1.1:

> “It is only for technical reasons that we do not require Dedekind schemes to be connected.”

Printed p. 12, §1.2, Definition 1, clause excerpts:

> “Let X_K be a smooth and separated K-scheme of finite type.”
>
> “an S-model X which is smooth, separated, and of finite type”
>
> “For each smooth S-scheme Y”
>
> “there is a unique S-morphism u : Y → X extending u_K.”

These excerpts verify the definition number, finite type, separatedness, the smooth test-scheme quantifier, and uniqueness. They do **not** verify existence.

### Conrad: full global existence statement

Theorem 1.1, p. 2:

> “Let S be a Dedekind scheme (i.e., a connected normal noetherian scheme of dimension 1), F its function field, and A an abelian variety over F. There exists a smooth separated finite type S-scheme 𝒜 with generic fiber A such that for all smooth T → S, any map T_F → A over F uniquely extends to a map T → 𝒜 over S:”

BLR is identified immediately beforehand as the lecture's main reference. The theorem itself is not accompanied by the exact citation §1.4/3.

### Romagny: the same mapping-property definition

Introduction, p. 1:

> “A Néron model of A_K over S is a smooth, separated model of finite type A that satisfies the Néron mapping property”

The following clause requires extension from the generic fibre of a smooth S-scheme, uniquely. The same page distinguishes the property restricted to étale test schemes as a **weak** Néron-model property. It does not identify this definition or the existence assertion by BLR §1.2/1 or §1.4/3.

### Overkamp–Suzuki: exact existence-locator attribution

§1.1, p. 2:

> “For a general (global) S, the Néron model of an abelian variety exists and is quasi-compact by [BLR90, Section 1.4, Theorem 3].”

Footnote 1 on p. 2 distinguishes their locally-finite-type usage from BLR's quasi-compact Néron models. Important qualification: before this quotation, the authors impose excellence of S and connectedness of G_K. This quotation is evidence of the exact BLR attribution, not an independent unrestricted-base theorem for every Dedekind domain.

## Standing hypotheses

- BLR convention actually read: S is noetherian and normal, of dimension **at most** one. It need not be connected. Its ring of rational functions is the finite product of the function fields of its components; for connected S it is a field. The text explicitly includes the spectrum of a field in the local case.
- BLR §1.2 actually read: S has that Dedekind convention, K is its ring of rational functions, and X_K is smooth, separated and of finite type. The mapping property is imposed for arbitrary smooth S-schemes Y. There is no separatedness or global finite-type condition imposed on Y in the printed definition.
- BLR §1.4/3: any additional theorem-specific hypotheses remain unread. They must not be supplied from recollection.
- Conrad: connected normal noetherian S of dimension one, its function field F, and an abelian variety over F. The printed existence statement has no excellence, completeness, henselianity, characteristic or perfect-residue-field restriction.
- Romagny: noetherian integral normal S of dimension one and an abelian variety over its function field. The later reduction to a DVR is a construction step, not a restriction in the initial global setup.
- Overkamp–Suzuki: irreducible Dedekind S and function field K; the ensuing discussion assumes S excellent, G_K connected, and commutative group schemes. Their own model terminology allows locally finite type without quasi-compactness, which they explicitly distinguish from BLR.

## Lean unfolded to plain mathematics

The definition is at [MumfordGroupLawNeron.lean:56–62](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean#L56-L62).

For every commutative Dedekind domain D **that is not a field**, every field L equipped with a D-algebra structure making it a fraction field of D, and every abelian variety A over L, there exist:

- a scheme N over S = Spec D;
- a smooth, separated, quasi-compact structure morphism N → S;
- an isomorphism ε : N ×_S Spec L ≅ A of L-schemes;

such that for **every** smooth S-scheme Y and every L-morphism u : Y_L → A, there exists an S-morphism f : Y → N with ε ∘ f_L = u.

The same N and ε work for all Y and u. Neither N nor Y is required to be affine; only the base is affine. N is not required to be proper. There is no restriction of Y to étale, affine, separated, quasi-compact, finite-type, or group schemes. The maps being extended are ordinary scheme morphisms, not just group homomorphisms.

### Definition dependencies and line references

- D and L, lines 57–58: `IsDedekindDomain D` includes the integral-domain, noetherian, dimension-at-most-one and integral-closure conditions. Together with `¬ IsField D`, this makes Spec D integral, normal, noetherian and dimension exactly one. `IsFractionRing D L` identifies L with Frac D through the specified algebra map; L is not an arbitrary extension of Frac D.
- A, line 58: [Objects.lean:160–178](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Objects.lean#L160-L178) defines `PkgI3.AbVar L` as a group object over Spec L, proper, smooth and geometrically integral. Commutativity is supplied by a theorem, not an extra open assumption. No polarization, positive-dimension or characteristic restriction appears here.
- Generic fibre, lines 60 and 42–44: [genMap](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/MumfordGroupLawNeron.lean#L41-L44) is Spec of D → L. Pullback along this map is the ordinary generic fibre. ε is an isomorphism of underlying schemes; no group structure on N or group compatibility is requested.
- Finiteness, lines 59–60: smoothness gives local finite presentation and hence local finite type. Quasi-compactness then gives finite type, exactly the finiteness required by the printed definition. With separatedness, N is also of finite presentation. This is not the weaker assertion that a possibly non-quasi-compact Néron lft-model exists.
- Extension, lines 61–62: surjectivity of Hom_S(Y,N) → Hom_L(Y_L,A), f ↦ ε ∘ f_L, says existence of extension, for each arbitrary smooth Y.
- Uniqueness: the leaf does not separately assert injectivity, unique extension, or uniqueness of the model. Unique extension follows because Y is flat, the generic fibre is schematically dense, and N is separated. The pinned [NMPInjective.lean:41–68](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/NeronC/NMPInjective.lean#L41-L68) supplies the general injectivity and dominance lemmas. The generic-point morphism is quasi-compact because it is affine. Consequently the restriction map above is a bijection. Applying the mapping property to models gives the usual uniqueness up to isomorphism compatible with the generic-fibre identification.
- Group structure: the leaf asks only for N as a scheme. This is consistent with BLR §1.2's definition and weaker than demanding a group scheme as extra data. The mapping property recovers the group operations, as Conrad observes on p. 3.

The dependency definitions were read at the mathlib revision fixed by the pinned manifest: `56a005855ea17e0b0958f73ec801ae140b0a1679`. This was a source reading, not a new Lean build or a proof that every definition-faithfulness obligation in the project is closed.

## Comparison

| Clause | Printed evidence and comparison |
|---|---|
| Base ring/scheme | Spec D is an affine instance of Conrad's connected, normal, noetherian dimension-one base, and lies within BLR's broader convention read on p. 6. No DVR-only restriction is being substituted for a global result. |
| “Not a field” | This is an additional restriction in Lean, not a dropped source hypothesis. However, the comment/flag's rationale that **BLR's Dedekind schemes are necessarily one-dimensional** is inaccurate: BLR explicitly permits dimension ≤ 1, including fields. This finding concerns the explanation, not an overstrong Lean conclusion. |
| Fraction field | The specified D-algebra L is a fraction field of D, matching the function field of the integral base Spec D. The statement does not ask for a model over an arbitrary unrelated field. |
| Abelian variety | The input is a proper smooth geometrically integral group scheme over L, not a general smooth variety or arbitrary algebraic group. No extra polarization or residue-field hypothesis is discarded. |
| Smooth and separated | Both are explicit in the leaf and in BLR Definition 1 and Conrad Theorem 1.1. |
| Finite type | The leaf's smoothness plus quasi-compactness implies finite type. It does not demand properness, or merely local finite type while omitting quasi-compactness. |
| Generic-fibre identification | The explicit isomorphism ε is the identification implicit in an S-model in BLR and explicit in the notes. It is fixed before choosing the test scheme or map. |
| Smooth test schemes | BLR p. 12 and Conrad p. 2 say **each/all smooth S-schemes**. The Lean quantifier matches; it is not relying on the weaker étale-point extension property printed in BLR §1.1. |
| Maps and quantifier order | Every generic-fibre scheme morphism extends to this one N, for every smooth Y. There is no group-homomorphism-only limitation and no choice of a different model for each map. |
| Uniqueness and group data | Lean explicitly requests only surjectivity and scheme data. Unique extension follows from the verified structural conditions, and the group structure is recoverable. These omissions do not strengthen the assertion. |
| Existence locator | Conrad prints the full unrestricted global statement. Overkamp–Suzuki explicitly cite **BLR §1.4, Theorem 3** for global existence and quasi-compactness, but do so within an excellent-base discussion. The actual BLR theorem remains unread; the exact locator therefore cannot be certified by this report. |

## Verdict

**UNVERIFIED**, limited specifically by the unread BLR existence theorem §1.4/3 and any theorem-specific qualifications on that page.

The inspected definition §1.2/1 is correctly numbered and matches the model and mapping-property clauses. Conrad's printed Theorem 1.1 supports the mathematical content of the non-field affine-Dedekind statement without extra excellence or perfectness assumptions. This support must not be relabelled as a reading of BLR §1.4/3. There is no basis here for **NO-locator**, since no different theorem was read at that locator; nor was a statement-strengthening mismatch found in the inspected clauses.

## False, incomplete or unclear

No counterexample to the Lean proposition was found. The incomplete part is source verification of the existence theorem, not a demonstrated mathematical failure. The explanatory assertion that BLR's definition of a Dedekind scheme excludes fields is contradicted by the publisher's p. 6. The extra Lean non-field hypothesis is a harmless narrowing for the statement compared here; no code change is proposed by this report.

## Not read

BLR §1.4/3, its proof and any theorem-specific preceding conventions; the remainder of BLR §1.2 after p. 12; BLR's construction chapters and cited lemmas; Artin's chapter in *Arithmetic Geometry*; the proofs behind the secondary existence statements; and the later results of Overkamp–Suzuki. No full definition-faithfulness audit of abelian varieties was attempted. Repository theorem sources and the named injectivity lemmas were inspected, but no compilation, test, repository edit, issue comment, or flag change was performed.

## AI use

An automated language-model assistant performed source discovery, downloaded legitimate copies, used Poppler's `pdftotext` on the PDFs, visually read the primary page images, read pinned Git objects and pinned dependency definitions, checked byte hashes, and wrote the mathematical comparison. The page-12 quotation is a visual transcription. No person independently read or endorsed the quotations or verdict in this check.

**Evidence: AI-READ.** This report is not HUMAN-READ evidence and does not clear the `unverified-locator` flag or change a LEAF/GLUE rating.

## Source URLs and SHA-256

Hashes identify the downloaded PDF/image bytes, not extracted text. Stable reading URLs are supplied alongside an exact image URL where needed.

### Primary literature

1. **BLR chapter-1 publisher preview**, pp. 6–7: https://page-one.springer.com/pdf/preview/10.1007/978-3-642-51438-8_2
   - SHA-256: `ced95c4d425935e38236fcafd630eddb33056411cea0a5dffb1862bbe4d3aa91`
   - Publisher chapter page: https://link.springer.com/chapter/10.1007/978-3-642-51438-8_2
2. **BLR p. 12, publisher-authorized ebook preview**, §1.2 Definition 1: https://books.google.com/books?id=BNfnCAAAQBAJ&pg=PA12&hl=en
   - Exact preview image supplied by that page: https://books.google.com/books/publisher/content?id=BNfnCAAAQBAJ&pg=PA12&img=1&zoom=3&hl=en&sig=ACfU3U0MFX0b6lsSSanllsWO1rSHuyiY1w
   - SHA-256 of the PNG: `719fa61390c8e3af73c19829ab2b2c8ad80721d3243ba1e3c6799eaa79a519c0`
   - The signed preview-image URL may expire; the reading URL identifies the edition and page.
3. **BLR publisher front matter**, bibliographic page and table of contents p. IX: https://link.springer.com/content/pdf/bfm:978-3-642-51438-8/1
   - SHA-256: `596b87aa699ceb4daa86c120f1ccfc5f0cbee5e84f5bb02280ff0ba793de938f`

### Secondary literature

4. **Conrad**, Theorem 1.1 p. 2, Remark 1.3 pp. 2–3, group structure p. 3: https://math.stanford.edu/~conrad/BSDseminar/Notes/L3.pdf
   - SHA-256: `bc27aad24f5b0ba8b1ae7fa6f8dde25f17ce479e46b1ff0256cf0e512ce988e6`
5. **Romagny**, global setup and Definition p. 1: https://imag.umontpellier.fr/~romagny/exposes/Neron_models.pdf
   - SHA-256: `22f81b540f570943fc98c9aca54ab2154f17680beb957c7ed00bae16ea1a7d7e`
6. **Overkamp–Suzuki**, arXiv v4, §1.1 pp. 1–2: https://arxiv.org/pdf/2310.14567
   - Downloaded edition: `arXiv:2310.14567v4`, June 9, 2026; versioned reference: https://arxiv.org/abs/2310.14567v4
   - SHA-256: `b75664a95d671d30bd3a4680956356962563a92922c5a01b81bdb57b662a6a67`

### Pinned definition support

These are source-code definitions, not substitutes for the cited literature theorem:

- [DedekindDomain/Basic.lean:123–150](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/DedekindDomain/Basic.lean#L123-L150): `IsDedekindRing` and `IsDedekindDomain`. SHA-256 of the raw source: `973a53a52dd7a3f918b933f545914ad7407b3786e77d7831a67ac03f3739965f`.
- [Smooth.lean:56–62,108–109,235–239](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean#L56-L62): smoothness, flatness and local finite presentation. SHA-256: `c547e32c9245e50a7b40034971893b29f1d729e004084ca1a11f9e82f97940e9`.
- [QuasiCompact.lean:37–44](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/QuasiCompact.lean#L37-L44): relative quasi-compactness. SHA-256: `add9feaca87bbd714f8045fef8e12d8e49819c81ef43343a5d65844985d26b4a`.
- [FiniteType.lean:17–20](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean#L17-L20): finite type means locally finite type and quasi-compact. SHA-256: `c960aa2a0ddd36c5aa1cc09beeeddb208b0de3403ab51f22f289f95153f59db5`.
- [FinitePresentation.lean:19–24](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/FinitePresentation.lean#L19-L24): local finite presentation, quasi-compactness and quasi-separatedness. SHA-256: `f772a3e6b5973ecc813c5876daae944ba26412f1a6ec4d54b61b86a5e35f10ba`.
