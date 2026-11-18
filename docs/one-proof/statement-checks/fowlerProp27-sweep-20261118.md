Recorded from the statement-check sweep of 2026-11-18: an AI-READ report written by an AI agent that the project runs (no person checked it), against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`. It clears no flag.

---

# Statement check: fowlerProp27

**Verdict: CONSEQUENCE.** Fowler’s printed Proposition 2.7 has exactly the proposed numerical bound, for all negative order discriminants and with no exceptional-field exclusion. Applying it to the Lean field additionally uses the order-discriminant and Picard/class-number dictionaries spelled out below. No stronger numerical theorem or missing arithmetic hypothesis was found.

Checked on 2026-11-18. This is a statement comparison, not a compilation or proof of the dictionary in Lean.

## Field and commit

- Field: `HDec.HSyn.OpenResearchLeaves65.fowlerProp27`.
- Proposition: `HDec.CMBranch.FowlerProp27`.
- Commit of the code, checklist and open list read: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
- Open-list entry: [OPEN.md, lines 376–388](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L376-L388).
- Field binding: [TailZ91.lean, lines 62–63](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/OneProof/H/TailZ91.lean#L62-L63).
- The requested checklist and [AUDIT.md, item 1](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/reviews/height-replacement/height/AUDIT.md#L17) were read. The latter was treated as a previous claim, not as a substitute for reading the publication.

## Edition, page, display

Guy Fowler, *Some uniform effective results on André–Oort for sums of powers in* \(\mathbb C^n\), *Mathematical Proceedings of the Cambridge Philosophical Society* **180** (2026), 607–641, DOI [10.1017/S0305004125101825](https://doi.org/10.1017/S0305004125101825).

- Journal Proposition **2·7**: printed p. **615**, PDF page **9**; its proof continues on printed p. **616**, PDF page **10**.
- Standing definitions: §2·1, printed pp. **612–613**, PDF pages **6–7**.
- Exception comparison: Proposition 2·5, printed p. **614**; Proposition 2·6, printed p. **615**.
- Independently compared with **arXiv:2405.06456v2**, revised 3 November 2025: Proposition **2.7**, p. **9**, including its entire proof on that page.

**Numbering map:** arXiv v2 Proposition 2.7 is journal Proposition 2·7, not a renumbered theorem. The statement, bound, conductor/class-number argument and separate treatment of \(D=-3,-4\) agree. The journal typesetting splits the proof across pp. 615–616 whereas arXiv v2 keeps it on p. 9. The journal PDF’s own page 1 is printed p. 607, so its PDF pages 9–10 are pp. 615–616. This is a display-by-display comparison, not an assumed global page offset between arXiv and the journal.

## Copy

Publisher PDF downloaded directly from Cambridge University Press; author-deposited arXiv v2 PDF used as a second edition. The downloaded copies were read through PDF text extraction and page reading. No unauthorized mirror was used.

### Source URLs and SHA-256

1. **Journal PDF, primary copy**
   - URL: https://www.cambridge.org/core/services/aop-cambridge-core/content/view/A72ABDB14BEB62DE7E9B47953B77DBDC/S0305004125101825a.pdf/some_uniform_effective_results_on_andreoort_for_sums_of_powers_in_mathbbcn.pdf
   - SHA-256: `bc676f4d5b6a2a70fa3e6bed55a4449622d6728167d4c668068b89da6b2d55ae`
   - 35 PDF pages; 391,611 bytes.
2. **arXiv v2 PDF**
   - URL: https://arxiv.org/pdf/2405.06456v2
   - SHA-256: `91669100e54b048c9fd55d951bfd36a3b3d0acaf40508e369f73f431f03eebee`
   - 32 PDF pages; 540,262 bytes.
3. **Printed order/ideal dictionary**: Barquero-Sanchez, Cadwallader, Cannon, Genao and Masri, *Faltings heights of CM elliptic curves and special Gamma values*, *Research in Number Theory* **3** (2017), article 13, §4, p. **6**.
   - URL: https://link.springer.com/content/pdf/10.1007/s40993-017-0077-7.pdf
   - SHA-256: `8752beb7b997e31a1f8a5e3ec5a13f5d8c0b675f7862305f1a873cd4b9f5ec8d`
4. **Explicit forms-to-ideals correspondence**: Eum, Jung, Koo and Shin, *On some extension of Gauss’ work and applications (II)*, arXiv:1810.06197v1, introduction pp. **1–2**, display **(1)** on p. **2**.
   - URL: https://arxiv.org/pdf/1810.06197
   - SHA-256: `61ce0cfbda94f38c60a80c50da89c0d79b27de07d9f6b41f95b7534ea15b2b61`
5. **Index/discriminant explanation**: Janis Klaise, *Orders in Quadratic Imaginary Fields of Small Class Number*, dated 27 March 2012, University of Warwick author copy, pp. **2–3**; forms/class-group statement, Theorem **7**, p. **6**.
   - URL: https://warwick.ac.uk/fac/cross_fac/complexity/people/students/dtc/students2013/klaise/janis_klaise_ug_report.pdf
   - SHA-256: `6d8dced2e991bc5945cd377cce648bc74d49cfd622acc277c2d795809bf92d7c`
   - Only the forward index/discriminant statement is used; the converse sentence on p. 3 is not used.

## Quote

The following is a short transcription of the journal statement; mathematical glyphs and superscripts are restored, not paraphrased.

> **PROPOSITION 2·7.** Let \(\Delta<0\) be such that \(\Delta\equiv0,1\bmod4\) and let \(k\in\mathbb Z_{>0}\). If \(h(\Delta)\leq k\), then
> \[
> |\Delta|^{1/2}\leq 2k^2e^{21000k^2}.
> \]

Journal p. 613 defines the quantity being bounded:

> “where \(h(\Delta)\) denotes the class number of the imaginary quadratic order of discriminant \(\Delta\).”

Supporting dictionary, Barquero-Sanchez et al., §4, p. 6:

> “It is known that a fractional \(\mathcal O_f\)-ideal is invertible if and only if it is proper (see [3, Proposition 7.4]).”

On the same page the printed definitions are \(\operatorname{Cl}(\mathcal O_f)=I(\mathcal O_f)/P(\mathcal O_f)\) and \(h(\mathcal O_f)=\#\operatorname{Cl}(\mathcal O_f)\), and the order discriminant is stated to be \(\Delta_f=f^2D\).

Eum et al., introduction p. 2, explicitly identify the form class group with that proper ideal class group in display (1):

> “Then, it is well known that the form class group \(C(D)\) is isomorphic to the \(O\)-ideal class group \(C(O)=I(O)/P(O)\) through the isomorphism”
> \[
> C(D)\longrightarrow C(O),\qquad [Q]\longmapsto[\mathbb Z\omega_Q+\mathbb Z].
> \]

Their p. 1 specifies primitive positive definite forms modulo \(\mathrm{SL}_2(\mathbb Z)\), and p. 2 expressly cites Cox Theorem 7.7. This corroborates the citation, but is not a reading of Cox’s book itself.

## Standing hypotheses

- \(\Delta\) is an arbitrary negative order discriminant: \(\Delta<0\) and \(\Delta\equiv0,1\pmod4\). It need not be fundamental.
- \(h(\Delta)\) is the order class number, equivalently the number of proper-equivalence classes of primitive positive definite binary quadratic forms of discriminant \(\Delta\). It is **not** the class number of the maximal order substituted for a nonmaximal order.
- The bounding parameter \(k\) is a positive integer. It is unrelated to the Lean field variable also named `k`.
- Although Fowler introduces a possible exceptional field \(K_*\) earlier in §2·2, Proposition 2·7 has no assumption \(\mathbb Q(\sqrt\Delta)\ne K_*\). Its proof uses unconditional Proposition 2·6 and the order class-number formula.

## Lean unfolded, with fixed-commit source locators

1. **Order.** [CMBranch.lean, lines 34–38](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CMBranch.lean#L34-L38): `IsImagQuadOrder k R` is the conjunction
   - `NumberField.IsTotallyComplex k`;
   - `Module.finrank ℚ k = 2`;
   - `R ≤ (integralClosure ℤ k).toSubring`;
   - `LeafQM.AV.conductor R ≠ 0`.
   Thus `k` is imaginary quadratic, and the unital subring `R` is a full finite-index subring of its integers.
2. **Conductor/index.** [QM/Leaves.lean, lines 147–149](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Leaves.lean#L147-L149): `conductor R` is the additive relative index of `R` in the integral closure of \(\mathbb Z\) in `k`, with the infinite-index convention returning zero. Containment plus nonzero index makes it the actual positive integer \(f=[\mathcal O_k:R]\).
3. **Discriminant.** [CMBranch.lean, lines 40–44](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CMBranch.lean#L40-L44): `orderDisc R = (conductor R : ℤ)^2 * NumberField.discr k`, hence \(\Delta_R=f^2d_k\).
4. **Picard group.** The dependency is pinned by [lake-manifest.json, lines 14–24](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/lake-manifest.json#L14-L24) to Mathlib commit `56a005855ea17e0b0958f73ec801ae140b0a1679`. At that revision:
   - [PicardGroup.lean, lines 75–78](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/PicardGroup.lean#L75-L78) defines invertibility through bijectivity of \(M^\vee\otimes_R M\to R\).
   - [Lines 427–430](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/PicardGroup.lean#L427-L430) define `CommRing.Pic R` as the invertible objects in the skeleton of the module category, with a size reduction. These are isomorphism classes of invertible modules, not all ideal classes in a noninvertible-ideal monoid.
   - [Lines 875–879](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/PicardGroup.lean#L875-L879) give `ClassGroup.equivPic` for **any domain**, not only a Dedekind domain.
   - [ClassGroup/Basic.lean, lines 86–90](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/ClassGroup/Basic.lean#L86-L90) defines `ClassGroup R` as invertible fractional ideals modulo principal fractional ideals. [Lines 180–182](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/ClassGroup/Basic.lean#L180-L182) permit any choice of fraction field.
   - Raw Picard-group source URL: https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/PicardGroup.lean
     SHA-256: `2cb65ea466b0639d59f0616ab807062de17f8ae727c8b39342728a6ddc075a88`.
   - Raw class-group source URL: https://raw.githubusercontent.com/leanprover-community/mathlib4/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/ClassGroup/Basic.lean
     SHA-256: `ea6b0b19938593430694875b5a5b556146ba12d142d51c75d3efb9b3bbebb917`.
5. **Whole statement.** [CMBranch.lean, lines 55–58](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CMBranch.lean#L55-L58) universally quantifies `k`, `R`, and natural `n`, assumes the order condition, `1 ≤ n`, and `Nat.card (CommRing.Pic R) ≤ n`, and concludes
   \[
   \sqrt{|\Delta_R|}\leq 2n^2\exp(21000n^2).
   \]

## Comparison, clause by clause

- Orders rather than fields: the print allows every order discriminant. The code’s finite-index subring is such an order; it does not require maximality. Finite index in a rank-two integer lattice gives a free rank-two integer lattice containing 1 and spanning the field.
- Discriminant: the basis/index formula identifies the trace discriminant with \(f^2d_k\), exactly the code’s `orderDisc`. It is negative and congruent to 0 or 1 modulo 4, so the print’s discriminant hypotheses follow. This dictionary is a mathematical step, not established merely by the docstring.
- Class number: for this domain the fraction field is `k`. Invertible modules represent invertible fractional ideals, modulo scalar multiplication; proper and invertible fractional ideals coincide for quadratic orders. The printed form/ideal correspondence therefore gives
  \[
  \operatorname{Nat.card}(\operatorname{CommRing.Pic}R)=h(\Delta_R).
  \]
  This is the order’s Picard group, not \(\operatorname{Pic}(\mathcal O_k)\). Proper equivalence is by \(\mathrm{SL}_2(\mathbb Z)\), not \(\mathrm{GL}_2(\mathbb Z)\); no conjugation quotient or factor of two is inserted.
- Finiteness: `Nat.card` would be zero for an infinite type, but the class group of an imaginary quadratic order is finite, by the primitive reduced-form correspondence. There is no additional finiteness assumption omitted from the mathematical statement.
- Parameter and boundary: Fowler’s positive integer \(k\) becomes the code’s natural `n` with `1 ≤ n`. Thus `n = 1` is included and `n = 0` is excluded exactly as in the print.
- Constants: the coefficient is \(2n^2\), and the exponential is \(\exp(21000n^2)\). There is no factor of \(\pi\), no change from \(|\Delta|^{1/2}\) to \(|\Delta|\), and no replacement of the exponential by a power at this leaf.
- No exceptional field: Proposition 2·5’s exclusion does not propagate to Proposition 2·7. The latter uses Proposition 2·6’s unconditional fundamental-discriminant bound; its proof separately treats \(D=-3,-4\), finishing with \(\sqrt{|\Delta|}\leq36k^2\leq2k^2e^{21000k^2}\). These are cases handled by the proof, not excluded hypotheses.
- Quantifiers: the extra variables are only a presentation of an order and its discriminant. The numerical result is uniform in the field and conductor, as the print requires.

## Verdict

**CONSEQUENCE**, in the checklist’s strict sense that a further dictionary step is named rather than silently treated as definitional: identify the finite-index quadratic order, its index-squared discriminant and its invertible-module Picard group with the printed order and order class number, then substitute \(\Delta=\Delta_R\), \(k=n\) in Proposition 2·7. The numerical statement itself is an exact match, not a weakening of an exceptional-field theorem and not a strengthening of a fundamental-discriminant-only theorem.

This report does not change the recorded `published`, `GLUE`, or `pending-review` classifications.

## False, incomplete or unclear

No false inequality or missing arithmetic hypothesis was found. The **unqualified citation of Cox’s precise book numbers remains unverified by direct book reading**: Theorem 7.7 is expressly cited and its correspondence stated in the read secondary sources; the book page itself, and the code’s Lemma 7.2 locator, were not read. The discriminant and class-number mathematics are supported independently above, so this locator limitation is not a numerical-statement failure.

## Not read

- Cox’s book itself: Lemma 7.2, Proposition 7.4, Theorem 7.7 and Theorem 7.24 were not page-read there.
- Fowler’s original references to Oesterlé, Goldfeld, Gross–Zagier and Tatuzawa, and their proofs, were not read. Fowler’s own Proposition 2·6 and Proposition 2·7 proof were read.
- Other sections of Fowler’s paper and the downstream CM branch proof are not certified.
- No compilation, build, repository edit, or formal construction of the order/form dictionary was performed.

## AI use

An AI language model performed the literature discovery, reading of the stated PDF pages, interpretation of the fixed-commit Lean definitions, comparison and report drafting. `pdftotext` extracted PDF text, PDF page reading checked displays, and SHA-256 hashing identified the downloaded copies. No human reading is claimed.

## Evidence

**AI-READ.** The journal statement was page-read at pp. 615–616. This report is not HUMAN-READ evidence and does not clear `pending-review` or make a maintainer classification ruling.
