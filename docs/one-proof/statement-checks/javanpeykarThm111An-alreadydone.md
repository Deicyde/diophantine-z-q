# Statement check: `javanpeykarThm111An` (alreadydone)

Recorded verbatim from [Deicyde #14](https://github.com/Deicyde/diophantine-z-q/issues/14#issuecomment-6955406000) (2026-11-17), an AI-READ report by alreadydone. Its Step B observation led to the correction of the row's semistability note in docs/one-proof/OPEN.md.

---

**Statement check report — `javanpeykarThm111An`** (packet R5; reply to the `Claiming reading R5` comment above)

## Field and commit

`javanpeykarThm111An` as listed in `docs/one-proof/OPEN.md` at `main` `b1615c9b1fb66c73104c96e825d237cd84ca3dba`
— row: kind **consequence**, strict **GLUE**, flags **reading-risk** + **long-pole**, tier **T4**, packet **R5**, 0 human readings;
bundle field `HDec.HSyn.OpenResearchLeaves53.javanpeykarThm111An`.

Lean block: `ZInQKernel.Contrib.OneProof.JavanpeykarAnRetype.JavanpeykarThm111An`
(`ZInQKernel/Contrib/OneProof/JavanpeykarAnRetype.lean:131`), which expands through `IsStableHeightBarAn`
(`JavanpeykarAnRetype.lean:90`) to `IsAnStableHeightSS`
(`ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean:227`), whose semistability clause is
`IsSemistablePrinted` (`SemistablePrintedReadings.lean:192` = geometric reading `:182` + `k(𝔭)` reading `:188`),
and whose constant is `javanpeykarBound g d = 13 * 10^6 * g * d^5`
(`ZInQKernel/HDecomp/LeafPush2/R18.lean:68`) with `belyiDegree X hB = Nat.find hB`
(`ZInQKernel/Contrib/OneProof/JavanpeykarDirect.lean:53`).

## Edition, page, display

Read: **arXiv:1403.6404v1** (submitted 25 Mar 2014; arXiv lists only v1 for this paper), §1.1 Theorem 1.1.1 and
§2.3 (plus the §2.1 normalisation sentence and the §2.2 Arakelov-degree display that §2.3 refers to).

Published pagination taken from the arXiv abs page's journal-ref: *Algebra and Number Theory* Vol. 8 (2014) No. 1,
pp. 89–140, DOI 10.2140/ant.2014.8.89 — consistent with the row's "Thm 1.1.1, p. 90" and "section 2.3, p. 98".
**I did not open the ANT typeset pages**, so the two page numbers themselves stay unadjudicated: I read an HTML
rendering that carries no page breaks, so even the row's "arXiv p. 1 / p. 9" markers are unverified at page level
(the content's *section* location is verified: Thm 1.1.1 is in §1.1, the height definition in §2.3).

## Copy

Web copy: `https://ar5iv.labs.arxiv.org/html/1403.6404` (LaTeXML rendering of the arXiv v1 LaTeX source), plus a
downloaded copy of the v1 PDF that this machine cannot render to text (no `pdftotext`/`pdftoppm`), so only the HTML
was read.

## Quote

(1) §1.1, preamble, defining the two sides:

> Let $\overline{\mathbb{Q}}$ be an algebraic closure of the field of rational numbers $\mathbb{Q}$. Let $X$ be a smooth projective connected curve over $\overline{\mathbb{Q}}$ of genus $g$. [...] Let $\deg_B(X)$ denote the Belyi degree of $X$, i.e., the minimal degree of a finite morphism $X\to\mathbb{P}^1_{\overline{\mathbb{Q}}}$ unramified over $\mathbb{P}^1_{\overline{\mathbb{Q}}}\backslash\{0,1,\infty\}$.

(2) §1.1, **Theorem 1.1.1** — first line of the display (the other three lines are quoted below):

> For any smooth projective connected curve $X$ over $\overline{\mathbb{Q}}$ of genus $g\geq 1$,
> $-\log(2\pi)g \leq h_{\mathrm{Fal}}(X) \leq 13\cdot 10^{6}\, g\, \deg_B(X)^{5}$
> $0 \leq e(X) \leq 3\cdot 10^{7}(g-1)\deg_B(X)^{5}$
> $0 \leq \Delta(X) \leq 5\cdot 10^{8}g^{2}\deg_B(X)^{5}$
> $-10^{8}g^{2}\deg_B(X)^{5} \leq \delta_{\mathrm{Fal}}(X) \leq 2\cdot 10^{8}g\deg_B(X)^{5}$.

(3) §2.3, the definition and the identification:

> Let $X$ be a smooth projective connected curve over $\overline{\mathbb{Q}}$ of genus $g\geq 1$. Let $K$ be a number field such that $X$ has a semi-stable minimal regular model $p:\mathcal{X}\to\mathrm{Spec}\, O_K$; see Theorems 10.1.8, 10.3.34.a and 10.4.3 in [29]. (Note that we implicitly chose an embedding $K\hookrightarrow\overline{\mathbb{Q}}$.)
>
> The *Faltings height* of $X$ is defined by
> $h_{\mathrm{Fal}}(X)=\dfrac{\widehat{\deg}\det p_\ast\omega_{\mathcal{X}/O_K}}{[K:\mathbb{Q}]}=\dfrac{\widehat{\deg}\det R^\cdot p_\ast\mathcal{O}_{\mathcal{X}}}{[K:\mathbb{Q}]},$
> where we endow the determinant of cohomology with the Faltings metric; see Section 2.1. **Note that $h_{\mathrm{Fal}}(X)$ coincides with the stable Faltings height of the Jacobian of $\mathcal{X}_K$; see [41, Lemme 3.2.1, Chapitre I].** Furthermore, we define [...] These invariants of $X$ are well-defined; see [36, Section 5.4].

(4) §2.2 and §2.1, the two ingredients the row's height display reproduces:

> $\widehat{\deg}(\mathcal{L})=\widehat{\deg}(\mathcal{L},\|\cdot\|)=\log\#(L/O_K s)-\sum_{\sigma:K\to\mathbb{C}}\log\|s\|_\sigma$

> We normalize this metric so that the metric on $\lambda(\Omega^1_X)=\det\mathrm{H}^0(X,\Omega^1_X)$ is induced by the hermitian inner product on $\mathrm{H}^0(X,\Omega^1_X)$ given above.

(5) §2.2, Def. 2.2.1, the print's meaning of "semi-stable" and "minimal":

> We say that $\mathcal{X}$ is semi-stable (or nodal) over $S$ if every geometric fibre of $\mathcal{X}$ over $S$ is reduced and has only ordinary double singularities; see [29, Definition 10.3.1]. We say that $\mathcal{X}$ is (relatively) minimal if it does not contain any exceptional divisor; see [29, Definition 9.3.12].

Bibliography, as printed: [29] Q. Liu, *Algebraic geometry and arithmetic curves*, Oxford Graduate Texts in
Mathematics 6, 2002. [36] L. Moret-Bailly, *Hauteurs et classes de Chern sur les surfaces arithmétiques*,
Astérisque 183 (1990). [41] L. Szpiro (ed.), *Séminaire sur les pinceaux arithmétiques: la conjecture de Mordell*,
Astérisque 127 (1985).

## Standing hypotheses

* §1.1 fixes $\overline{\mathbb{Q}}$ once, as *an* algebraic closure of $\mathbb{Q}$; $X$ is smooth, **projective**,
  connected, of genus $g$; $\deg_B(X)$ is a *minimum* over finite morphisms to $\mathbb{P}^1_{\overline{\mathbb{Q}}}$
  unramified off $\{0,1,\infty\}$.
* §2.3 restricts to $g \geq 1$, and every invariant is defined only after choosing a number field $K$ over which
  $X$ has a semi-stable **minimal regular** model $\mathcal{X}/O_K$, with an implicit embedding $K \hookrightarrow
  \overline{\mathbb{Q}}$; existence of such a $K$ and model is cited to Liu ([29], Thms 10.1.8, 10.3.34.a, 10.4.3).
* "Semi-stable" and "minimal" are Def. 2.2.1's (quote 5), i.e. properties of the **curve model**: reduced geometric
  fibres with only ordinary double points, no exceptional divisor.
* The archimedean side is fixed by §2.1's normalisation sentence (quote 4, second block) applied to the Faltings
  metric on the determinant of cohomology; the non-archimedean side by §2.2's Arakelov degree (quote 4, first block).
* Independence of $K$ and of the model is asserted, not proved: "These invariants of $X$ are well-defined; see
  [36, Section 5.4]."

## Comparison, clause by clause

1. **Ground field.** Print: a curve over $\overline{\mathbb{Q}}$ (any algebraic closure of $\mathbb{Q}$). Lean:
   `(Kbar : Type) [Field Kbar] [Algebra ℚ Kbar] [IsAlgClosure ℚ Kbar]`, `X : Over (Spec (CommRingCat.of Kbar))`.
   Same; nothing is fixed to a particular closure.
2. **Curve hypotheses.** Print: "smooth projective connected curve", i.e. the row's `[IsCurve X]` (kernel: smooth,
   proper, geometrically connected — over an algebraically closed field "connected" and "geometrically connected"
   agree) plus the row's explicit projectivity hypothesis `(∃ n, Finite n, i : X ⟶ ℙ(n), IsClosedImmersion i ∧
   i ≫ ℙ(n) ↘ Spec Kbar = X.hom)` and `[IsIntegral X.left]`. The closed-immersion-into-$\mathbb{P}^n$ form is the
   usual meaning of "projective" for a scheme over a field, so this clause does not exceed the print; integrality
   is implied by smooth + connected over an algebraically closed field.
3. **Genus.** Print: $g \geq 1$. Lean: `1 ≤ genusK X` (`genusK X = Nat.dim ℚ (H⁰(X, Ω¹))`, the print's genus for a
   smooth projective curve). Match.
4. **Belyi degree.** Print: $\deg_B(X)$ = *minimal* degree of a finite $X \to \mathbb{P}^1_{\overline{\mathbb{Q}}}$
   unramified over $\mathbb{P}^1 \backslash \{0,1,\infty\}$. Lean: `JavanpeykarDirect.belyiDegree X hB = Nat.find hB`
   with `HasBelyiMapOfDegree X d := 0 < d ∧ ∃ β : X ⟶ P1 k, IsBelyiMap X β d` (`JavanpeykarDirect.lean:45`).
   This is the minimum, as printed; the extra `0 < d` is annotated in the code as removing nothing and as making the
   minimum the print's. The row keeps `hB` as a hypothesis (existence of one Belyi map), which the print gets for
   free from Belyi's theorem over $\overline{\mathbb{Q}}$ — a weakening of the Lean row, not a strengthening.
5. **The constant and the shape.** Print: $13\cdot 10^{6}\, g\, \deg_B(X)^5$. Lean:
   `javanpeykarBound g d = 13 * 10 ^ 6 * g * d ^ 5`. Constant, exponent and factor order match exactly.
   The row keeps only the upper bound of the first line: it drops the lower bound $-\log(2\pi)g$ and the lines for
   $e(X)$, $\Delta(X)$, $\delta_{\mathrm{Fal}}(X)$, so it is a **direct instance** of the printed display in that
   respect.
6. **The height itself — this is where the row and the print are not the same sentence.** The print's $h_{\mathrm{Fal}}(X)$
   (quote 3) is the Arakelov degree, divided by $[K:\mathbb{Q}]$, of $\det p_*\omega_{\mathcal{X}/O_K}$ for a
   semi-stable **minimal regular model of the curve**. The row never defines a height of a curve; it uses
   `IsStableHeightBarAn W x`, i.e. $x$ is read off `IsAnStableHeightSS` from a **Néron model $\mathcal{N}$ of the
   abelian variety $W$** (which the row requires to represent $\mathrm{Pic}^0_X$ via `repW`, with the tensor-product
   compatibility `PicardTensorCompatible`):
   `x = (Real.log (secIndex (printedDetLattice 𝒩 g) eta) - (1/2) * ∑ τ, Real.log (r τ)) / Module.finrank ℚ L`
   with `IsAnMetricSq 𝒩 τ eta (r τ)`. Term by term that display is §2.2's
   $\log\#(L/O_K s) - \sum_\sigma \log\|s\|_\sigma$, divided by $[K:\mathbb{Q}]$, with $r_\sigma = \|s\|_\sigma^2$
   (hence the factor $\tfrac12$) and the summation over $L \to +\ast \mathbb{C}$ = the embeddings $\sigma:K\to\mathbb{C}$;
   the metric is the Faltings metric normalised as in §2.1 (the code's density is the print's $(i/2)^g$-normalised
   hermitian form). So the **form** of the height matches exactly; the **object** it is computed on differs
   (Jacobian's Néron model, not the curve's minimal regular model), and that shift is justified *inside the paper*
   by the bolded sentence of quote 3, "Note that $h_{\mathrm{Fal}}(X)$ coincides with the stable Faltings height of the
   Jacobian of $\mathcal{X}_K$" — the delegation to [41, Lemme 3.2.1, Chapitre I] is the paper's own, not the row's.
7. **Semistability.** The print's clause (quote 5) is a property of the **curve's** model: geometric fibres reduced
   with ordinary double points, model minimal. The row's clause `IsSemistablePrinted 𝒩` is a property of the
   **Jacobian's Néron model**: at every maximal $\mathfrak{p}$ of $O_L$, the identity component of the geometric
   special fibre (and, in the second reading, of the $k(\mathfrak{p})$ special fibre) is an extension of an abelian
   variety by a torus. These are not the same sentence, and "as printed" in `OPEN.md`'s note is best read as
   "the printed notion, transported": the equivalence (semi-stable curve model $\Rightarrow$ the Jacobian's Néron
   model has semi-abelian identity components, and the converse) is a theorem about Néron models, not a definition
   in either text.
8. **Quantifier shape / well-definedness.** The print asserts one inequality about one number $h_{\mathrm{Fal}}(X)$,
   after declaring the invariants well-defined ("see [36, Section 5.4]"). The row instead says: for **every** $x$
   that some choice of number field $L \subseteq \overline{\mathbb{Q}}$, model $V$ of $W$ over $L$, Néron model and
   determinant section witnesses as the height, $x \le$ bound. That universal reading of a witnessed predicate is
   exactly the print's independence-of-choice statement, again delegated by the print to [36, §5.4].

## Verdict

**CONSEQUENCE.** The Lean row follows from the printed Theorem 1.1.1 (quote 2, first line) in two named steps, both
of which the paper itself states and cites rather than proves:

* **Step A (in the source, cited to [41]).** Replace $h_{\mathrm{Fal}}(X)$ by the stable Faltings height of
  $\mathrm{Jac}(X_K)$ — the bolded sentence of §2.3 (quote 3). This licenses the row's choice to state the bound
  about the Jacobian's height.
* **Step B (outside the source).** Replace the print's *curve-model* semi-stability (Def. 2.2.1) by the row's
  *Néron-model* semi-stability `IsSemistablePrinted`. The name I would give for this step is
  Bosch–Lütkebohmert–Raynaud, *Néron Models* (Ergebnisse der Mathematik 24), Chap. IX, §5–§6: for a curve over the
  fraction field of a DVR whose minimal regular model has reduced geometric fibres with ordinary double points, the
  identity component of the special fibre of the Jacobian's Néron model is an extension of an abelian variety by a
  torus (the toric rank being the loop number of the dual graph), and conversely semi-abelian reduction of the
  Jacobian is what Grothendieck's monodromy criterion calls semi-stable reduction. **I did not read BLR**; the
  chapter reference is given as the place to look, not as a verified locator, and I did not check theorem numbers.
* Additionally, the row's $\forall x$ over a *witnessed* height predicate rests on the print's own
  "these invariants are well-defined; see [36, Section 5.4]" — i.e. on Moret-Bailly, Astérisque 183 §5.4, unread
  (quote 3, last sentence).

No mismatch found: the row is not stronger than the print in constant, exponent, genus bound, ground field, Belyi
degree, or metric normalisation, and it drops three of the four printed inequalities plus the lower bound.

## False, incomplete or unclear

Not false as far as I can tell. Incomplete only in justification: the composite is licensed by §2.3's own sentence
plus one external equivalence (Step B) and one external well-definedness statement ([36, §5.4]). The row's flag
`reading-risk: R3'` (the `IsHolChart` atlas being the complex structure of $A_\tau(\mathbb{C})^{\mathrm{an}}$, and
the density being the print's normalisation) is a **Lean-internal faithfulness** question — §2.1's single
normalisation sentence is the whole of what the print says there, and it does not settle whether the kernel's atlas
predicate denotes that metric; that belongs to packet R8, not to this reading.

## Not read

The proof of Theorem 1.1.1 (§4.5–§4.6 and all of §3–§6); the rest of §2 beyond the quoted displays; [29] (Liu)
Chs. 9–10, [36] (Moret-Bailly) §5.4, [41] (Astérisque 127) Lemme 3.2.1 Chap. I; BLR Ch. IX; the ANT typeset pages;
the kernel's own definitions of `IsCurve`, `genusK`, `IsBelyiMap`, `printedDetLattice`, `secIndex`, `IsAnMetricSq`
(only their types and the docstrings were read, so this report checks the row against the paper, not the row's
dictionary against the literature — that is R8's job).

## AI use

This entire reading was produced by an AI agent (Qoder Desktop, working for the account holder): WebFetch of the
ar5iv HTML rendering of arXiv:1403.6404v1, local text search of the fetched copy, and the reading of the Lean
sources quoted above. The account holder did not open the paper during this reading. Quotation marks indicate text
transcribed from the LaTeXML rendering, which is generated from the arXiv v1 LaTeX source; the rendering is known to
mangle display layout, so the four lines of Theorem 1.1.1's array were checked against the surrounding prose and
against the code's constants rather than against a page image.

## Evidence

**AI-READ** (per `docs/one-proof/STATEMENT-CHECKS.md`: recorded, never counted as a human reading).

**For a second reader with the ANT print:** the two things worth confirming by eye are (i) whether the typeset
Theorem 1.1.1 on p. 90 is word-for-word the v1 statement quoted above, and (ii) the page of §2.3's "Note that
$h_{\mathrm{Fal}}(X)$ coincides with..." sentence, which is the sentence this verdict turns on.
