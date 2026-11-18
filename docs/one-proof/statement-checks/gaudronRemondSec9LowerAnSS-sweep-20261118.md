Recorded from the statement-check sweep of 2026-11-18, against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: `gaudronRemondSec9LowerAnSS` (packet R5)

Gaudron–Rémond, *Polarisations et isogénies*, §9, proof of Lemme 9.1, p. 2098, against the Lean leaf
`ZInQ.BostGR9.GaudronRemondSec9LowerAnSS`. AI-READ (see the last two fields).

* **Field and commit**: `HDec.HSyn.OpenResearchLeaves65.gaudronRemondSec9LowerAnSS`; Lean constant
  `ZInQ.BostGR9.GaudronRemondSec9LowerAnSS`, `ZInQKernel/Contrib/OneProof/GaudronRemondSection9SS.lean:31-33`. OPEN.md
  read at commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (entry `docs/one-proof/OPEN.md:390-402`;
  `docs/one-proof/kinds.tsv:17`: published, GLUE, long-pole, pending-reading).

* **Edition, page, display**: É. Gaudron, G. Rémond, *Polarisations et isogénies* (GR14 below), Duke Math. J. 163
  (2014), no. 11, 2057–2108, DOI 10.1215/00127094-2782528. **§9, proof of Lemme 9.1, p. 2098** (the inequality and
  the normalization warning). The same inequality is used again on p. 2101 (proof of Lemme 9.4) and p. 2102 (proof of
  Corollaire 1.5). h_F is defined on p. 2058. The warning points to É. Gaudron, G. Rémond, *Théorème des périodes et
  degrés minimaux d'isogénies*, Comment. Math. Helv. 89 (2014), 343–403 (cited as [GR1]); read there: §2.3 with
  Définition 2.1, pp. 351–352, and Corollaire 8.4 with its proof, p. 400.

* **Copy**: author copy, i.e. the typeset journal PDF (Duke masthead, 52 pages = pp. 2057–2108, so PDF page n is printed
  page 2056 + n) posted on the first author's institutional page: https://lmbp.uca.fr/~gaudron/art13.pdf (fetched
  2026-11-18; 535 639 bytes; sha256 `6d62ddb8a0aa8f8b8f803d70060c6a26c7a6f2a00936b85867c830946cf3db12`). The page
  numbers are therefore the Duke page numbers. No arXiv version of this paper was found (an arXiv author search for
  Gaudron and Rémond returns only 1105.1230 and 1109.2812, which are other papers). [GR1]: typeset CMH PDF on the same
  page, https://lmbp.uca.fr/~gaudron/art11.pdf (61 pages = pp. 343–403, PDF page n is printed page 342 + n;
  664 722 bytes; sha256 `d6b02e1adb9c8f2ab5a574bd8f8c301b5dfcfb8e14db3516bd2ae099b216ac54`). On the access date the
  host's TLS certificate had expired; both files are identified by their content (masthead, DOI, pagination) and by
  the hashes above. Byte identity with the publishers' own files was not checked.

* **Quote** (French, transcribed from the rendered pages):
  * p. 2098, proof of Lemme 9.1: « Sinon nous utilisons la minoration de la hauteur de Faltings
    h_F(C_{i,j}) ≥ −(3/2) dim C_{i,j} due à Bost (voir [GR1, Corollaire 8.4] en prenant garde à la différence entre
    h(·) et h_F(·) rappelée au paragraphe 2.3). »
  * p. 2101, proof of Lemme 9.4: « en notant que h_F(A) ≥ −3g/2 (minoration de Bost). »
  * p. 2102: « Par la minoration de Bost utilisée ci-dessus, h_{F,K}(B₁) ≥ h_F(B₁) ≥ −(3/2) dim B₁ ≥ −(3/2)g. »
  * p. 2058: « h_F(A) est la hauteur de Faltings stable de A (avec la normalisation originale de Faltings, voir [GR1,
    paragraphe 2.3]). »
  * [GR1] p. 351: the norm defining h is ‖s‖² = (2π)^{-g} ∫_{A_σ} |s ∧ s̄|; « Définition 2.1. La hauteur h(A) de A est
    le degré d'Arakelov normalisé de ω̄_{𝒜/𝒪_K}. »
  * [GR1] p. 352: « la définition originale h_F(A) de Faltings [Fa] ne fait pas apparaître le π dans la définition de
    la norme ci-dessus et donc on a h_F(A) = h(A) − (g/2) log π. » and « Nous utiliserons en fait la variante avec
    h_F(·) obtenue en substituant et en majorant log(π√2) ≤ 3/2 ».
  * [GR1] p. 400: « Corollaire 8.4. *Pour toute variété abélienne A définie sur un corps de nombres, on a
    h(A) ≥ −(1/2)(dim A) log(2π).* »

* **The normalization warning, read.** It is the parenthesis « en prenant garde à la différence entre h(·) et h_F(·)
  rappelée au paragraphe 2.3 ». GR14 numbers its divisions as "parties" and has no paragraph 2.3; each of its other
  references to a "paragraphe 2.3" is to [GR1, paragraphe 2.3] (pp. 2058, 2062, 2096). The warning therefore refers to
  [GR1] §2.3, where h is defined with the metric (2π)^{-g}∫|s∧s̄| and h_F = h − (g/2) log π. It says that [GR1]
  Corollaire 8.4 is stated for h, and that the displayed bound is its translation to h_F. The displayed inequality is
  in h_F, which GR14 defines on p. 2058 as the stable height in Faltings' original normalization. The reading that the
  −3/2 bound concerns h, the (2π)^{-g} metric that the project calls Deligne's, is excluded by the print.

* **Standing hypotheses**: §9 (p. 2097) works under the hypotheses of the four main theorems: a number field k;
  abelian varieties A, A′ over k; an extension K of k over which A and A′ are isogenous; an abelian subvariety B of A
  defined over K; g = dim A (≥ 1 by p. 2058); k₁ the smallest extension of k over which all endomorphisms of A × A′ are
  defined; C_{i,j} abelian varieties simple over k₁, with A isogenous over k₁ to A‴ = ∏_i ∏_j C_{i,j}^{n_i m_{i,j}}.
  Heights: h_F is the stable height, original normalization (p. 2058); h_{F,K} is the height relative to K, without
  extension to a semistable model (p. 2062). [GR1] §2.3: the stable height is computed over a finite extension with
  semi-abelian reduction, on a semi-abelian model, and does not depend on these choices.

* **The Lean, unfolded** (paths and lines at the commit above):

  ```lean
  def GaudronRemondSec9LowerAnSS : Prop :=
    ∀ (K : Type) [Field K] [NumberField K] (A : PkgI3.AbVar K) (g : ℕ), A.dim = (g : WithBot ℕ∞) →
      ∀ x : ℝ, IsAnStableHeightSS A x → -(3 / 2) * (g : ℝ) ≤ x
  ```

  * `PkgI3.AbVar K` (`ZInQKernel/HDecomp/Objects.lean:162-168`): a group object in `K`-schemes, proper, smooth and
    geometrically integral. `A.dim` (`:181`): Krull dimension of the underlying space.
  * `IsAnStableHeightSS A x` (`ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean:227-233`): there are a number
    field `L ⊇ K`, a group model `𝒩` of `A_L` over `𝓞_L` (`GroupModel`, `ZInQKernel/HDecomp/Faltings/Models.lean:31-43`)
    with the Néron mapping property (`ZInQKernel/HDecomp/Faltings/Height.lean:275-279`) and `IsSemistablePrinted 𝒩`, a
    nonzero `η` of finite index in `ω = printedDetLattice 𝒩 g` (`ZInQKernel/Contrib/OneProof/HeightDictionary.lean:91-94`,
    `⋀^g Γ(Spec 𝓞_L, e^*Ω¹)`; index `secIndex`, `ZInQKernel/HDecomp/Faltings/HodgeData.lean:69-70`) and reals `r τ` with
    `IsAnMetricSq 𝒩 τ η (r τ)` for every `τ : L → ℂ`, such that `x = (log #(ω/𝓞_L η) − ½ Σ_τ log r τ) / [L : ℚ]`.
  * `IsAnMetricSq` (`ZInQKernel/Contrib/OneProof/AnalyticStableHeight.lean:701-704`, through `:694-696` and `:679-690`):
    `r τ` is the total mass of the measure on the complex manifold `A_τ(ℂ)` whose density in every holomorphic chart
    (`IsHolChart`, `:168-178`) is `|τ(l)|² |det D(F_p ∘ φ⁻¹)|²` relative to Lebesgue measure `dx₁dy₁⋯dx_gdy_g`, for
    `η = l · df₁ ∧ ⋯ ∧ df_g`. That is `(i/2)^g ∫ η ∧ η̄ = 2^{-g} ∫ |η ∧ η̄|`: Faltings' original metric, no factor `π`.
  * `IsSemistablePrinted 𝒩` (`SemistablePrintedReadings.lean:192-193`): at every maximal ideal, the identity component
    of the special fibre is an extension of an abelian variety by a torus, both over `κ̄(𝔭)` with a split torus
    (`:182-183`, `HasSemiAbelianG0` `:119-128`) and over `k(𝔭)` (`:188-189`, `HasSemiAbelianG0Torus` `:133-150`).
  * Context in the tree: `GaudronRemondSec9LowerAnSS` implies bost-gr9's `GaudronRemondSec9LowerAn`
    (`GaudronRemondSection9SS.lean:36-37`; that leaf is at `ZInQKernel/Contrib/OneProof/GaudronRemondSection9.lean:49-51`)
    and follows from the row it replaced, `BostLowerBoundAnSS` (`GaudronRemondSection9SS.lean:41-47`; the row at
    `SemistablePrintedReadings.lean:244-247`, `−(g/2) log 2π ≤ x + (g/2) log π`; conversion `deligne_bound_iff` and
    `half_log_two_pi_sq_lt`, `GaudronRemondSection9.lean:83-89, 104-108`).

  In words: for every abelian variety `A` of dimension `g` over a number field, the stable Faltings height of `A` in the
  original normalization (computed on the Néron model over a number field where the reduction is semi-abelian
  everywhere) is at least `−(3/2) g`.

* **Comparison**, clause by clause:

  | clause | print | Lean | result |
  |---|---|---|---|
  | generality | invoked as a general fact, « la minoration de la hauteur de Faltings … due à Bost », and applied to the C_{i,j} (simple over k₁, p. 2098), to A itself (p. 2101) and to B₁, an arbitrary abelian subvariety, possibly 0 (p. 2102) | every number field `K`, every `A/K` | same generality |
  | base field | number fields (k, k₁, finite extensions K) | `[NumberField K]` | same |
  | height | h_F, stable, original normalization (p. 2058) | `x` from `IsAnStableHeightSS`: `2^{-g}∫\|η∧η̄\|` on the Néron model over a semistable `L` | same normalization; no metric-factor mismatch |
  | constant | −(3/2) dim | `−(3/2) · g` with `g = dim A` | same |
  | dimension 0 | not excluded (B₁ on p. 2102 may be 0, and then both sides vanish) | `g = 0` allowed; then `x = 0` by the product formula | consistent |
  | semistability | none (stable height) | inside the height, hypothesis position; both readings required | cannot strengthen the leaf (the condition implies semi-abelian reduction; even a non-semistable witness would give a relative height ≥ the stable height, and the bound is a lower bound) |

  **Inside a proof.** The inequality is printed in a refereed paper, but as an attributed, unproved citation inside the
  proof of Lemme 9.1 (and used again on pp. 2101–2102). It is not a numbered result of GR14. Its printed proof is in
  [GR1]: the appendix proves Bost's theorem (Théorème 8.1) and derives Corollaire 8.4, stated for h. Against [GR1] the
  Lean is a CONSEQUENCE with two steps, both printed on [GR1] p. 352: `h_F = h − (g/2) log π`, and
  `log(π√2) ≤ 3/2`. Together they give `h_F(A) ≥ −(g/2) log 2π − (g/2) log π = −g log(π√2) ≥ −(3/2) g`.

  **Every reading supports the Lean.** Even if the −3/2 were read as a bound for h, the Lean's
  `h_F ≥ −(3/2) g` would still follow from the printed [GR1] Corollaire 8.4 with the §2.3 conversion, as above
  (`log(π√2) = 1.4913… < 3/2`).

* **Verdict**: **YES.** Against the cited place (GR14 p. 2098), the Lean is the printed inequality, in the same
  normalization and the same generality. The flag's open item, "the normalization warning on that page is unread", is
  now read: the warning concerns translating [GR1] Cor. 8.4 from h to h_F, and confirms the Faltings reading. For the
  reviewer: the theorem-level printed source is [GR1] Cor. 8.4 with §2.3, as a CONSEQUENCE with the steps named above.
  Note also that the stronger row this leaf replaced, `BostLowerBoundAnSS` (`−(g/2) log 2π ≤ x + (g/2) log π`), is
  exactly the inequality of [GR1] Corollaire 8.4, `h ≥ −(1/2)(dim A) log 2π`, once `x + (g/2) log π` is read as [GR1]'s
  `h` (the identity `h = h_F + (g/2) log π`, [GR1] p. 352). That corollary is printed with its proof (p. 400), although
  the manuscript does not cite [GR1].

* **False, incomplete or unclear**: not false, not stronger than the print, and no normalization mismatch. Only the
  provenance caveat remains (a cited statement inside a proof, with its proof in [GR1] and Bost); the existing flag text
  says this accurately. The identification of the Lean's `x` with h_F(A) rests on the faithfulness of the project's
  height definitions (packet R8) and on the independence of the stable height from the field and the model ([GR1]
  p. 351). These were checked here only for normalization and shape.

* **Not read**: Bost, Sém. Bourbaki 795 (Astérisque 237, 1996), and the notes [Bo3] and [Gr] cited in [GR1] §8; the
  proofs of [GR1] Théorème 8.1 and Lemmes 8.2–8.3 (only the statement of Corollaire 8.4 and its short proof, p. 400,
  were read); the rest of GR14 beyond pp. 2057–2062, 2096–2098 and 2101–2102; SGA 7 IX; the publisher's own PDFs;
  non-vacuity of `IsAnStableHeightSS`.

* **AI use**: the whole reading was done by an AI assistant (a large language model). It found the copies through the
  first author's publication list and an arXiv search, downloaded them, extracted the text (poppler `pdftotext`),
  rendered the cited pages to images (`pdftoppm`) to read the formulas, transcribed the quotes from those images, read
  the Lean source at the commit above, and wrote this comparison. No person has checked it.

* **Evidence**: AI-READ.
