Recorded from the statement-check sweep of 2026-11-18: an AI-READ report written by an AI agent that the project runs (no person checked it), against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`. It clears no flag.

---

# Statement check: `gaudronRemondThm14AnSS` (packet R5)

Gaudron–Rémond, *Polarisations et isogénies*, Théorème 1.4, against the Lean leaf
`ZInQ.SemistabAssembly.GaudronRemondThm14AnSS`. AI-READ (see the last two fields).

* **Field and commit**: `HDec.HSyn.OpenResearchLeaves65.gaudronRemondThm14AnSS`; Lean constant
  `ZInQ.SemistabAssembly.GaudronRemondThm14AnSS`, `ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean:252-257`.
  OPEN.md read at commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (entry `docs/one-proof/OPEN.md:404-416`;
  `docs/one-proof/kinds.tsv:18`: published, GLUE, long-pole, pending-review).

* **Edition, page, display**: É. Gaudron, G. Rémond, *Polarisations et isogénies*, Duke Math. J. 163 (2014), no. 11,
  2057–2108, DOI 10.1215/00127094-2782528. **Théorème 1.4, p. 2060.** Also read: α(g), κ(A) and the definition of
  h_F, p. 2058; the convention "couple d'isogénies", p. 2059; isogeny and degree, p. 2062 (§2). The normalization
  reference given on p. 2058 was followed to É. Gaudron, G. Rémond, *Théorème des périodes et degrés minimaux
  d'isogénies*, Comment. Math. Helv. 89 (2014), 343–403 (cited there as [GR1]): §2.3, Définition 2.1, pp. 351–352.

* **Copy**: author copy, i.e. the typeset journal PDF (Duke masthead, 52 pages = pp. 2057–2108, so PDF page n is printed
  page 2056 + n) posted on the first author's institutional page: https://lmbp.uca.fr/~gaudron/art13.pdf (fetched
  2026-11-18; 535 639 bytes; sha256 `6d62ddb8a0aa8f8b8f803d70060c6a26c7a6f2a00936b85867c830946cf3db12`). The page
  numbers above are therefore the Duke page numbers; no preprint mapping was needed. No arXiv version of this paper was
  found (an arXiv author search for Gaudron and Rémond returns only 1105.1230 and 1109.2812, which are other papers).
  [GR1]: typeset CMH PDF on the same page, https://lmbp.uca.fr/~gaudron/art11.pdf (61 pages = pp. 343–403, PDF page n
  is printed page 342 + n; 664 722 bytes; sha256 `d6b02e1adb9c8f2ab5a574bd8f8c301b5dfcfb8e14db3516bd2ae099b216ac54`).
  On the access date the host's TLS certificate had expired; both files are identified by their content (masthead,
  DOI, pagination) and by the hashes above. Byte identity with the publishers' own files was not checked.

* **Quote** (French, transcribed from the rendered pages):
  * p. 2060: « THÉORÈME 1.4. *Soient K une extension de k et A′ une variété abélienne définie sur k et isogène à A sur
    K. Il existe un couple de K-isogénies A ⇌ A′ de degré au plus κ(A).* »
  * p. 2058: « Soient donc k un corps de nombres et A une variété abélienne sur k de dimension g ≥ 1. Nous notons
    α(g) = 2^10 g^3 puis κ(A) = ((14g)^{64g^2} [k : ℚ] max(h_F(A), log[k : ℚ], 1)^2)^{α(g)} où h_F(A) est la hauteur
    de Faltings stable de A (avec la normalisation originale de Faltings, voir [GR1, paragraphe 2.3]). »
  * p. 2059: « φ : A ⇌ A′ désigne un couple d'isogénies φ1 : A → A′ et φ2 : A′ → A et l'on note
    deg φ = max(deg φ1, deg φ2). »
  * p. 2062: « Nous travaillons sur un corps K de caractéristique nulle. » … « Un morphisme φ : A → B est appelé
    isogénie lorsqu'il est surjectif de noyau fini. […] Le degré de φ, noté deg φ, est le cardinal de son noyau. »
  * [GR1] p. 351: « soit K une extension finie de k sur laquelle A est définie et admet réduction semi-abélienne.
    Soient π : 𝒜 → Spec 𝒪_K un modèle semi-abélien de A et ε : Spec 𝒪_K → 𝒜 sa section nulle. » The norm is
    ‖s‖² = (2π)^{-g} ∫_{A_σ} |s ∧ s̄|; « Définition 2.1. La hauteur h(A) de A est le degré d'Arakelov normalisé de
    ω̄_{𝒜/𝒪_K}. Cette définition est indépendante des choix de K et de 𝒜. »
  * [GR1] p. 352: « la définition originale h_F(A) de Faltings [Fa] ne fait pas apparaître le π dans la définition de
    la norme ci-dessus et donc on a h_F(A) = h(A) − (g/2) log π. »

* **Standing hypotheses**: p. 2058 fixes a number field k and an abelian variety A over k of dimension g ≥ 1 for the
  whole paper; h_F(A) is the stable Faltings height in Faltings' original normalization. §2 (p. 2062) works over a field
  of characteristic 0; morphisms are morphisms of abelian varieties (homomorphisms); an isogeny is a surjective
  morphism with finite kernel; its degree is the cardinality of the kernel. Through [GR1] §2.3: the stable height is
  computed over a finite extension where A has semi-abelian reduction, on a semi-abelian model, with
  ω = ε^*Ω^g, normalized Arakelov degree, metric (2π)^{-g}∫|s∧s̄| for h and 2^{-g}∫|s∧s̄| for h_F
  (h_F = h − (g/2) log π); independent of the field and the model. Théorème 1.4 has no semistability, polarization or
  simplicity hypothesis. "Réduction semi-abélienne" is not defined further on the pages read.

* **The Lean, unfolded** (paths and lines at the commit above):

  ```lean
  def GaudronRemondThm14AnSS : Prop :=
    ∀ (K : Type) [Field K] [NumberField K] (A B : PkgI3.AbVar K) (g : ℕ) (x : ℝ),
      A.dim = (g : WithBot ℕ∞) → IsAnStableHeightSS A x →
      (∃ φ : A.X ⟶ B.X, IsIsogeny φ) →
      (∃ φ : A.X ⟶ B.X, IsIsogeny φ ∧ (isogDeg φ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x) ∧
      (∃ ψ : B.X ⟶ A.X, IsIsogeny ψ ∧ (isogDeg ψ : ℝ) ≤ grKappa g (Module.finrank ℚ K) x)
  ```

  * `PkgI3.AbVar K` (`ZInQKernel/HDecomp/Objects.lean:162-168`): a group object in `K`-schemes, proper, smooth and
    geometrically integral. `A.dim` (`:181`): Krull dimension of the underlying space.
  * `IsIsogeny φ` (`ZInQKernel/HDecomp/Faltings/Leaves.lean:44-45`): `φ` is a homomorphism of group schemes, finite and
    surjective. `isogDeg φ` (`:48-49`): the number of `K̄`-points `P` of `A` with `φ(P) = 0` (`ptObj`, `:37-39`).
  * `grKappa g d x` (`:52-53`): `((14g)^(64g²) · d · max(max(x, log d), 1)²)^(1024g³)`.
  * `IsAnStableHeightSS A x` (`ZInQKernel/Contrib/OneProof/SemistablePrintedReadings.lean:227-233`): there are a number
    field `L ⊇ K`, a group model `𝒩` of `A_L` over `𝓞_L` (`GroupModel`, `ZInQKernel/HDecomp/Faltings/Models.lean:31-43`:
    smooth, separated, quasi-compact group scheme with generic fibre isomorphic to `A_L` as group schemes) and `g`, such
    that `𝒩` has the Néron mapping property (`GroupModel.IsNeronModel`, `ZInQKernel/HDecomp/Faltings/Height.lean:275-279`),
    `IsSemistablePrinted 𝒩` holds, `dim A = g`, and for a nonzero `η` in `printedDetLattice 𝒩 g`
    (`ZInQKernel/Contrib/OneProof/HeightDictionary.lean:91-94`: `⋀^g` of `ω = Γ(Spec 𝓞_L, e^*Ω¹)`,
    `ZInQKernel/Contrib/OneProof/HeightDictionary/Conormal.lean:313-314`) of finite index (`secIndex`,
    `ZInQKernel/HDecomp/Faltings/HodgeData.lean:69-70`: `#(ω/𝓞_L η)`) and reals `r τ` with `IsAnMetricSq 𝒩 τ η (r τ)`
    for every `τ : L → ℂ`, `x = (log #(ω/𝓞_L η) − ½ Σ_τ log r τ) / [L : ℚ]`.
  * `IsAnMetricSq` (`ZInQKernel/Contrib/OneProof/AnalyticStableHeight.lean:701-704`), through `IsAnFormMeasure`
    (`:694-696`) and `HasAnFormDensityAt` (`:679-690`): a finite Borel measure on `A_τ(ℂ)` (analytic topology `anTop`,
    `ZInQKernel/OneProof/H/TailZ.lean:875-877`; `anBorel`, `HeightDictionary.lean:48-49`) exists whose density in every
    holomorphic chart `φ` (`IsHolChart`, `AnalyticStableHeight.lean:168-178`) at `p`, when `η = l · df₁ ∧ ⋯ ∧ df_g` at
    the origin, is `|τ(l)|² · |det D(F_p ∘ φ⁻¹)(φ p)|²` relative to Lebesgue measure `dx₁dy₁⋯dx_gdy_g`; every such
    measure has total mass `r τ`. Since `(i/2) dz ∧ dz̄ = dx ∧ dy`, `r τ = (i/2)^g ∫ η ∧ η̄ = 2^{-g} ∫ |η ∧ η̄|`: Faltings'
    original metric, no factor `π`.
  * `IsSemistablePrinted 𝒩` (`SemistablePrintedReadings.lean:192-193`) is the conjunction of `IsSemistableGeomPrinted`
    (`:182-183`: at every maximal ideal `𝔭`, the identity component of `𝒩 ×_{𝓞_L} κ̄(𝔭)` is an extension of an abelian
    variety by a split torus, `HasSemiAbelianG0`, `:119-128`) and `IsSemistableResPrinted` (`:188-189`: the same over
    `k(𝔭)` with a torus that splits over an algebraic closure, `HasSemiAbelianG0Torus`, `:133-150`). Fibres:
    `geomFibre` (`ZInQKernel/OneProof/H/TailY.lean:96-98`), `resFibre`
    (`ZInQKernel/Contrib/OneProof/PrintedStableHeight.lean:566-568`).
  * No polarization and no polarization degree occur in the leaf or in Théorème 1.4 (polarizations enter only
    Théorème 1.1 and the proofs).

  In words: for a number field `K`, abelian varieties `A`, `B` over `K` with `g = dim A`, and `x` the stable Faltings
  height of `A` in the original normalization (computed on the Néron model over a number field `L ⊇ K` over which the
  identity components of all special fibres are semi-abelian), if some `K`-isogeny `A → B` exists, then there are
  `K`-isogenies `A → B` and `B → A`, each of degree at most `((14g)^{64g²} [K : ℚ] max(x, log[K : ℚ], 1)²)^{1024g³}`.

* **Comparison**, clause by clause:

  | clause | print | Lean | result |
  |---|---|---|---|
  | base field | k a number field (p. 2058) | `K` with `[NumberField K]` | same |
  | field of the isogenies | any extension K of k (Thm 1.4) | the base field `K` itself | direct specialization K := k |
  | A | abelian variety over k of dimension g ≥ 1 (p. 2058) | `A : PkgI3.AbVar K`, `A.dim = g`, `g : ℕ` | Lean also allows g = 0 (see below) |
  | A′ | abelian variety over k, isogenous to A over K | `B : PkgI3.AbVar K` with `∃ φ : A → B, IsIsogeny φ` | same (K = k) |
  | isogeny | surjective morphism of abelian varieties with finite kernel (p. 2062) | homomorphism, finite and surjective | same notion (a homomorphism of abelian varieties with finite kernel is finite; a finite morphism has finite kernel) |
  | degree | cardinality of the kernel, characteristic 0 (p. 2062) | `#ker φ(K̄)` | same (the kernel is étale in characteristic 0) |
  | conclusion | a pair φ1 : A → A′, φ2 : A′ → A with max(deg φ1, deg φ2) ≤ κ(A) (pp. 2059–2060) | `∃ φ : A → B` with degree ≤ κ, and `∃ ψ : B → A` with degree ≤ κ | same |
  | κ(A) | ((14g)^{64g²} [k : ℚ] max(h_F(A), log[k : ℚ], 1)²)^{α(g)}, α(g) = 2^10 g³ | `((14g)^(64g²) · [K : ℚ] · max(max(x, log[K : ℚ]), 1)²)^(1024g³)` | same constants (2^10 = 1024); [k : ℚ] is the degree of the field of definition, here `K` |
  | which height | h_F(A) of A (not of A′), stable | `x` attached to `A` | same |
  | normalization | original Faltings: 2^{-g}∫\|s∧s̄\| (p. 2058 and [GR1] p. 352) | `(i/2)^g ∫ η ∧ η̄ = 2^{-g}∫\|η∧η̄\|` | same; no metric-factor mismatch |
  | height recipe | normalized Arakelov degree of ε^*Ω^g of a semi-abelian model over a finite extension with semi-abelian reduction; independent of the choices ([GR1] p. 351) | the same degree for `ω = ⋀^g Γ(e^*Ω¹)` of the Néron model over `L`, divided by `[L : ℚ]` | same: the fibrewise identity component of that Néron model is a semi-abelian model with the same `e^*Ω^g` |
  | semistability | none on A; only inside the definition of the stable height | inside `IsAnStableHeightSS`, in hypothesis position: both the `k(𝔭)` and the geometric reading are required | the Lean condition implies the print's semi-abelian reduction; requiring both readings only narrows the witnesses `(L, 𝒩)`, so it cannot strengthen the leaf |

  **Boundary g = 0.** The print assumes g ≥ 1 throughout (p. 2058); the Lean quantifies over every `g : ℕ`. For g = 0 the
  Lean conclusion is true for a trivial reason: a 0-dimensional abelian variety over `K` is `Spec K`, so `B` (isogenous
  to `A`) is `Spec K`, every isogeny has degree 1, and `grKappa 0 d x = (…)^(1024·0³) = 1`. This instance is not
  covered by the print.

  **Semistability readings (the flag's open item).** Only the direction "Lean condition implies the print's semi-abelian
  reduction" matters, since the condition is in hypothesis position. The Lean condition (extension of an abelian variety
  by a torus, over `k(𝔭)` and over `κ̄(𝔭)`) gives the standard meaning; the "no G_a" reading also follows from it (an
  extension of an abelian variety by a torus contains no G_a). Independently of any reading, the leaf would remain a
  consequence of the print even if the Lean condition let a non-semistable Néron model through: `x` would then be the
  height relative to `L`, which is at least the stable height (GR use h_{F,K}(B₁) ≥ h_F(B₁) on p. 2102), and κ is
  nondecreasing in the height. So the open ga-rigidity reading cannot make this row stronger than the print.

* **Verdict**: **CONSEQUENCE.** For g ≥ 1 the Lean is the direct instance K := k of Théorème 1.4, with the same
  isogeny notion, degree, constants and height normalization (YES on that range). The one further step is the g = 0
  corner, outside the print's standing hypothesis "g ≥ 1": "an abelian variety of dimension 0 is Spec K, so every
  isogeny has degree 1 and κ = 1". It can be closed by adding `1 ≤ g` to the leaf (the manuscript applies Théorème 1.4
  only to positive-dimensional sources) or by proving that case.

* **False, incomplete or unclear**: not false, and not stronger than the print beyond the true g = 0 corner. No
  normalization mismatch: GR's h_F is the original normalization, as in the Lean. The identification of the Lean's `x`
  with h_F(A) rests on the faithfulness of the project's height definitions (packet R8: the analytic topology, the
  holomorphic charts, the lattice `printedDetLattice`) and on the independence of the stable height from the field and
  the model ([GR1] p. 351). These were checked here only for normalization and shape.

* **Not read**: the proofs of Théorème 1.4 (§§2–9), apart from pp. 2096–2098 and 2101–2102; Théorèmes 1.1–1.3 beyond
  their statements; Faltings (1983); Bost (Sém. Bourbaki 795); SGA 7 IX (the definition of semi-abelian reduction);
  Masser–Wüstholz; the publisher's own PDF; non-vacuity of `IsAnStableHeightSS`.

* **AI use**: the whole reading was done by an AI assistant (a large language model). It found the copies through the
  first author's publication list and an arXiv search, downloaded them, extracted the text (poppler `pdftotext`),
  rendered the cited pages to images (`pdftoppm`) to read the formulas, transcribed the quotes from those images, read
  the Lean source at the commit above, and wrote this comparison. No person has checked it.

* **Evidence**: AI-READ.
