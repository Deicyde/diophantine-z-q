Recorded from the statement-check sweep of 2026-11-18, against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: cmHeight62

**Verdict: CONSEQUENCE.** The Lean inequality follows from the general elliptic discriminant formula in the normalization of the printed equation (6.2), after converting a proper smooth group model to everywhere good reduction and supplying a metrized-model witness for the defining infimum. There is no missing CM assumption. A citation/normalization warning is essential: Silverman’s own printed discriminant prefactor is reciprocal to that in (6.2), so Silverman’s display cannot be copied unchanged as an identically normalized formula.

Checked on 2026-11-18. This compares the mathematical statement and its definitions; it does not construct the comparison in Lean or certify the entire stable-height formalization.

## Field and commit

- Field: `HDec.HSyn.OpenResearchLeaves65.cmHeight62`.
- Proposition: `HDec.CMBranch.CMHeight62`.
- Commit of the code, checklist and open list read: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
- Open-list entry: [OPEN.md, lines 278–290](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L278-L290).
- Field binding: [TailZ91.lean, lines 68–69](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/OneProof/H/TailZ91.lean#L68-L69).
- The requested checklist and [AUDIT.md, item 2](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/reviews/height-replacement/height/AUDIT.md#L19) were read. The previous audit was treated as a claim, not as independent source evidence.

## Edition, page, display

Adrian Barquero-Sanchez, Lindsay Cadwallader, Olivia Cannon, Tyler Genao and Riad Masri, *Faltings heights of CM elliptic curves and special Gamma values*, *Research in Number Theory* **3** (2017), article **13**, DOI [10.1007/s40993-017-0077-7](https://doi.org/10.1007/s40993-017-0077-7).

- **Equation (6.2): p. 14 of 16**, PDF page 14. The surrounding Proposition 6.1 and its period convention (6.1) start on **p. 13**.
- **Original differential metric:** §1, **p. 1**. Definition of the stable height and Deligne shift, display **(1.2)**: **p. 2**.
- Dedekind eta and the invariant function \(F\), display **(3.2)**: **p. 5**.
- Proof of Theorem 1.3, including potential good reduction and removal of the finite discriminant term: **p. 15**.
- The same numbered journal edition was also read in the author-posted copy linked by the previous audit. Pages 1, 2, 6, 13, 14 and 15 agree after whitespace normalization between the two extracted texts; the PDF bytes differ.

**Numbering map:** the final journal edition itself was read, so (6.2), (6.1), (3.2) and (1.2) have their journal numbers, not inferred preprint numbers. An arXiv edition of this particular paper was not identified: a public title query returned no entry, and the author’s publication list supplied a PDF/journal link rather than an arXiv link for it. No claim of archive-wide absence or invented arXiv-to-journal numbering is made.

For the **general, non-CM scope**, the publisher’s legitimate preview of Joseph H. Silverman, *Heights and Elliptic Curves*, in Cornell–Silverman (eds.), *Arithmetic Geometry* (1986), Chapter X, pp. **253–254**, was read: **Proposition 1.1** and **Remark 1.2**, printed p. **254**, preview PDF page **2**. This is the original reference cited in (6.2).

A second printed check is Steffen Löbrich, *A Gap in the Spectrum of the Faltings Height*, *Journal de Théorie des Nombres de Bordeaux* **29** (2017), 289–305: §2, **Definition 2.3 and Remark 2.1, p. 292**, and **Proposition 2.1, p. 293**. Its height uses Deligne’s normalization, whose shift must be removed.

## Copy

Open-access publisher PDF from Springer; the author-posted journal copy as a cross-check. Silverman’s two-page preview was downloaded from the preview link on the publisher’s chapter page, not from an unauthorized book mirror. Löbrich’s journal PDF came from Numdam. The full Silverman chapter was not obtained; its two-page preview was sufficient to read Proposition 1.1 and its scope.

### Source URLs and SHA-256

1. **Barquero-Sanchez et al., journal PDF, primary copy**
   - URL: https://link.springer.com/content/pdf/10.1007/s40993-017-0077-7.pdf
   - SHA-256: `8752beb7b997e31a1f8a5e3ec5a13f5d8c0b675f7862305f1a873cd4b9f5ec8d`
   - 16 PDF pages; 657,548 bytes.
2. **Author-posted copy of the journal article**
   - URL: https://tylergenao.com/wp-content/uploads/2017/09/faltings-heights-of-cm-elliptic-curves-and-special-gamma-values.pdf
   - SHA-256: `f91cc2017dcc82dbc55d641d397c8b2bb5fc15205b1377cdaae8bdbbd7fc14a6`
   - 16 PDF pages; 585,415 bytes.
3. **Silverman, publisher preview of Chapter X**
   - URL: https://page-one.springer.com/pdf/preview/10.1007/978-1-4613-8655-1_10
   - SHA-256: `82fbf5b33ac6243188afb8057d73f3ac06258f344e8bfb95cb06edcd279faa9f`
   - 2 PDF pages, printed pp. 253–254; 347,725 bytes.
   - Chapter page: https://link.springer.com/chapter/10.1007/978-1-4613-8655-1_10
4. **Löbrich, published article**
   - URL: https://www.numdam.org/item/10.5802/jtnb.980.pdf
   - SHA-256: `4de47448a77cb292a88018e2233b64eb973ba47d04a367ab241c52dddff36169`
   - 18 PDF pages including the cover; printed pp. 292–293 are PDF pages 5–6.
5. **Geometric dictionary support: Stein factorization**
   - URL: https://stacks.math.columbia.edu/tag/03H0
   - Theorem **37.53.4**, tag **03H0**, “Stein factorization; Noetherian case”. Read as a numbered theorem on the official site, not assigned a PDF page number.
   - SHA-256 of the downloaded HTML: `dac42f128e663313c962f5a814bd8b7623d433acef47513a8630ca60283bfc45`.

## Quote

Short transcription from Barquero-Sanchez et al., p. 14; mathematical glyphs and superscripts are restored.

> “Moreover, let
> \[\Delta(z):=(2\pi)^{12}\eta(z)^{24}\]
> be the discriminant function. Then Silverman [16, Proposition 1.1] proved that the Faltings height of \(E/L\) is given by”
> \[
> h_{\mathrm{Fal}}(E/L)
> =\frac{\log(N_{L/\mathbb Q}(\Delta_{E/L}))}{12[L:\mathbb Q]}
> -\frac{1}{12[L:\mathbb Q]}
> \sum_{\sigma\in\operatorname{Hom}(L,\mathbb C)}
> \log\bigl(\operatorname{Im}(z_\sigma)^6|\Delta(z_\sigma)|\bigr).
> \tag{6.2}
> \]

On p. 1 the actual metric in the height definition is
\[
\|\omega\|_\sigma^2=\frac{i}{2}\int_{E^\sigma(\mathbb C)}\omega^\sigma\wedge\overline{\omega^\sigma},
\]
and the height is the finite differential-index term divided by \([L:\mathbb Q]\), minus \(1/(2[L:\mathbb Q])\) times the sum of logarithms of these squared norms. On p. 2, (1.2) states
\[
h_{\mathrm{geom}}(E)=h_{\mathrm{Fal}}^{\mathrm{stab}}(E/L)+\tfrac12\log\pi.
\]

Silverman, p. 254, lists **“\(E/K\) an elliptic curve”**, with no CM assumption, and states:

> “**Proposition 1.1.** With notation as above, the height of \(E/K\) is given by the formula”
> \[
> [K:\mathbb Q]h_S(E/K)=\frac1{12}
> \left\{\log|N_{K/\mathbb Q}\Delta_{E/K}|-
> \sum_{v\in M_K^\infty}n_v\log\bigl(|\Delta_S(\tau_v)|(\operatorname{Im}\tau_v)^6\bigr)\right\},
> \]
> with \(n_v=1\) at real places and \(n_v=2\) at complex places.

The added subscript \(S\) here distinguishes Silverman’s convention from the convention of (6.2); it is not in Silverman’s notation. Silverman’s **printed definition** is
\[
\Delta_S(\tau)=(2\pi)^{-12}q_\tau\prod_{n\geq1}(1-q_\tau^n)^{24},
\]
not \((2\pi)^{12}\eta(\tau)^{24}\). Remark 1.2(1) says the height in Silverman’s proposition is not the stabilized height; Remark 1.2(2) says the displayed quantity is \(\mathrm{SL}_2(\mathbb Z)\)-invariant and independent of period choice.

Löbrich’s Definition 2.3, p. 292, gives (6.2)’s right-hand side **plus** \(\tfrac12\log\pi\) for a general elliptic curve over a number field. Its following remark states:

> “Faltings’s original definition [4] does not have the \(\frac12\log\pi\)-term.”

Proposition 2.1(iii), p. 293, states:

> “\(h_0(E/K)=0\) if and only if \(E/K\) has everywhere good reduction.”

## Standing hypotheses

- The paper’s §1 height definition is for an elliptic curve over a number field, with its Néron differential lattice and **Faltings’ original \(i/2\) metric**. It is not Deligne’s geometric height.
- Proposition **6.1**, surrounding (6.2), is a **CM** proposition and assumes coefficients of a Weierstrass equation lie in \(\mathbb Q(j(E))\). Its conclusion is a **class-group average**. Those hypotheses are used later on p. 14 to replace an embedding average by a class-group average. They must not be silently dropped if using that conclusion.
- Equation **(6.2)** is the **embedding-average discriminant formula** recalled from Silverman, not the CM class-group formula. Silverman’s own Proposition 1.1 is explicitly for a general elliptic curve; Löbrich §2 also states the general formula after a specified normalization change.
- The finite term is the logarithm of the norm of the **minimal discriminant ideal**, not the logarithm of an order discriminant or of a chosen, potentially nonminimal Weierstrass discriminant.
- Good reduction everywhere makes that ideal \(\mathcal O_L\), hence the finite term zero. Merely semistable reduction would not suffice to omit the finite term, since multiplicative fibres can contribute.

## Lean unfolded, with fixed-commit source locators

1. **Elliptic curve.** [G0StableBC.lean, line 18](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/HeightBC/G0StableBC.lean#L18) makes `ZInQ.DefFaltings.AbVar K` an alias of `PkgI3.AbVar K`. [Objects.lean, lines 160–181](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Objects.lean#L160-L181) defines a group object over `Spec K` that is proper, smooth and geometrically integral, with `dim` the Krull dimension. The condition `E.dim = 1` selects an elliptic curve; its group unit supplies the rational origin.
2. **Field extension and model.** [Models.lean, lines 24–45](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Faltings/Models.lean#L24-L45): `GroupModel E L` contains a group scheme `G` over `Spec (𝓞 L)`, with smoothness, separatedness and quasi-compactness, together with a group-scheme identification of its generic fibre with `E.baseChange L`. The extra `IsProper 𝒢.G.hom` in the checked leaf applies to the **structure morphism over the integers**, not just to the generic fibre. Both `K` and `L` are number fields and `[Algebra K L]` gives the inclusion; it is automatically a finite extension of fields in this situation.
3. **Period predicate.** [CMBranch.lean, lines 66–71](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CMBranch.lean#L66-L71): `IsPeriodAt E σ τ` supplies a lattice and a uniformizing map from `Fin 1 → ℂ`, whose kernel is exactly the lattice, and a nonzero scalar `c` making it \(c(\mathbb Z+\tau\mathbb Z)\).
   - [LeafPush2/R22.lean, lines 25–56](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/LeafPush2/R22.lean#L25-L56) defines the target as complex points of the base-changed variety and requires a surjective group homomorphism, the exact kernel, open preimages of Zariski opens and holomorphy of regular functions on those preimages.
   - The positivity assumption \(\operatorname{Im}\tau>0\) and `c ≠ 0` ensure the displayed lattice has rank two and positive covolume. Thus this is a full period lattice, not an arbitrary subgroup or an isogeny lattice.
   - [LPrefix.lean, lines 5322–5329](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/OneProof/H/LPrefix.lean#L5322-L5329) shows `LeafAdopt.abVarEquiv` preserves the underlying variety and dimension.
4. **Summand.** [Arith.lean, lines 16–27](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CMBranch/Arith.lean#L16-L27):
   \[
   \operatorname{discAn}(\tau)=(2\pi)^{12}\eta(\tau)^{24},\qquad
   \operatorname{summand62}(\tau)=-\frac1{12}\log\bigl(|\operatorname{discAn}(\tau)|(\operatorname{Im}\tau)^6\bigr).
   \]
   The complex norm is absolute value, **not** its square. [Lines 79–96](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CMBranch/Arith.lean#L79-L96) contain the expansion, for positive imaginary part,
   \[
   -\log(2\pi)+\frac\pi6 y-\tfrac12\log y
   -2\sum_{n\geq1}\log|1-e^{2\pi in\tau}|.
   \]
5. **Metric and averaging.** [HodgeData.lean, lines 266–269](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Faltings/HodgeData.lean#L266-L269) defines `torusMetricSq Λ a = ‖a‖^2 * covolume Λ`, the positive \((i/2)^g\) metric. [Lines 338–350 and 364–398](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Faltings/HodgeData.lean#L338-L398) define the actual period lattices, differential coefficient maps, their norms, and
   \[
   \operatorname{modelHeight}=\frac{\deg\overline\omega}{[L:\mathbb Q]}
   =\frac{\log\#(\omega/\mathcal O_L s)-\tfrac12\sum_\sigma\log\|s\|_\sigma^2}{[L:\mathbb Q]}.
   \]
   For a normalized lattice \(\mathbb Z+\tau\mathbb Z\), \(\|dz\|^2=y\). There is no division by \(\pi\) in this metric and no added constant in `modelHeight`.
6. **Hodge lattice and model compatibility.** [Models.lean, lines 89–117 and 151–167](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Faltings/Models.lean#L89-L167) build the cotangent space, local differential lattices, their intersection and top exterior-power lattice. [Height.lean, lines 29–41](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Faltings/Height.lean#L29-L41) requires a `MetrizedModel` to use that lattice and genuine analytic uniformizations, with the coefficient map identified by the derivative determinant. Its periods and metric are not unconstrained height parameters.
7. **Stable height is an infimum.** [Height.lean, lines 43–73](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Faltings/Height.lean#L43-L73) defines
   \[
   \operatorname{stableFaltingsHeight}(E)=\inf_{L',g,M}\operatorname{modelHeight}(M)\in\mathrm{EReal}
   \]
   over number fields with a `K`-algebra structure and compatible metrized models. The lemma `stableFaltingsHeight_le`, lines 71–73, bounds this infimum by **any one actual metrized model**. The Deligne variant, lines 62–65, instead adds \((g/2)\log\pi\) to each model height; it is not the function used by the checked leaf.
8. **Whole statement.** [CMBranch.lean, lines 81–87](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CMBranch.lean#L81-L87) quantifies all number fields `K,L`, all dimension-one `E/K`, every such proper group model over `𝓞 L`, and every valid period choice at every \(\sigma:L\to\mathbb C\). It concludes
   \[
   \operatorname{stableFaltingsHeight}(E)
   \leq\frac1{[L:\mathbb Q]}\sum_{\sigma:L\hookrightarrow\mathbb C}\operatorname{summand62}(\tau_\sigma).
   \]
   Its left side is in `EReal`; it does not use a default real value for an infinite height.

## Comparison, clause by clause

### Scope: general elliptic curves, not a CM-only height formula

The Lean has **no CM hypothesis**. This would be too broad if it asserted Proposition 6.1’s class-group average, or Theorem 1.3’s special Gamma-value formula. It asserts neither. It uses (6.2)’s embedding-average discriminant formula.

Silverman’s original Proposition 1.1, including its standing variable list, was independently read: its curve is an arbitrary elliptic curve over a number field. Löbrich’s Definition 2.3 supplies the same general formula in Deligne normalization; removing its explicitly stated \(\tfrac12\log\pi\) shift gives (6.2). This resolves the scope issue without assuming that hypotheses of an enclosing CM proposition can automatically be ignored.

The restriction to \(\mathbb Q(j(E))\)-coefficients first matters when p. 14 regroups the sum over embeddings by their restrictions to \(\mathbb Q(j(E))\), and then uses CM theory to replace that sum by the order class-group sum. None of those regrouping steps appears in `CMHeight62`.

### Proper group model versus good reduction

`GroupModel` already asserts **smoothness** over \(\mathcal O_L\). Adding properness gives a smooth proper model of \(E_L\) with a group law and geometrically connected generic fibre. Over the normal Dedekind base \(\operatorname{Spec}\mathcal O_L\), this has geometrically connected fibres and is an abelian scheme; thus \(E_L\) has everywhere good reduction.

Here is the geometric dictionary step, rather than an unsupported inference from the word “proper”: on each affine open of the base, properness makes the algebra of global functions finite. Flatness makes its restriction to the generic fibre injective. The generic fibre is a geometrically integral proper elliptic curve, whose global functions are \(L\). Normality of \(\mathcal O_L\) then forces this finite algebra inside \(L\) to be the base algebra itself. Stein factorization, tag 03H0, gives geometrically connected fibres. Smoothness makes these fibres geometrically reduced. A smooth proper group scheme with these connected fibres is an abelian scheme. There are no additional disconnected vertical components permitted by the hypotheses.

Consequently \(\Delta_{E_L/L}=\mathcal O_L\), its ideal norm is 1 and the finite term in (6.2) is zero. No good-reduction assumption over the original field `K` is needed. Merely having a proper **nonsmooth** model would not justify this deletion; the code is not making that weaker assumption.

### Periods, powers and factors

- The printed (6.1) asks for \(E^\sigma(\mathbb C)\simeq\mathbb C/(\mathbb Z+\mathbb Zz_\sigma)\). The code supplies \(\mathbb C/(c(\mathbb Z+\tau_\sigma\mathbb Z))\); division by nonzero `c` gives exactly the printed form. No isogeny is being substituted for an isomorphism.
- `IsPeriodAt` is imposed at \(\sigma\circ(K\to L)\), precisely the conjugate of \(E_L\) at \(\sigma:L\to\mathbb C\).
- Any choice of period basis is allowed, not only a reduced or CM period. \(|\Delta(\tau)|(\operatorname{Im}\tau)^6\) is invariant under \(\mathrm{SL}_2(\mathbb Z)\): the weight-12 discriminant contributes \(|c\tau+d|^{12}\) and \(y^6\) contributes its inverse. Silverman Remark 1.2(2) explicitly states this invariance. Hence the universal period quantifier is justified.
- The analytic discriminant is \((2\pi)^{12}\eta^{24}\), absolute value appears once, and the imaginary part is raised to **6**, exactly as in (6.2). Expanding gives the constant **\(-\log(2\pi)\)**, the term \(\pi y/6\) and \(-\tfrac12\log y\), in agreement with the code.
- The sum runs over **all complex embeddings**. The code’s field ring homomorphisms fix \(\mathbb Q\), and there are \([L:\mathbb Q]\) of them. A complex place contributes two embeddings, matching Silverman’s weight \(n_v=2\); a real place contributes one. No further factor of two belongs in the average.
- Thus `sum summand62 / finrank ℚ L` is exactly \(-1/(12[L:\mathbb Q])\) times the log sum. The normalization is absolute, not the unnormalized field-dependent Arakelov degree.

### Original metric versus Deligne and Silverman: explicit warning

The code and Barquero-Sanchez et al. p. 1 both use the original \(i/2\) metric. Replacing it by \(i/(2\pi)\) would multiply the squared differential norm by \(\pi^{-1}\), increasing the height by **\(\tfrac12\log\pi\)** in dimension one. That shift is printed in (1.2), appears in Löbrich’s Definition 2.3, and is consistent with the code’s Deligne variant. It is **not present** in `CMHeight62`.

Do not conflate this shift with the prefactor in Silverman’s printed modular discriminant. If \(\Delta_{62}=(2\pi)^{12}\eta^{24}\), Silverman’s displayed definition has
\[
\Delta_S=(2\pi)^{-12}\eta^{24}=(2\pi)^{-24}\Delta_{62}.
\]
Consequently the **displayed right-hand sides** satisfy
\[
h_S-h_{62}=2\log(2\pi),
\]
because the total archimedean weight is \([L:\mathbb Q]\). Equivalently, recovering the height convention of (6.2) from Silverman’s displayed expression requires subtracting \(2\log(2\pi)\).

The sentence on Barquero-Sanchez et al. p. 1 calling the normalization the same as Silverman’s should therefore not be used as an unqualified identification of the two printed displays. Löbrich’s Remark 2.1 also prints a “\(-2\log2\pi\)” comparison; this report does **not** rely on that sentence’s sign direction. The explicit discriminant prefactors and the two displayed formulas determine the direction algebraically. The target uses (6.2)’s prefactor and explicit original metric, so this source warning does not produce a wrong constant in the Lean inequality.

### Equality versus the Lean inequality and defining infimum

For the standard stable height, everywhere good reduction over `L` is semistable reduction, so the stable height of `E/K` is its original-metric height over `L`; the published equality (6.2) then gives the average exactly.

For the **actual Lean definition**, a sufficient argument is even narrower: construct a genuine dimension-one metrized model over `L` from the abelian scheme’s invariant differential lattice and the supplied analytic periods, and identify its model height with (6.2)’s good-reduction right-hand side. Then use `stableFaltingsHeight_le` to bound the infimum by that one witness. This only needs the **upper** comparison. It does not require proving that every term in the infimum is the standard stable height, nor a separate lower bound or finiteness theorem for the infimum.

Constructing that witness and identifying the cotangent lattice and analytic differential metric are **definition-faithfulness/model-comparison steps**, not statements literally printed in (6.2). They must be supplied in a formal discharge; they are not proved by this report.

## Verdict

**CONSEQUENCE.** Named steps: proper smooth group model \(\Rightarrow\) abelian scheme/everywhere good reduction; minimal discriminant norm \(=1\); normalize the general elliptic formula to (6.2)’s original metric; identify valid period choices; construct the compatible metrized-model witness; apply the infimum upper-bound lemma. Each has the right mathematical hypotheses. There is no missing CM or \(\mathbb Q(j(E))\)-coefficient hypothesis in the checked embedding-average inequality.

This report does not change the recorded `consequence`, `GLUE`, or `pending-review` classifications.

## False, incomplete or unclear

No false target inequality or missing curve/reduction hypothesis was found. The **citation gloss about an identical Silverman normalization is incomplete when compared with the displays as printed**. It should not replace the explicit normalization in (6.2). A formal proof still needs the geometric and metrized-model comparison steps just listed; a naked appeal to the printed equality, without constructing an infimum witness or a stable-height comparison, would be incomplete.

No full certification of the custom stable-height definition, or of equality of its infimum with the usual stable height, is made. The checked upper inequality does not need that full equality.

## Not read

- Silverman’s full proof beyond its beginning on p. 254, and Chapters/sections beyond the two-page publisher preview.
- Faltings’ original paper and Deligne’s original Bourbaki paper; their full proofs and precise independent locators are not certified here.
- The complete proofs of the Gamma-value and Chowla–Selberg formulas in §§3–5 of the 2017 paper. Only the eta/invariance definitions needed for this check were used there.
- Other parts of Löbrich’s paper beyond the relevant §2 definitions, normalization discussion and Proposition 2.1 proof.
- No arXiv edition of the 2017 paper was read or assigned journal numbering.
- No compilation, build, repository edit, or formal construction of the metrized-model witness was performed.

## AI use

An AI language model performed literature discovery, reading of the stated PDF pages, interpretation of the fixed-commit Lean definitions, comparison and report drafting. `pdftotext` extracted PDF text, PDF page reading checked the displayed constants and the reciprocal prefactor in Silverman’s preview, and SHA-256 hashing identified the downloaded copies. No human reading is claimed.

## Evidence

**AI-READ.** The cited journal equation (6.2) was page-read on pp. 13–14, and its original metric was page-read on pp. 1–2. This report is not HUMAN-READ evidence and does not clear `pending-review` or make a maintainer classification ruling.
