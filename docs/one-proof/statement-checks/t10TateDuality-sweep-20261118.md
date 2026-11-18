Recorded from the statement-check sweep of 2026-11-18: an AI-READ report written by an AI agent that the project runs (no person checked it), against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`. It clears no flag.

---

# Statement check: OpenAddedLeaves28.t10TateDuality

## Field and commit

- Field: `HDec.HSyn.OpenAddedLeaves28.t10TateDuality`.
- Exact proposition: `T10Etale.T10_TateDuality`.
- Project commit read: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
- The [OPEN.md entry, lines 194–203][open-row], [bundle field, TailZ87.lean:69–75][bundle], and [proposition, T10Etale.lean:522–527][t10-row] were read at that commit. The statement-check checklist was read first. Only this row is assessed.
- Imported definitions were read from the official Mathlib revision `56a005855ea17e0b0958f73ec801ae140b0a1679` (v4.35.0), which the project's [pinned manifest:14–24][manifest] records. These imported files are not themselves contained in the project commit.

## Edition, page, display

**Milne.** J. S. Milne, *Abelian Varieties*, the desired author edition whose cover says **Version 2.0, March 16, 2008**. Its revision list instead dates v2.00 March 17, 2008; both dates occur in the same downloaded copy. This is not a substituted later edition.

- Part I, Theorem 12.1(a): **printed p. 55 = PDF page 61**.
- Part I, Remark 12.5: **printed p. 56 = PDF page 62**.
- Relevant conventions and definitions also read: Notations, printed p. v = PDF page 5; the abelian-variety definition, printed pp. 7–8 = PDF pages 13–14; Remark 7.3, printed p. 34 = PDF page 40; Proposition 10.5, printed p. 45 = PDF page 51; the degree-one construction and coefficient extension in the proof of Theorem 12.1, printed pp. 55–56 = PDF pages 61–62.
- The PDF has 172 pages, including six preliminary pages. The page offsets above were checked against the printed headings, not inferred from a search excerpt.

**Bhatt–Scholze.** Bhargav Bhatt and Peter Scholze, *The pro-étale topology for schemes*, **arXiv:1309.1198v2, 17 December 2014**, 72 PDF pages. The official abstract page and the PDF's first-page version label agree.

- Section 5.6, Definition 5.6.1 and Proposition 5.6.2: **printed p. 41 = PDF page 41**.
- Necessary surrounding material read: Definition 4.1.1 and Remark 4.1.2, p. 27; Lemma 4.2.12, p. 30; the beginning of Section 5 and Corollary 5.1.6, pp. 34–35; Lemmas 5.4.1–5.4.2, p. 39; Definition 6.8.1 and Lemma 6.8.2, pp. 58–59; the introductory classical coefficient formula, p. 2.
- In this arXiv copy, these printed page numbers equal PDF page indexes. No claim is made about pagination of the separate 2015 published edition.

## Copy

Free author/official copies, retrieved on November 18, 2026:

1. **Milne author PDF:** https://www.jmilne.org/math/CourseNotes/AV.pdf
   - 1,291,594 bytes; 172 PDF pages.
   - SHA-256: `f5ca4e63e5092a4b102daad1470e4cbed5fe8f82115e3a28c8881e3f67f6aaef`.
   - Author's edition page: https://www.jmilne.org/math/CourseNotes/av.html
2. **Bhatt–Scholze official, version-pinned arXiv PDF:** https://arxiv.org/pdf/1309.1198v2
   - 771,493 bytes; 72 PDF pages.
   - SHA-256: `ae0960a28f0f25300211569cd350def057d6c0f781f635694182868e766d3c84`.
   - Version record: https://arxiv.org/abs/1309.1198v2
   - The separately retrieved unversioned official URL, https://arxiv.org/pdf/1309.1198, returned byte-identical content at retrieval.
3. **Bhatt–Scholze author-hosted PDF, also read at the relevant locators:** https://www.math.uni-bonn.de/people/scholze/proetale.pdf
   - 1,279,571 bytes; 72 PDF pages.
   - SHA-256: `99b418b32846c12721e0603590be864b0982d5fa7cf594f8771fc78e53e014c7`.
   - This is not byte-identical to the arXiv PDF. The checked theorem and definition locators agree; the report's version-specific citations refer to arXiv v2.

Relevant Mathlib source was retrieved from the official upstream repository at the manifest's revision, not from an unversioned installation. For example, [ElladicCohomology.lean][elladic] has SHA-256 `f3cb63097d6170774278c5ca16586d9f8be0ffaf126e32515f58d4b77115035b`.

## Quote (verbatim)

Words are quoted verbatim; mathematical typography is transcribed into LaTeX. The principal theorem pages and displays were also checked as rendered page images.

**Milne, Theorem 12.1(a), printed p. 55:**

> Let \(A\) be an abelian variety of dimension \(g\) over a separably closed field \(k\), and let \(\ell\) be a prime different from \(\operatorname{char}(k)\).
>
> (a) There is a canonical isomorphism
> \[
> H^1(A_{\mathrm{et}},\mathbb Z_\ell)\xrightarrow{\simeq}
> \operatorname{Hom}_{\mathbb Z_\ell}(T_\ell A,\mathbb Z_\ell).
> \]

**Milne, Remark 12.5, printed p. 56:**

> Theorem 12.1 is still true if \(k\) is only separably closed (see Milne 1980, II 3.17). If \(A\) is defined over a field \(k\), then the isomorphism
> \[
> \bigwedge{}^*\operatorname{Hom}(T_\ell,\mathbb Z_\ell)
> \longrightarrow H^*(A_{k^{\mathrm{sep}}},\mathbb Z_\ell)
> \]
> is compatible with the natural actions of \(\operatorname{Gal}(k^{\mathrm{sep}}/k)\).

The remark's display prints `T_ℓ` without an `A`; its surrounding discussion concerns `T_ℓ A`. Also, its first sentence redundantly repeats a hypothesis already present in this edition's Theorem 12.1. Neither feature has been silently corrected in the quote.

**Bhatt–Scholze, Proposition 5.6.2, printed p. 41:**

> Let \(\{F_n\}\) is a pro-system of abelian sheaves on \(X_{\mathrm{ét}}\) with surjective transition maps. Then there is a canonical identification
> \[
> H^i_{\mathrm{cont}}(X_{\mathrm{ét}},\{F_n\})\simeq
> H^i(X_{\mathrm{proét}},\lim\nu^*F_n).
> \]

The grammatical “Let … is” is in the printed copy.

## Standing hypotheses

**Milne:** Throughout the notes, the base is a field. An algebraic variety is, in the notes' scheme interpretation, a geometrically reduced separated scheme of finite type; the notes omit its nonclosed points in their presentation. An abelian variety is a complete connected group variety (Part I, Section 1, p. 8); smoothness, geometric irreducibility and commutativity are the usual consequences. Theorem 12.1 assumes a separably closed base and a prime distinct from its characteristic. Remark 12.5 treats an abelian variety defined over an arbitrary field using its separable closure. The coefficient action on \(\mathbb Z_\ell\) in the dual is trivial; the induced action on the dual is contragredient.

**Bhatt–Scholze:** Section 5 begins “Fix a scheme \(X\),” and Section 5.6 repeats this. Proposition 5.6.2 has **no finite-type or algebraically-closed-field hypothesis**: its substantive extra hypothesis is surjectivity of the transition maps of the pro-system of sheaves. Its conclusion involves **Jannsen continuous étale cohomology**, not a blanket identification with naive inverse limits of cohomology groups or with the cohomology of a discrete \(\mathbb Z_\ell\)-sheaf. The introductory classical \(\mathbb Q_\ell\)-formula is stated for a variety over an algebraically closed field, with \(\ell\) different from the characteristic; the constructibility definition there separately assumes a topologically noetherian scheme.

For the row's geometric abelian variety, finite type, separatedness, quasi-compactness, noetherianity and connectedness are available, rather than missing assumptions. In particular, Mathlib's [properness definition][proper] includes separatedness and local finite type, and [universal closedness implies quasi-compactness][uc-qc]. Base change preserves the proper, smooth and geometrically integral properties in [Objects.lean:374–382][basechange].

## Comparison

### 1. Exact proposition and quantifier order

The proposition is:

```lean
def T10_TateDuality : Prop :=
  ∀ (K : Type) [Field K] (A : AbVar K) (ℓ : ℕ) [Fact ℓ.Prime], (ℓ : K) ≠ 0 →
    ∃ φ : (A.baseChange (AlgebraicClosure K)).X.left.EllAdicCohomology ℓ 1 ≃ₗ[ℤ_[ℓ]]
        Module.Dual ℤ_[ℓ] (A.T ℓ),
      ∀ (σ : Field.absoluteGaloisGroup K) x,
        φ (galH A ℓ σ x) = (A.galT (ℓ := ℓ) σ⁻¹).dualMap (φ x)
```

For **every field** \(K\), every project-defined abelian variety \(A/K\), and every prime \(\ell\) whose image in \(K\) is nonzero, there must be **one** integral \(\mathbb Z_\ell\)-linear isomorphism intertwining **every** \(\sigma\) and **every** cohomology class \(x\). There is no characteristic-zero, number-field or dimension-two restriction. The condition on \(\ell\) says precisely \(\ell\ne\operatorname{char}K\) when the characteristic is positive and excludes no prime in characteristic zero. In particular, \(\ell=2\) is included when invertible.

Milne supplies a canonical isomorphism; the row requests only existence, not uniqueness or naturality in all homomorphisms of abelian varieties. Taking degree one in Remark 12.5 gives the relevant compatibility. No polarization or Tate twist is present. Neither side excludes the zero-dimensional abelian variety: its Tate module and degree-one cohomology vanish.

### 2. Abelian variety, geometric points, Tate module

[Objects.lean:160–178][abvar] defines `AbVar K` as a group object over `Spec K` whose structure map is proper, smooth and geometrically integral; it obtains commutativity by a theorem. This is the usual scheme version of Milne's abelian variety. [Geometric integrality][geomint] is tested after field-valued base changes and implies geometric reducedness and irreducibility; [smoothness][smooth] is the standard affine-local smooth ring-map condition.

[Objects.lean:251–287][points] defines \(A(L)\) as \(K\)-scheme morphisms \(\operatorname{Spec}L\to A\). Its Galois action is precomposition with \(\operatorname{Spec}\sigma\), hence applies \(\sigma\) to coordinates.

[Objects.lean:60–80, 95–138][tate-seq] constructs

\[
T_\ell A=\{(x_n)_{n\ge0}:x_0=0,\ \ell x_{n+1}=x_n\}
\subseteq\prod_{n\ge0}A(\overline K).
\]

The compatibility implies \(\ell^n x_n=0\). Removing the redundant zeroth coordinate gives exactly Milne's sequences in Remark 7.3, p. 34: the inverse limit of \(A[\ell^n]\) with multiplication-by-\(\ell\) transition maps. This is **not** the direct-limit \(\ell\)-primary torsion group. The scalar \(a\in\mathbb Z_\ell\) acts on \(x_n\) through its residue modulo \(\ell^n\); choosing a natural-number representative causes no change because \(x_n\) is killed by \(\ell^n\). The actual abelian-variety Tate module is [Objects.lean:294–306][tate-v].

### 3. Exact Mathlib cohomology and coefficients

The [Mathlib small pro-étale site][site] has weakly étale objects over \(X\), where [weakly étale][weakly] means flat with flat diagonal. Its covering topology is the fpqc covering topology restricted to these objects. The [quasi-compact covering condition][qc-cover] permits every affine open of the target to be covered by finitely many images of affine opens of the components; this matches Bhatt–Scholze Definition 4.1.1, not a requirement that each member of an arbitrary covering family be individually quasi-compact.

[ElladicCohomology.lean:64–77][elladic] defines the coefficient sheaf by [continuous sections and restriction by precomposition][continuous]:

\[
U\longmapsto C(U,\mathbb Z_\ell),\qquad
H^1_{\mathrm{Mathlib}}(X)=\operatorname{Ext}^1(\underline{\mathbb Z},F_{\mathbb Z_\ell}).
\]

There are universe lifts in the actual code. More precisely, [Sheaf.H][sheaf-h] is Ext from the constant sheaf on `ULift ℤ`, and the coefficient abelian groups are lifted as well. This is the standard Ext presentation of derived global sections, with harmless changes of universe, not a newly postulated cohomology group.

The topological coefficient ring is the usual one: [\(\mathbb Q_\ell\)][qell] is the completion of \(\mathbb Q\) for the \(\ell\)-adic norm, [\(\mathbb Z_\ell\)][zell] is its norm-at-most-one subring, and [the quotient maps and their kernels][residues] together with [the projective-limit universal property][zlimit] recover \(\mathbb Z_\ell=\varprojlim_n\mathbb Z/\ell^n\). Thus the coefficient is **not the discrete constant sheaf with underlying abstract group \(\mathbb Z_\ell\)**. Bhatt–Scholze Lemma 4.2.12 and Definition 6.8.1 give exactly this continuous-function sheaf; Lemma 6.8.2(1) identifies it with the inverse limit of the finite coefficient sheaves. For finite discrete coefficients these are the pullbacks \(\nu^*(\mathbb Z/\ell^n)\).

[T10Etale.lean:53–123][scalar] makes \(a\in\mathbb Z_\ell\) act by multiplication on the coefficient sheaf and then by `Sheaf.H.map` on cohomology. This is the expected scalar action. Its degree-zero check is useful evidence, but does **not** by itself establish a comparison theorem in degree one.

### 4. Continuous cohomology is an intermediate step, not the final printed formula

Apply Proposition 5.6.2 to the surjective quotient tower \(F_n=\mathbb Z/\ell^n\). With \(X=A_{\overline K}\), it gives

\[
H^1_{\mathrm{proét}}(X,F_{\mathbb Z_\ell})
\simeq H^1_{\mathrm{cont}}(X_{\mathrm{ét}},\{\mathbb Z/\ell^n\}).
\]

Milne's integral classical notation is the inverse-limit cohomology. To reach it from the continuous group, use the **further degree-one derived-limit step**. The derived-limit description in the proof of Proposition 5.6.2 yields the usual exact sequence

\[
0\to\varprojlim{}^1_n H^0_{\mathrm{ét}}(X,\mathbb Z/\ell^n)
\to H^1_{\mathrm{cont}}(X,\{\mathbb Z/\ell^n\})
\to\varprojlim_n H^1_{\mathrm{ét}}(X,\mathbb Z/\ell^n)\to0.
\]

Here \(X\) is nonempty and connected, so the \(H^0\)-tower is \(\mathbb Z/\ell^n\) with surjective quotient maps. It satisfies the Mittag–Leffler condition; the left term vanishes. Consequently the desired **degree-one integral** pro-étale/classical comparison follows. This argument does not require an extra unproved finite-type hypothesis on the row: properness already gives finite type, and the degree-one obstruction is settled directly by connectedness. It must not be restated as “Section 5.6 prints naive étale/pro-étale equality for all schemes.”

This identification is \(\mathbb Z_\ell\)-linear by naturality with respect to the compatible coefficient endomorphisms “multiplication by \(a\bmod\ell^n\).” Proposition 5.6.2 prints an identification of cohomology groups; this scalar compatibility is a dictionary argument, not an extra phrase quoted from its statement.

### 5. Algebraic closure versus separable closure, including positive characteristic

For the nonequivariant isomorphism, Theorem 12.1 can be applied directly over \(\overline K\), since an algebraically closed field is separably closed. There is no problem with that specialization.

Remark 12.5 states its equivariance over \(K^{\mathrm{sep}}\). In **characteristic zero**, an embedded separable closure is the algebraic closure, so this closure dictionary is immediate. However, the exact row quantifies over **all** fields, not only this characteristic-zero application.

For the full row in positive characteristic one must also use:

- \(\overline K/K^{\mathrm{sep}}\) is purely inseparable. Its base-change map on abelian varieties is an integral universal homeomorphism. Étale cohomology is invariant under it; Bhatt–Scholze **Lemma 5.4.2, p. 39**, also explicitly gives the corresponding equivalence of pro-étale topoi.
- Prime-to-characteristic torsion is finite étale, so extension from \(K^{\mathrm{sep}}\) to \(\overline K\) adds no \(\ell^n\)-torsion geometric points. The Tate-module inverse limits agree.
- Restriction identifies \(\operatorname{Aut}_K(\overline K)\) with \(\operatorname{Gal}(K^{\mathrm{sep}}/K)\); automorphisms extend uniquely across the purely inseparable extension. This is an elementary field-theoretic dictionary, **not** a theorem printed as part of Theorem 12.1 or Section 5.6.

These are compatible identifications, so the positive-characteristic quantifier is legitimate. Merely writing “\(\overline K\) versus \(K^{\mathrm{sep}}\), trivial in characteristic zero” would leave the full proposition incompletely accounted for.

### 6. Absolute Galois action, transport direction, and dual action

[Mathlib's absolute Galois group][absolute-galois] is literally

\[
\operatorname{Aut}_K(\operatorname{AlgebraicClosure}K),
\]

with its Krull topology. [Objects.lean:283–306][tate-v] acts on points by \(P\mapsto P\circ\operatorname{Spec}\sigma\), and acts on Tate sequences coordinatewise; call the latter action \(\rho_T(\sigma)\).

Put \(a_\sigma=1_A\times\operatorname{Spec}\sigma\) on \(A_{\overline K}\). [T10Etale.lean:188–251][transport] constructs the site equivalence and the induced sheaf/Ext transport. Its direction is

\[
\operatorname{transport}(e)=e_*=(e^{-1})^*.
\]

The coefficient-sheaf isomorphism is componentwise the identity; the constant-sheaf identification is the canonical one from the sections adjunction. The [degree-zero calculation:366–381][transport-zero] confirms the direction, sending a global function to its composition with \(e^{-1}\). Transport is proved linear and bijective in the file.

[The exact `galH` definition:505–512][gal-h] uses transport along \(a_{\sigma^{-1}}\). Therefore its intended cohomological action is **\(a_\sigma^*\)**, not \(a_{\sigma^{-1}}^*\). Together with the point action above, this is the usual contragredient convention: the pullback of a constant-coefficient character precomposes that character with the inverse Galois action on the Tate module.

[Module.Dual][dual] is the algebraic linear dual, and [dualMap:124–130][dual-map] is precomposition. Thus the final equality of the proposition says exactly

\[
\phi(\operatorname{galH}(\sigma)x)(t)
=\phi(x)(\rho_T(\sigma^{-1})t)
\quad\text{for every }\sigma,x,t.
\]

The coefficient action is trivial; no \(\mathbb Z_\ell(1)\), Weil pairing, or dual abelian variety is substituted here. Milne's Remark 12.5 gives the natural Galois compatibility, and taking degree one and the inverse of its displayed isomorphism gives this orientation.

The comparison remains natural under scheme isomorphisms by the finite-coefficient comparison and the derived-limit construction. Bhatt–Scholze **Lemma 5.4.1, p. 39**, explicitly records functoriality of \(\nu\) in the scheme. Identifying this functorial pullback with the file's particular Ext transport is another mathematical implementation dictionary; it is not literally a named theorem of Milne or Proposition 5.6.2.

### 7. The rational formulation is a consequence of the integral row

The actual proposition does **not** assert a \(\mathbb Q_\ell\)-linear isomorphism: it asserts the integral isomorphism above. [Objects.lean:299–300][tate-v] defines

\[
V_\ell(A)=\mathbb Q_\ell\otimes_{\mathbb Z_\ell}T_\ell A.
\]

Milne's Proposition 10.5, p. 45, gives finite freeness of \(T_\ell A\), and the proof on p. 56 explicitly uses

\[
H^1_{\mathrm{ét}}(A,\mathbb Q_\ell)
\simeq H^1_{\mathrm{ét}}(A,\mathbb Z_\ell)\otimes_{\mathbb Z_\ell}\mathbb Q_\ell.
\]

Hence scalar extension of the integral comparison, finite-free base change of linear duals, and finite-dimensional biduality give

\[
V_\ell(A)\simeq
\operatorname{Hom}_{\mathbb Q_\ell}
\bigl(H^1_{\mathrm{ét}}(A_{\overline K},\mathbb Q_\ell),\mathbb Q_\ell\bigr)
\]

Galois-equivariantly. `Module.Dual ℚ_[ℓ]` means this ordinary algebraic \(\mathbb Q_\ell\)-linear dual. The finiteness conditions needed for dual base change and biduality come from the abelian variety; they are not valid for an arbitrary module merely by notation.

A rational representation isomorphism alone does **not** give a specified integral-lattice isomorphism. Thus the comment's “equivalently … after \(\otimes\mathbb Q_\ell\)” should describe the rationalization, not claim an unrestricted reverse implication. Likewise, identifying scalar-extended cohomology with cohomology of the pro-étale \(\mathbb Q_\ell\)-coefficient sheaf uses a further coefficient-localization comparison; Lemma 6.8.2(2) identifies the sheaf by localization but is not itself that cohomology statement. The integral row does not require this additional rational reformulation.

### 8. What remains a definition/comparison dictionary

The sources justify the intended mathematics, but neither source mentions the particular Lean types or constructions. The remaining steps are explicit rather than hidden:

1. identify the fixed-universe, lifted Ext construction with ordinary sheaf cohomology; Bhatt–Scholze Remark 4.1.2 discusses site-size independence of cohomology;
2. identify the continuous coefficient sheaf with the finite-coefficient inverse limit and its scalar action;
3. pass from Jannsen continuous cohomology to classical degree-one inverse-limit cohomology using the vanishing derived limit above;
4. use the closure and Galois-group identifications, including the purely inseparable case;
5. identify the chosen site/Ext transport with canonical cohomological pullback and preserve these comparisons under it.

The defining Mathlib cohomology file's [notes:33–36][elladic-notes] expressly leave its comparison with classical cohomology for future development. The imported definitions read here do not supply a compiled theorem connecting this row to Milne. Also, [T10Etale.lean:497–507][action-note] explicitly leaves transport functoriality, and hence the separately proved action law for `galH`, unproved in that file. Its displayed intertwining identities would themselves imply the action law via the Tate-module action; this is not a counterexample to the proposition. The degree-zero and bijectivity checks do not replace the natural degree-one dictionary.

## Verdict

**CONSEQUENCE.** The underlying mathematical statement follows from the **integral** canonical isomorphism in Milne Theorem 12.1(a), the **printed** natural Galois compatibility in Remark 12.5, and the **further named steps** above: continuous-function coefficients, the Bhatt–Scholze continuous-cohomology comparison, the degree-one Mittag–Leffler step, closure/Galois identifications, and natural scalar/Ext transport. The requisite geometric finiteness and invertibility conditions are supplied by the row's definitions.

It is **not YES as a verbatim printed theorem**: Mathlib's pro-étale cohomology and its particular Galois transport are not Milne's literal notation, and Section 5.6 alone does not print all of these dictionaries. This is a mathematical statement reading, **not** a newly verified Lean proof of the row or a certification of every implementation lemma.

## False, incomplete or unclear

- **No false clause or missing geometric hypothesis was found.** This is not a NO-statement or NO-locator verdict.
- A source description restricted to the characteristic-zero closure dictionary is **incomplete for the actual all-fields row**. Positive characteristic requires the additional identifications in Comparison 5.
- A description treating Proposition 5.6.2 as a direct printed identification with naive classical \(\ell\)-adic cohomology is **incomplete**: continuous cohomology and the derived-limit step must be named.
- The actual integral proposition is supported by Milne's integral theorem. A rational-only paraphrase must not replace it or assert the reverse integral implication without a lattice argument.
- The specific Mathlib comparison and transport-coherence theorems remain implementation work; this report does not represent their absence from the definitions read as a refutation of the intended mathematical statement.

## Not read

- No other open row, including any modular-form row, was assessed.
- Milne's 1986 chapter and its Theorem 15.1(a), Milne 1980 including II 3.17, the full foundations of étale cohomology and their cited proofs were not independently read. The 2008 theorem, remark, relevant definitions and displayed degree-one/coefficient arguments were read; their full external dependencies were not audited.
- The remainder of Bhatt–Scholze outside the enumerated pages, Jannsen's 1988 paper, and the separate 2015 published copy were not independently checked. The proof on arXiv p. 41 and the pertinent sheaf/functoriality definitions were read.
- The entire dependency proof library, all categorical coherence proofs, and code outside the relevant project definitions were not audited. No proof compilation or new proof construction was performed. This is not a whole-repository verification.

## AI use

An AI assistant read the sources and code and prepared this report; curl and pdftotext handled retrieval/text extraction. A second AI reading checked the principal source pages, the exact quantifiers, and the transport/dual conventions. Neither reading is a human reading or a formal proof check.

## Evidence: AI-READ

This report is AI-READ evidence, not a human reading. Source-page availability, quotation checks and the consequence verdict do not certify a formal proof or change any review classification by themselves.

[open-row]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L194-L203
[bundle]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/OneProof/H/TailZ87.lean#L69-L75
[t10-row]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Textbook/T10Etale.lean#L522-L527
[manifest]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/lake-manifest.json#L14-L24
[abvar]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Objects.lean#L160-L178
[points]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Objects.lean#L251-L287
[tate-seq]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Objects.lean#L60-L138
[tate-v]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Objects.lean#L283-L339
[basechange]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Objects.lean#L374-L382
[scalar]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Textbook/T10Etale.lean#L53-L123
[transport]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Textbook/T10Etale.lean#L188-L251
[transport-zero]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Textbook/T10Etale.lean#L366-L381
[gal-h]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Textbook/T10Etale.lean#L505-L512
[action-note]: https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Textbook/T10Etale.lean#L497-L507
[elladic]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean#L64-L77
[elladic-notes]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean#L33-L36
[site]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Sites/Proetale.lean#L45-L150
[weakly]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/WeaklyEtale.lean#L44-L48
[qc-cover]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Cover/QuasiCompact.lean#L34-L68
[continuous]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Sites/ConstantSheaf.lean#L43-L45
[sheaf-h]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/SheafCohomology/Basic.lean#L53-L58
[proper]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/Proper.lean#L14-L41
[uc-qc]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/UniversallyClosed.lean#L164-L165
[geomint]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Geometrically/Integral.lean#L37-L59
[smooth]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean#L56-L72
[absolute-galois]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/FieldTheory/AbsoluteGaloisGroup.lean#L40-L46
[dual]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Dual/Defs.lean#L59-L62
[dual-map]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/LinearAlgebra/Dual/Defs.lean#L124-L130
[qell]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Padics/PadicNumbers.lean#L531-L539
[zell]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Padics/PadicIntegers.lean#L61-L75
[residues]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Padics/RingHoms.lean#L447-L498
[zlimit]: https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/Padics/RingHoms.lean#L656-L702
