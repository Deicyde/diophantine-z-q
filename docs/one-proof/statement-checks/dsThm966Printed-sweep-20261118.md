Recorded from the statement-check sweep of 2026-11-18, against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: dsThm966Printed

## Field and commit

**Field and commit:** `HDec.HSyn.OpenResearchLeaves65.dsThm966Printed`, at commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` of [Deicyde/diophantine-z-q](https://github.com/Deicyde/diophantine-z-q).

The actual field binding is [TailZ91.lean:17–27](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/OneProof/H/TailZ91.lean#L17-L27); it names `DSThm966EV.DSThm966Printed`. The row is [OPEN.md:544–556](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L544-L556).

**Code-locator correction:** this proposition is [DSThm966EV.lean:48–58](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSThm966EV.lean#L48-L58), not the similarly named `DSCoeffExt.DSThm966Printed` at [DSCoeffExt.lean:472–481](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L472-L481). The latter is a normalized, full-eigenform/coefficient formulation. This report checks the field's actual proposition, not that older formulation.

## Edition, page, display

**Edition, page, display:** P. Deligne and J.-P. Serre, *Formes modulaires de poids 1*, Annales scientifiques de l'École Normale Supérieure, fourth series, volume 7, no. 4 (1974), 507–530; DOI `10.24033/asens.1277`. Theorem 4.1 begins on printed p. 513 and concludes with display (4.1.1) and the irreducibility clause on p. 514. These are PDF pages 8–9, because the PDF includes an unnumbered cover. Standing conventions were read in §§1.1–1.6, printed pp. 507–509, and §3.1 with Remarks 3.3–3.4, printed pp. 512–513. The Frobenius convention is the footnote on p. 513.

**Copy:** freely accessible official digitized journal scan supplied by NUMDAM; not a secondary exposition.

- Bibliographic page: https://www.numdam.org/item/ASENS_1974_4_7_4_507_0/
- PDF downloaded and read: https://www.numdam.org/item/ASENS_1974_4_7_4_507_0.pdf
- PDF SHA-256: `65b390f6d33e827e30c6c66bbc15421eca51db3180bdf5996dcee19047be97fc`
- PDF: 25 pages, 2,402,609 bytes. Hash identifies the downloaded scan, not a text extraction.

## Quote

**Quote:** short French excerpts transcribed against the scan; line breaks normalized and mathematical notation retypeset.

Theorem 4.1, p. 513:

> On suppose que f est fonction propre des Tₚ, p ∤ N, avec pour valeurs propres aₚ.

Theorem 4.1, p. 514:

> qui est non ramifiée en dehors de N et telle que

The displayed representation and (4.1.1) are

\[
\rho:G\longrightarrow\mathrm{GL}_2(\mathbf C),\qquad
G=\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q),
\]
\[
\mathrm{Tr}(F_{p,\rho})=a_p,\qquad
\det(F_{p,\rho})=\varepsilon(p)\quad(p\nmid N).
\]

Footnote, p. 513, identifying the inverse of the authors' Frobenius:

> son inverse est le « Frobenius géométrique ».

**Translation:** Assume that f is an eigenfunction of Tₚ, p ∤ N, with eigenvalues aₚ. The representation is unramified outside N and satisfies the displayed formulas. Its Frobenius inverse is geometric Frobenius.

## Standing hypotheses

**Standing hypotheses:** N is an integer at least 1. A Dirichlet character is a homomorphism `(ℤ/Nℤ)× → ℂ×`, and ε is odd: ε(−1)=−1. In §1.5, a form of type `(k, ε)` on Γ₀(N) is a weight-k modular form on Γ₁(N) satisfying

\[
f\!\left(\frac{az+b}{cz+d}\right)
 =\varepsilon(d)(cz+d)^k f(z)
\quad\text{for }\begin{pmatrix}a&b\\c&d\end{pmatrix}\in\Gamma_0(N).
\]

Forms are holomorphic on the upper half-plane and at all cusps (§1.2); parabolic means vanishing at the cusps. In Theorem 4.1 f is nonzero, has weight 1, and is not required to be primitive, normalized, or parabolic. The authors' Tₚ is fixed by the Fourier formula (1.6.1), p. 509. In weight 1 it sends `Σ bₙqⁿ` to `Σ bₚₙqⁿ + ε(p)Σ bₙqᵖⁿ` for p ∤ N.

Section 3.1 defines a linear Galois representation to be a continuous homomorphism, with ℂ carrying the discrete topology. Its image is finite. Unramified at p means trivial on the inertia group of a place above p; Frobenius images are defined up to conjugacy. The p. 513 footnote explicitly uses Artin's arithmetic convention, not geometric Frobenius. Remark 3.3 explains that outside N means every prime not dividing N.

## Lean in plain mathematics

For every positive natural number N, every complex Dirichlet character ε modulo N, and every bundled good Hecke eigenform F of weight 1 and level Γ₁(N), assume that its nebentypus is ε on units and that ε(−1)=−1. There is a group homomorphism

\[
\rho:\mathrm{Gal}(\overline{\mathbf Q}/\mathbf Q)\longrightarrow\mathrm{GL}_2(\mathbf C)
\]

continuous for the usual complex matrix topology, with finite image. For every prime p not dividing N:

1. every inertia subgroup at every valuation place v of ℚ̄ above p lies in ker ρ;
2. for every such v and every arithmetic Frobenius lift σ at v, `trace(ρ(σ))` is F's Tₚ-eigenvalue and `det(ρ(σ))=ε(p mod N)`.

The bundled input is defined at [Newform.lean:85–100](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Newform.lean#L85-L100): a **nonzero** cusp form, character-space membership, and an eigenvector equation at every positive index coprime to N. It imposes no `a₁=1`, no newspace condition, and no bad-prime eigencondition. The character space is the joint diamond eigenspace [DiamondOperators.lean:278–295](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/DiamondOperators.lean#L278-L295); [the same file:374–388](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/DiamondOperators.lean#L374-L388) identifies this with the Γ₀(N) transformation law above, using the lower-right entry and ε, not ε⁻¹.

The Galois definitions are [I4Layer.lean:735–747](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/G9/I4Layer.lean#L735-L747). Here `Qbar=AlgebraicClosure ℚ`, `GQ=Aut_ℚ(Qbar)` with the Krull topology, and `LiesOver v p` means p belongs to the nonunits of v. `IsArithFrob σ v p` means that σ stabilizes v and induces `x ↦ xᵖ` on its residue field: for every x ∈ v, `σ(x)−xᵖ` is in v's maximal ideal.

## Comparison

**Comparison, clause by clause:**

1. **Quantifiers, level, character.** `N : ℕ` with `NeZero N` is exactly N ≥ 1. Both permit imprimitive ε and arbitrary positive N; neither requires squarefree level or primitive conductor. `F.χ=MulChar.toUnitHom ε` matches the character on units. Evaluating ε at p modulo N is harmless because p ∤ N. The explicit oddness assumption is the one printed in Theorem 4.1. At small N where no odd character or nonzero weight-1 form exists, the conditional statement asserts nothing; it does not manufacture a representation.

2. **Type `(1, ε)` and nonzero input.** The diamond/Γ₀(N) dictionary above matches §1.5, with the same weight and character sign. F is a cusp form, whereas the printed theorem permits noncuspidal forms too. This is a restriction of the input, not a stronger conclusion for the printed input class. Nonzeroness is a structure field, not omitted.

3. **Eigenvector condition and normalization.** The Lean input asks for eigenvectors at all positive indices coprime to N; the print asks only for prime Tₚ away from N. The former supplies all the hypotheses the latter uses. No normalization or bad-prime condition has been inserted into the checked proposition. The trace is the eigenvalue, not an unnormalized Fourier coefficient. At good primes the ring action is the classical Tₚ, proved in [Prime/Basic.lean:184–194](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/HeckeSlash/Nebentypus/Prime/Basic.lean#L184-L194) and [RingEigenvalue.lean:104–111](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/RingEigenvalue.lean#L104-L111). Its coefficient recurrence in [Eigenvector.lean:158–170](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/HeckeSlash/Nebentypus/Eigenvector.lean#L158-L170) has exactly the ε(p)p^(k−1) term of (1.6.1). There is no extra diamond factor, inverse character, or power of p in the trace normalization.

4. **One representation, all primes.** The existential ρ occurs before the universal p, v, σ binders. Thus one representation simultaneously satisfies the conditions at every prime p ∤ N, as the printed theorem says. The field is ℂ, the dimension is 2, and the base Galois group is Gℚ in both statements.

5. **Continuity and finite image.** The printed standing convention is continuity into discrete GL₂(ℂ), and it explicitly supplies finite image. Lean asks for finite image and continuity into the usual topology. The printed continuous representation is also continuous for that weaker target topology, so this is not an additional hypothesis or stronger conclusion. No l-adic representation is substituted here.

6. **Unramified outside N; all places and lifts.** The printed inertia condition is stated for a place above p and the resulting Frobenius matrix up to conjugacy. Lean writes that condition for every place and every lift. Inertia groups above the same p are conjugate; triviality is preserved under conjugation. Two Frobenius lifts at a fixed place differ by inertia, and different places give conjugate Frobenius images. Consequently trace and determinant are independent of these choices. This is the explicit form of the printed convention, not a new ramification or local-global theorem. There is no conclusion at p | N, no claim that N is the conductor, and no ramification-at-every-divisor assertion.

7. **Arithmetic versus geometric Frobenius.** The source footnote settles the convention. Lean's residue action x ↦ xᵖ is arithmetic Frobenius. Formula (4.1.1) therefore gives exactly the Lean trace aₚ and determinant ε(p), not ε(p)⁻¹ or the trace of an inverse matrix.

8. **Irreducibility and other omitted conclusions.** The print adds that ρ is irreducible if and only if f is parabolic; hence it supplies irreducibility for the Lean cusp-form input. The checked Lean proposition does **not** ask for irreducibility, uniqueness, a global determinant identity, or conductor equality. Dropping those conclusions is weaker, not a missing hypothesis. The normalized coefficient specialization and parity glue later in DSThm966EV.lean are separate from this row.

## Verdict and limitations

**Verdict: YES.** The actual field is a direct restricted instance of Deligne–Serre Theorem 4.1 under its printed conventions. No clause is stronger than the source. The analytic/character/Hecke dictionary has the matching formulas and existing Lean comparison lemmas cited above; the Frobenius convention is explicitly printed. The field binds to `DSThm966EV.DSThm966Printed` at `DSThm966EV.lean:48–58`, not the older `DSCoeffExt` definition. The printed locator—Theorem 4.1 with (4.1.1), pp. 513–514—is correct, so this is not a `NO-locator` verdict.

**False, incomplete or unclear:** no false or unjustified strengthening was found in the proposition checked. Calling it literally word-for-word printed would be inaccurate: it restricts to cusp forms and all-good-index eigenforms, omits irreducibility, uses the usual rather than discrete target topology, and expands choice-independent Frobenius notation. These changes do not exceed the source. The existing note that the paper is not in the manuscript's bibliography is a bibliographic matter not resolved by this reading.

**Not read:** the proof of Theorem 4.1 in §§5–9; the cited proofs behind the preliminary facts; the entire transitive library dependency tree; and any separate claims about normalized coefficient formulations or the complete Diophantine proof. No Lean compilation, proof verification, repository edit, or review-record change was performed.

**AI use:** an AI assistant read the pinned Lean declarations and the official scan, transcribed the French excerpts, translated them, and prepared the clause-by-clause comparison. `curl` retrieved the PDF and `pdftotext` extracted searchable text; the quoted mathematics and Frobenius footnote were checked against the page images rather than copied from defective OCR. A second AI assistant independently checked the source pages, quotations, code binding, and clause comparisons and agreed with the YES verdict. Neither reading is a human reading or a Lean proof check.

**Evidence: AI-READ.** This report supplies page-read evidence only; it does not count as HUMAN-READ and does not by itself clear a human-reading or statement-review flag.
