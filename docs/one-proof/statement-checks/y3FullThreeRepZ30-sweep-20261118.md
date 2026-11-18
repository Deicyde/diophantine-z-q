Recorded from the statement-check sweep of 2026-11-18, against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: y3FullThreeRepZ30

**Verdict: CONSEQUENCE. Evidence: AI-READ.** The auxiliary-level construction gives the Lean statement by standard additional steps; it is not a direct level-three instance of Buzzard’s numbered results. A useful citation correction is that Buzzard already states the relative canonical-polarization assertion in §1, p. 3. It is not necessary to posit a new, unprinted relative Lemma P for this comparison.

Checked on 2026-11-18. This report records a statement comparison, not a human reading or a formal discharge of the open hypothesis.

## Field and commit

- Field: `HDec.HSyn.OpenResearchLeaves65.y3FullThreeRepZ30`.
- Lean constant: `Y3RouteA.Y3FullThreeRepZ30`.
- OPEN.md commit: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
- [OPEN.md entry, lines 502–511](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L502-L511).
- [Definition, lines 284–288, and its docstring, lines 242–283](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3FullThreeZ30.lean#L242-L288).
- [Manuscript construction, lines 443–477](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/diophantine_zq.tex#L443-L477).

## Edition, page, display

Kevin Buzzard, *Integral models of certain Shimura curves*, Duke Mathematical Journal **87**(3) (1997), 591–612; [DOI 10.1215/S0012-7094-97-08719-6](https://doi.org/10.1215/S0012-7094-97-08719-6).

**Edition actually read:** the author copy whose cover says “Original version 13/5/1996. Some typos fixed 14/6/2002.” It has 21 PDF pages, including the cover. In this copy the printed page numbers agree with the PDF page numbers:

- §1, false elliptic curves and the relative canonical principal polarization: **pp. 2–3**.
- Definition 1.1 and the full-level and quotient-level sheaves: **pp. 3–4**.
- Standing hypotheses (i)–(iii) and the definition of the moduli category: **pp. 4–5**.
- **Theorem 2.1: p. 5.**
- Lemma 2.2 and its proof: **pp. 6–7**.
- **Corollary 2.3: p. 7**, including its proof.

These are author-copy page numbers, not guessed journal page numbers. The original publisher facsimile was not obtained, and identity of every word with the 1997 typeset edition is not claimed.

## Copy

**Author copy, preserved in a public web archive.** The author’s [papers page](https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/index.html) lists this paper and its PDF. The current PDF origin failed to return the file; the publicly archived 2021-10-16 copy of that author-posted PDF was downloaded instead. Its PDF signature, 21-page count, 2002 creation metadata, and archive capture digest were checked. No publisher access restriction was bypassed.

Primary source and checksums:

- Original author URL: https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/shimura.pdf
- **Exact downloaded copy:** https://web.archive.org/web/20211016141108id_/https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/shimura.pdf
- **PDF SHA-256:** `4854cb4adc99fec7eac47596dea86832e2e468f3c80d78726afeb98d2404b915`.
- PDF size: **231177 bytes**. Its SHA-1 archive digest matches the capture record: `D5H43O7U5R5DH4C3WSAXG4CCHNCUWXDI`.
- [Pinned manuscript](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/diophantine_zq.tex), SHA-256 of the complete file: `cb1148cd6c7769d2af3f1636b60ff0ada4b40431978d1e98d0c339274b3d792b`.
- [Pinned Lean statement file](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3FullThreeZ30.lean), SHA-256 of the complete file: `f3daeff48168ad0865cfbcecd34eda2e360d2f8949d1ef9f4a6deec3f253a861`.

## Quote

The following are short verbatim quotations; line breaks and mathematical typography are transcribed into Markdown notation.

**Theorem 2.1, p. 5:**

> “$X^D(U)$ is an algebraic stack over $\mathbb Z[1/M_Ud]$. Moreover, the morphism $X^D(U)\to\operatorname{Spec}(\mathbb Z[1/M_Ud])$ is proper and smooth of relative dimension 1.”

**Corollary 2.3, p. 7:**

> “If $U\subseteq\mathcal O_{D,f}^{\times}$ is open and compact, and satisfies properties (i)–(iii) above, then $X^D(U)$ is the stack associated to a regular scheme, and the morphism $X^D(U)\to\operatorname{Spec}(\mathbb Z[1/M_Ud])$ is projective.”

**Restriction on discriminant-prime level, p. 5:**

> “(ii) is much more important, as it ensures that we never consider level structures at primes dividing $d$”

**Relative principal polarization, §1, p. 3:**

> “We now observe that if $(A/S,i)$ is a false elliptic curve, then there is a unique principal polarisation on $A$ such that if $s$ is a geometric point of $S$, then the corresponding Rosati involution on $\operatorname{End}(A_s)$ induces $*$ on $\mathcal O_D$.”

> “Finally, we deduce the result for a general base $S/\operatorname{Spec}(\mathbb Z[1/d])$ by the Proposition in Section 11 of [B].”

**Finite order of the relevant automorphism, Lemma 2.2 proof, p. 6:**

> “By [M] proposition 17.5, this implies that $\theta$ has finite order in $\operatorname{End}_k(A)$.”

Here [B] is Boutot’s *Variétés de Shimura: Le problème de modules en inégale caractéristique*; [M] is **Milne’s** 1986 *Abelian Varieties*, not Mumford’s book.

## Standing hypotheses

Buzzard fixes an **indefinite non-split quaternion algebra** $D/\mathbb Q$, its reduced discriminant $d$, and a maximal order $\mathcal O_D$. False elliptic curves are abelian schemes of relative dimension two with an injective, identity-preserving $\mathcal O_D$-action, over schemes on which $d$ is invertible. A polarization is **not a separate datum** in the definition of a false elliptic curve.

For the numbered results in §2, the compact open subgroup $U\subseteq\widehat{\mathcal O}_D^{\times}$ satisfies:

1. $\det(U)=\widehat{\mathbb Z}^{\times}$, with determinant interpreted as reduced norm.
2. $U$ is maximal at every prime dividing $d$.
3. $U\subseteq V_1(N)$ for some $N\geq4$ with $\gcd(N,d)=1$.

At the split primes, $V_1(N)$ is the inverse image of the subgroup of matrices $\left(\begin{smallmatrix}a&b\\0&1\end{smallmatrix}\right)$ modulo $N$. The integer $M_U$ is the smallest positive $M$ prime to $d$ with $V_M\subseteq U$. The base is $\operatorname{Spec}\mathbb Z[1/(M_Ud)]$.

The section uses arbitrary schemes over this base; it does not impose the Lean statement’s restriction to locally noetherian bases. Full markings are $\mathcal O_D$-equivariant isomorphisms from the constant torsion module. Quotient-level structures are defined by **étale sheafification**, not just by taking orbits of globally available markings.

For the canonical polarization, §1 fixes $t\in\mathcal O_D$ with $t^2=-d$ and the involution $x^*=t^{-1}\bar x t$. It explicitly supplies the unique principal polarization of this Rosati type over a general $\mathbb Z[1/d]$-base.

## Comparison

### 1. What the Lean statement actually says

There is one scheme $\mathcal Y/\mathbb Z[1/30]$, proper and smooth of relative dimension one, and one universal level-three QM abelian-surface scheme over $\mathcal Y$. For **every** locally noetherian $\mathbb Z[1/30]$-scheme $S$ and every such object over $S$, there is exactly one base-preserving map $S\to\mathcal Y$ along which that object is isomorphic to the pullback of the universal object, with its order action and level sections.

The existential choice of $(\mathcal Y,\mathcal A)$ precedes the universal quantifier over $S$. This is scheme representability with a universal family, not merely a parametrization of geometric points.

Definitions unfolded at the pinned commit:

- Quaternion algebra and order: [Structures.lean, lines 30–69](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Structures.lean#L30-L69). Here $B=(2,-3\mid\mathbb Q)$ and $\mathcal O=\mathbb Z\langle1,i,(1+j)/2,(i+ij)/2\rangle$. The algebra is ramified precisely at 2 and 3 and split at infinity. The reduced-trace Gram determinant of this displayed order is $-36$, so its reduced discriminant is 6 and it is maximal. Thus it matches Buzzard’s fixed algebra/order, not an Eichler or level-three order.
- Base: [Y3FullThreeZ30.lean, lines 225–238](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3FullThreeZ30.lean#L225-L238). `Z30` is the localization of $\mathbb Z$ away from 30.
- Family and dimensions: [Leaves.lean, lines 25–32](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Leaves.lean#L25-L32), and [ShimuraY3PrintedLeaves.lean, lines 75–108](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean#L75-L108). `QMAbSchemeP` means a proper, smooth, geometrically connected group scheme of relative dimension two, with a unital ring action and additive $\mathcal O$-linear sections $\eta(a)$ satisfying $\eta(3a)=0$; its `P` suffix refers to the printed level condition, **not polarization**.
- Full level three: [the same file, lines 94–108](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean#L94-L108). At every geometric point, the kernel of $\eta$ is exactly $3\mathcal O$, and its image is all of the geometric three-torsion. Since 3 is invertible, this is an isomorphism of finite étale group schemes $(\mathcal O/3\mathcal O)_S\simeq A[3]$, not just an injection into rational points. Both sides have degree 81. Additivity and linearity give the required module structure, also over nonreduced bases.
- Isomorphism/pullback relation: [ShimuraGoodReductionNoGuard.lean, lines 44–52](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean#L44-L52). `QMFamFibre` supplies a pullback square and compatibility with the order action and all level sections. It preserves the zero section. By standard rigidity, the resulting zero-preserving scheme isomorphism is an isomorphism of abelian schemes; no larger isomorphism relation is being substituted.

The group law presentation uses the standard characterization of an abelian scheme as a proper smooth group scheme with geometrically connected fibres; commutativity follows from rigidity. Although the action’s axioms do not separately say injective, faithfulness is automatic on a nonempty base: a nonzero two-sided ideal of $\mathcal O$ contains a nonzero integer, whereas multiplication by that integer cannot be the zero endomorphism of a positive-dimensional abelian variety on any geometric fibre. The empty-base case uses the usual unique-empty-family convention of a moduli functor and adds no nonempty objects.

The full five-marking and $G_5=(\mathcal O/5\mathcal O)^\times$ occur in the **derivation**, [manuscript lines 447–477](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/diophantine_zq.tex#L447-L477); they are not additional fields or conclusions in this Lean proposition. At 5 the algebra is split, so $G_5\simeq\operatorname{GL}_2(\mathbb F_5)$, of order 480. Its marking action is by precomposition with right multiplication, commuting with the left $\mathcal O$-action.

### 2. Printed starting point: valid at V₁(5), invalid as a direct level-three citation

For $U=V_1(5)$ and $d=6$, all three hypotheses hold. At 5, matrices $\operatorname{diag}(a,1)$ give the full determinant image; the other local factors are maximal-order units. At 2 and 3 the level is maximal. Finally $5\geq4$ and $\gcd(5,6)=1$. Here $M_U=5$, so the base is **exactly $\mathbb Z[1/30]$**.

Theorem 2.1 and Corollary 2.3 therefore give a smooth proper, indeed projective, fine moduli scheme at this auxiliary level, with its universal false elliptic curve.

They do **not** directly apply to full level three: it is nonmaximal at $3\mid d$, and $N=3$ also fails the displayed smallness bound. Nor may Corollary 2.3 simply be reapplied to the full-five kernel: its determinant image is restricted modulo 5 and fails (i). The manuscript correctly avoids both invalid applications by constructing finite étale marking covers instead.

### 3. Full five-marking: printed relative construction, then a consequence

For a fixed $V_1(5)$-marking, its full-five refinements form a finite étale cover, by the full-marking torsor and quotient-level definitions in §1, pp. 3–4. More precisely, the refinement cover is a torsor under

$H=\{\left(\begin{smallmatrix}a&b\\0&1\end{smallmatrix}\right):a\in\mathbb F_5^\times,\ b\in\mathbb F_5\}$,

of order **20**, not a torsor of order 480 over the intermediate $V_1(5)$ scheme. Each full marking determines its quotient marking, so this cover represents the full-five problem. No determinant component has been discarded. Its smoothness and projectivity follow from being finite étale over the printed auxiliary model.

This is standard and correct. It uses the printed relative marking construction, not a new application of the theorem at a level with smaller determinant image.

### 4. Adding full three: manuscript argument, standard and correct

Because 3 is invertible on the base, $A[3]$ is finite étale. The $\mathcal O$-equivariant isomorphism sheaf between it and the constant module is represented by a finite étale scheme. It remains to establish nonemptiness, not merely representability of an empty isomorphism sheaf.

On every geometric fibre, including characteristic $p\notin\{2,3,5\}$, $V_3(A)$ has $\mathbb Q_3$-dimension four. The unital action of the division algebra $B_3$, also of dimension four, makes it a rank-one left $B_3$-module. Its Tate lattice is stable under the maximal order $\mathcal O_3$.

After identifying this module with $B_3$, take an element $x$ of the lattice with least division valuation. Every other lattice element $y$ has $v(yx^{-1})\geq0$, hence $yx^{-1}\in\mathcal O_3$. Stability gives the reverse inclusion, so the lattice is exactly $\mathcal O_3x$. Reduction modulo **3**, not modulo the division algebra’s maximal ideal, gives $A[3]\simeq\mathcal O_3/3\mathcal O_3\simeq\mathcal O/3\mathcal O$ on the geometric fibre. The isomorphism sheaf is therefore a surjective finite étale cover.

This is the additional argument in manuscript lines 449–462, not a statement of Theorem 2.1 or Corollary 2.3. The division-lattice argument works directly in every allowed characteristic; no characteristic-zero-only polarization or Tate comparison is being silently used. It gives the smooth projective full-three/full-five scheme $X_{35}$.

### 5. Freeness at three: manuscript argument, with a printed polarization input

A geometric stabilizer for the $G_5$-action on $X_{35}$ supplies an $\mathcal O$-linear automorphism $u$ of $A$ fixing its full three-marking. It preserves the canonical principal polarization from Buzzard §1; uniqueness also makes that polarization compatible with isomorphisms and base change. The finite-order assertion used here is explicitly recalled in Buzzard’s Lemma 2.2 proof, p. 6.

On $T_3(A)$, $u$ is congruent to the identity modulo 3. The group $1+3M_4(\mathbb Z_3)$ has no nontrivial torsion. To check the relevant boundary case, suppose an element of prime order $q$ is $1+3^rM$, $r\geq1$, with some entry of $M$ a unit. If $q\ne3$, its $q$th power is nonidentity modulo $3^{r+1}$. If $q=3$, the leading term of its cube is $3^{r+1}M$, and the other terms have valuation at least $r+2$. Both cases are contradictions. Every nontrivial finite-order element has a nontrivial prime-order power.

Faithfulness of the prime-to-characteristic Tate action gives $u=1$, and the full five-marking then gives the stabilizing group element equal to 1. Thus the action is free. This does not assume $\operatorname{End}(A)=\mathcal O$ and does not omit CM or positive-characteristic fibres. The change of five-marking may change the intermediate $V_1(5)$-marking; the action is on $X_{35}$ over $\mathbb Z[1/30]$, not necessarily over the intermediate auxiliary scheme.

### 6. Quotient and universal family: additional descent, standard and correct

A finite group acting on a projective scheme has a scheme quotient; with this free action, $X_{35}\to Y=X_{35}/G_5$ is a finite étale torsor. Standard finite-group quotient and effective descent results give projectivity of $Y$ and descent of smoothness and relative dimension one. Properness is consequently no difficulty.

Forgetting the five-marking gives a $G_5$-equivariant universal abelian scheme with its order action, three-marking and canonical polarization. The canonical isomorphisms satisfy the descent cocycle. Effective étale descent for polarized abelian schemes supplies an abelian scheme on $Y$, and the action and three-marking descend with it.

This quotient represents the **unsheafified moduli problem of objects up to isomorphism**, not just geometric orbits. Indeed, for any object $(A,\iota,\eta_3)$ on a base $S$, the sheaf of full five-markings is a surjective finite étale $G_5$-torsor on $S$. Over it the object has a classifying map to $X_{35}$; forgetting five yields a descended map $S\to Y$. Conversely the descended universal family pulls back to the original object. Rigidity at full level three makes the identifications unique and gives uniqueness of the classifying map. This argument works for nonreduced, locally noetherian bases as well as fields.

These quotient/descent steps are the manuscript’s lines 473–477, not the text of Buzzard’s two numbered results. The Lean file assumes their resulting representability statement; its later generic-fibre readers do not prove these steps.

### 7. Polarization and the final range of the claim

The purported missing relative Lemma P is **already printed** as the unnumbered §1 assertion on p. 3, with the extension to general bases stated there. For this order, the manuscript’s $\mu=2j+ij$ lies in $\mathcal O$ and satisfies $\mu^2=-6$. Taking $t=\mu$ gives exactly the manuscript’s involution $x\mapsto\mu^{-1}\bar x\mu$. Thus the polarized problem of this fixed canonical type and the polarization-free problem have the same objects and isomorphisms. Omitting an arbitrary polarization would not be a weakening in general, but there is a printed justification for omitting this canonical one here.

After the construction, the Lean conclusion is weaker in requiring **proper** rather than projective and in testing only locally noetherian bases in universe zero. It does not require geometrically connected fibres, a chosen determinant component, or a degree bound. The covers and quotient keep all markings/determinant components that the full-three functor requires. The analytic identification with $Y_3$ and the bound 324 are not extra clauses in the proposition being checked.

## Verdict

**CONSEQUENCE.** A valid source chain is Buzzard **Theorem 2.1 and Corollary 2.3 at $V_1(5)$**, together with **§1, pp. 3–4** for canonical polarization and the relative marking sheaves, followed by the manuscript’s division-lattice argument, full-three rigidity, free finite-group quotient, and effective étale descent.

No stronger Lean clause or dropped necessary hypothesis was found in this chain. The numbered locators are correct in the author edition read. They are not locators for a direct full-three theorem. Add **Buzzard §1, p. 3** to the relative-polarization citation and **§1, pp. 3–4** to the full-five refinement citation. No repair of the mathematical statement is indicated by this reading.

## False, incomplete or unclear

**Not found false.** Citing only the two numbered results as if they directly represented full level three would be incomplete and incorrect, but the row explicitly records an auxiliary-level consequence. The additional derivation above supplies the comparison. The docstring’s on-the-spot polarization warning can be replaced, at the source-comparison level, by the printed §1 locator.

The marking-at-three, torsion-freeness, quotient and descent arguments remain additional steps, not a kernel proof of this open Lean field. This report does not reclassify the row as a direct printed leaf and does not clear human-reading or review flags.

## Not read

- The original typeset 1997 Duke facsimile; only the identified corrected author copy was read.
- Boutot [B], §§11 and 14; Boutot–Carayol [BC], III.1.5; Milne [M], Proposition 17.5; and Deligne–Rapoport [DR], II.1.14. Their uses were read in Buzzard, not independently checked in those works.
- Separate printed proofs of the general quotient, effective descent, Tate-action faithfulness and rigidity facts. The particular division-lattice and congruence-group steps were checked as mathematical arguments above.
- Buzzard §§3–5 were not checked for results used by this report. The proof of Theorem 2.1 is a citation to [B]; that underlying proof was not inspected. Corollary 2.3 and Lemma 2.2 were read with their displayed proofs.
- No compilation, repository modification, issue comment or public posting was performed.

## AI use

A language-model assistant performed public-source discovery, read the identified author-copy pages and extracted text, unfolded the pinned Lean definitions, checked the mathematical argument, and drafted this report. `curl` downloaded the public author-copy archive; `pdftotext` extracted the PDF text. Checksums and the small quaternion/group-order calculations were computed programmatically. There was no human source reading or independent human review.

## Evidence

**AI-READ.** This is recorded reading evidence only; it is not HUMAN-READ and does not authorize changing the project’s counts or review flags.
