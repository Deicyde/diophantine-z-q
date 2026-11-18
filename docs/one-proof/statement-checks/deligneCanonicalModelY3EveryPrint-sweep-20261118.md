Recorded from the statement-check sweep of 2026-11-18, against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: deligneCanonicalModelY3EveryPrint

Verdict: CONSEQUENCE. The actual Lean implication is supported by the canonical-model theorem together with the explicit PEL, level, polarization, and witness-comparison arguments below. It is not a statement printed verbatim in Deligne or Milne. No false conclusion or stronger integral-model assertion was found in this Prop. In particular, the words “stated as the print states it” should not replace the consequence argument.

Evidence: AI-READ. This report is not a human reading and does not clear a pending-review or reading-risk flag.

## Field and commit

- Field: `HDec.HSyn.OpenResearchLeaves65.deligneCanonicalModelY3EveryPrint`.
- Lean constant: `Y3Hodge.DeligneCanonicalModelY3EveryPrint`.
- OPEN.md commit read: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
- Record: [OPEN.md:320–332](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L320-L332).
- Definition and docstring: [Y3HodgePrint.lean:914–937](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L914-L937).
- Method: the [statement-check checklist](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/STATEMENT-CHECKS.md#L49-L75) and the [locator audit, R1](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/research/locators.md#L40-L46).
- Reading date: 2026-11-18. All code references in this report are to that commit, not to a moving branch.

## Edition, page, display

### D — Deligne

Pierre Deligne, *Travaux de Shimura*, Séminaire Bourbaki, exposé 389, February 1971; text written March 1971; printed pp. 123–165.

- URL: https://www.numdam.org/article/SB_1970-1971__13__123_0.pdf
- SHA-256: `054847cecac9c396e2a6f568443db180786a0c5528ec08530fd464d5474bd534`
- Copy: legitimate NUMDAM archive scan of the original French text, including its copyright notice; 44 PDF pages.
- Page mapping: printed page `p` is PDF page `p − 121`; PDF page 1 is the archive cover.
- Relevant passages read: §1.2, p. 126; §§1.5–1.12, pp. 127–131; §§3.13–3.15, pp. 141–143; §§4.9–4.12, pp. 147–149; §§4.15–4.17, p. 150; Theorem 4.21, p. 152; Corollaries 5.5–5.7, p. 156; Example 5.8, p. 157. The strong-approximation statement (0.3), p. 125, was also read.

### M — Milne

J. S. Milne, *Introduction to Shimura Varieties*, Clay Mathematics Proceedings 4 (2005), pp. 265–378; author-hosted copy of the published typeset chapter.

- URL: https://jmilne.org/math/xnotes/svi2005.pdf
- SHA-256: `6336f0a23084dc0bf815a901c61a0f925dbc8dc1c395af8864c1d90bea69c4a1`
- Copy: legitimate author-hosted published typesetting; 114 PDF pages. The edition is identified by the chapter masthead and printed pagination, not by the PDF metadata's modification date.
- Page mapping: printed page `p` is PDF page `p − 264`.
- Relevant passages read: §2, pp. 281–283, especially Examples 2.4, 2.7, 2.8 and (19); Theorem 4.16, p. 300; §5, pp. 303, 308–314; §6, pp. 314–317 and 319–320, especially (31), Theorem 6.8 and Theorem 6.11; §8, pp. 323–329, especially Propositions 8.7, 8.14, Theorem 8.17 and Proposition 8.19; §12, pp. 343–347, especially Definition 12.2, Example 12.4(c),(d), and Definition 12.8 with (54); §14, pp. 352–355, especially Theorem 14.8, Proposition 14.12 and the PEL paragraph spanning pp. 354–355. The field-of-definition discussion on pp. 366–367 was read as a supplementary caution.

### B — supplementary polarization supplier

Kevin Buzzard, *Integral models of certain Shimura curves*, author copy. Its cover states “Original version 13/5/1996. Some typos fixed 14/6/2002.” The paper was published in Duke Mathematical Journal 87 (1997); this reading does not certify the journal's pagination or byte identity.

- URL: https://www.ma.imperial.ac.uk/~buzzard/maths/research/papers/shimura.pdf
- SHA-256: `4854cb4adc99fec7eac47596dea86832e2e468f3c80d78726afeb98d2404b915`
- Copy: legitimate author-hosted corrected author copy; 21 PDF pages.
- Relevant passages read: definition of false elliptic curve, §1, p. 2; the fixed-involution principal-polarization assertion, §1, p. 3; level-structure conventions, pp. 3–4; standing hypotheses (i)–(iii), p. 5; Theorem 2.1, p. 5; Lemma 2.2, pp. 6–7; Corollary 2.3, p. 7. These printed footer numbers coincide with the physical PDF page numbers in this copy.
- This is an additional supplier for the polarization comparison, not a claim that Deligne's canonical-model theorem alone states that comparison.

### Shimura 1967

G. Shimura, *Construction of class fields and zeta functions of algebraic curves*, Annals of Mathematics 85 (1967), 58–159; bibliographic URL: https://doi.org/10.2307/1970526

The original Main Theorem I was not read. A readable legitimate full-text copy was not obtained; no restricted or unauthorized copy was downloaded. There is consequently no PDF SHA-256 or verified original page/display locator for it in this report. The canonical-model comparison rests on the read Deligne reformulation and Milne exposition, not on a supposed reading of Shimura's original.

## Quote

The following are short verbatim excerpts. Mathematical notation is transcribed in LaTeX; ellipses mark omitted material, not replacement hypotheses.

D, §4.15, p. 150:

> On peut préciser 4.11 et 4.14 en montrant que \({}_K M_{\mathbf C}(G,h)\) est le schéma de modules grossier d'un foncteur évident sur les schémas de type fini sur \(\mathbf C\).

D, §4.16, p. 150:

> Pour \(n \geq 3\), les objets classifiés n'ont plus d'automorphismes et le foncteur \(F\) est représenté par un \(\mathbf Q\)-schéma \({}_{K_n}M\) [6].

This paragraph is the Siegel principally polarized moduli problem with symplectic similitude level structure, not a statement already specialized to the quaternionic polarization-free functor.

D, Theorem 4.21, p. 152:

> Le modèle \(M(G_p,h_o)\) construit en 4.17 est un modèle canonique.

D, Example 5.8, p. 157:

> Pour \((G,h_o)\) comme en 4.9, on construit par 5.7 et 4.21 un modèle canonique \(M(G^o,h_o^o) \subset M(G_p(V,\psi),h_o)\otimes_{\mathbf Q} E(G^o,h_o^o)\).

The superscript `o` is material: it denotes the identity component of the algebraic group. For the type-C datum here, the group is connected, so this does not discard real half planes or determinant components.

M, Theorem 6.8, p. 319:

> The functor \(A \mapsto H_1(A,\mathbf Z)\) is an equivalence from the category AV of abelian varieties over \(\mathbf C\) to the category of polarizable integral hodge structures of type \((-1,0),(0,-1)\).

M, Theorem 8.17, p. 327:

> Then \(\operatorname{Sh}_K(G,X)(\mathbf C)\) classifies the isomorphism classes of quadruples \((A,s,i,\eta K)\)

with, among the listed clauses,

> \(\pm s\) is a polarization of the hodge structure \(H_1(A,\mathbf Q)\),

and condition (**):

> there exists a \(B\)-linear isomorphism \(a:H_1(A,\mathbf Q)\to V\) sending \(s\) to a \(\mathbf Q^\times\)-multiple of \(\psi\).

M, Example 12.4(c), p. 344:

> \(E(G,X)\) is the field generated over \(\mathbf Q\) by \(\{\operatorname{Tr}_X(b)\mid b\in B\}\)

M, Definition 12.8, p. 346, display (54):

> \(\sigma[x,a]_K=[x,r_x(s)a]_K\),

with the printed condition \(\operatorname{art}_{E(x)}(s)=\sigma\). The surrounding statement quantifies every special pair and every \(a\in G(\mathbf A_f)\), and requires the point's coordinates to lie in \(E(x)^{\mathrm{ab}}\).

B, §1, p. 3:

> We now observe that if \((A/S,i)\) is a false elliptic curve, then there is a unique principal polarisation on \(A\) such that if \(s\) is a geometric point of \(S\), then the corresponding Rosati involution on \(\operatorname{End}(A_{\bar s})\) induces \(*\) on \(\mathcal O_D\).

Here the preceding sentence fixes \(t\in\mathcal O_D\), \(t^2=-d\), and defines \(x^*=t^{-1}x^\iota t\). This is exactly the fixed-involution qualification needed; it is not uniqueness of an arbitrary principal polarization after forgetting the involution.

## Standing hypotheses

1. Canonical-model theorem: a reductive Shimura datum, not an arbitrary complex curve. Deligne §4.9 starts with a faithful module over a semisimple algebra with involution, a nondegenerate alternating form satisfying \(\psi(bx,y)=\psi(x,b^*y)\), and the prescribed Hodge homomorphism/positivity. Corollary 5.7 is an inclusion/descent result; Example 5.8 uses the Siegel theorem to construct the PEL canonical model over the reflex field.
2. Milne's PEL statement: the simple type-A or type-C datum, the polarization and similitude level orbit, and the rational comparison (**) are retained. “Simple” describes the algebra/datum, not a requirement that every abelian surface be simple or non-CM. Integral objects are recovered from the Tate lattice and level orbit; an isogeny-class description alone is not yet the project's isomorphism-class functor.
3. Conventions: Milne uses \(h(z)|V^{p,q}=z^{-p}\bar z^{-q}\), (19), p. 282. Deligne 1971 §1.2 uses the positive-exponent convention. The project must translate these conventions, not identify their symbols literally. Milne's positivity is \(\psi(v,Jv)>0\); the project's Riemann form uses \(E(Jv,v)>0\). Thus in the modern convention take \(\psi=-E\). This sign change leaves the adjoint involution and similitude group unchanged.
4. Field/base: this leaf concerns schemes over \(\mathbf Q\), hence characteristic zero and invertible 3. The canonical-model theorem permits compact open level at a prime ramified in the quaternion algebra. Integral smoothness at that prime is a different question.
5. Buzzard: \(D\) is indefinite and non-split, \(\mathcal O_D\) is maximal, and \(d\) is invertible on the base. The polarization statement applies over \(\mathbf Q\). In contrast, the level results in §§1–2 assume the auxiliary level is prime to \(d\), maximality at primes dividing \(d\), full determinant image, and containment in \(V_1(N)\) for \(N\geq4\). They do not apply directly to \(K_3\) at \(3\mid6\).

## What the Lean statement says: unfolded notions

### The moduli objects and the meaning of “every”

- Abelian surface: a proper smooth geometrically integral group scheme over the field, of dimension two; [Objects.lean:160–181](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Objects.lean#L160-L181) and [Structures.lean:222–226](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Structures.lean#L222-L226).
- QM: an injective unital ring map \(\iota:\mathcal O\to\operatorname{End}_K(A)\); [Structures.lean:115–118](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Structures.lean#L115-L118).
- Level: an additive left-\(\mathcal O\)-linear map \(\eta:\mathcal O\to A(K)\) with kernel \(3\mathcal O\); [Structures.lean:140–158](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Structures.lean#L140-L158). In characteristic zero this is a full marking \((\mathcal O/3\mathcal O)_K\simeq A[3]\), not a cyclic subgroup or a single level point: both sides have 81 geometric points. The family predicate explicitly requires bijectivity on every geometric fibre; [ShimuraY3PrintedLeaves.lean:94–108](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean#L94-L108).
- Isomorphism classes: `M3` quotients by actual \(\mathcal O\)-equivariant abelian-variety isomorphisms preserving the marking, not by quasi-isogenies; [Structures.lean:228–236, 288–297](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Structures.lean#L228-L297). A polarization is not a field of this structure.
- `PtEquiv Y`: bijections \(Y(K)\simeq M_3(K)\) for every field \(K/\mathbf Q\); [Pairs.lean:344–361](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Pairs.lean#L344-L361).
- The premise `R1fpPropsAbP`: \(Y/\mathbf Q\) is proper and smooth of relative dimension one; the point bijections are natural under field extensions; a universal `QMAbSchemeP` induces them; and families over proper smooth curves have compatible classifying morphisms. This is a restricted fine-moduli clause list, not a definition of representability on all schemes; [ShimuraY3PrintedLeaves.lean:296–317](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean#L296-L317).
- “Every”: \(\forall(Y,\Phi)\), if that clause list holds, then there exists the required \(\Psi\). It does not assert existence of \(Y\), does not range over arbitrary rational models of the complex curve, and does not supply an integral universal family. The quantifier order is [Y3HodgePrint.lean:935–937](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L935-L937).

### The concrete datum, homology, and conclusion

- Algebra and order: \(B=(2,-3\mid\mathbf Q)\), with \(i^2=2\), \(j^2=-3\), \(ij=-ji=k\); \(\mathcal O=\mathbf Z\langle1,i,(1+j)/2,(i+k)/2\rangle\); [Structures.lean:30–69](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Structures.lean#L30-L69).
- Polarization datum: \(\mu=2j+k\), \(\mu^2=-6\), \(a^\dagger=\mu^{-1}\bar a\mu\), \(E_0(x,y)=\operatorname{trd}(\mu^{-1}x\bar y)\); [Polar.lean:64–95, 127–155](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Polar.lean#L64-L155).
- Finite adelic level: \(K_3=\{g\in\widehat{\mathcal O}^{\times}:g\equiv1\pmod{3\widehat{\mathcal O}}\}\), inside \((B\otimes\mathbf A_f)^\times\); [RayClassShimura.lean:335–350](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/RayClassShimura.lean#L335-L350). `OhatU` is the full group of order units, not `K3Q`; [RayClassShimura.lean:1109–1110](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/RayClassShimura.lean#L1109-L1110).
- Genuine \(H_1\): `H1 A` is the abelianization of \(\pi_1(A(\mathbf C),0)\); [Y3HodgePrint.lean:76–100](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L76-L100). The topology is generated by Zariski-open complex point sets and inverse images of complex balls under regular functions, hence the classical analytic topology. `IsAnalyticHom` is a group homomorphism holomorphic in regular coordinates, not a mere set map; [TailQ.lean:99–111](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/OneProof/H/TailQ.lean#L99-L111).
- Hodge clause: `IsHodgeH1Print P τ` supplies a holomorphic homomorphism \(e:\mathbf C^n\to A(\mathbf C)\), a real-linear isomorphism \(\beta:B_{\mathbf R}\simeq\mathbf C^n\), and the straight-loop classes \(b\mapsto[t\mapsto e(t\beta(b))]\). They biject \(\mathcal O\) with \(H_1(A,\mathbf Z)\), intertwine the actual \(\iota(a)_*\)-action, and satisfy \(\beta(MJ_\tau)=i\beta(M)\); [Y3HodgePrint.lean:473–492](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L473-L492). The real-linear isomorphism forces \(n=2\). Additivity of the loop identification is proved, rather than silently assumed; [Y3HodgePrint.lean:1036–1118](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L1036-L1118).
- Uniformization: \(\Psi:\mathfrak H^{\pm}\times(B\otimes\mathbf A_f)^\times\to Y(\mathbf C)\) is onto, and its fibres are exactly \((z,g)\sim(\gamma z,\gamma gk)\), \(\gamma\in B^\times\), \(k\in K_3\). `DCRelPM` allows either norm sign; [Y3HodgePrint.lean:665–688](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L665-L688).
- Remaining clauses: holomorphy on \(\mathfrak H\) for every \(g\); the above Hodge description at every \([\tau,u]\), \(u\in\widehat{\mathcal O}^\times\); and one pair of conventions \(\varepsilon\in\{1,-1\}\), \(\delta\in\{\mathrm{true},\mathrm{false}\}\) working for all imaginary quadratic fields, CM embeddings, ideles and allowed automorphisms of \(\mathbf C\); [Y3HodgePrint.lean:887–912](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L887-L912). `IsCMPoint` is the eigenvector condition on \((z,1)^t\); `ArtinCondC` specifies the action on every finite abelian extension through the fixed embedding; [RayClassShimura.lean:384–407](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/RayClassShimura.lean#L384-L407).

## Comparison: the necessary consequence steps

### 1. Identify the PEL datum; do not substitute the left regular representation

Take \(V=B\) with the order acting on the left, involution \(\dagger\), and \(\psi=-E_0\) in Milne's convention. The group of \(B\)-linear similitudes is identified with \(B^\times\) by

\[
\rho(g)(v)=vg^{-1},\qquad
\psi(vg^{-1},wg^{-1})=\operatorname{nrd}(g)^{-1}\psi(v,w).
\]

This handles the opposite-algebra issue: \(\operatorname{End}_B(B)=B^{\mathrm{op}}\), and the inverse makes \(\rho\) a group homomorphism. It also gives precisely
\(L_g=B\cap\widehat{\mathcal O}g^{-1}\).

The involution is positive and of Milne's type C. Over a splitting field this is the transpose involution with a symmetric form; its centralizer similitude group is \(\operatorname{GSp}_2\simeq\operatorname{GL}_2\). Thus Deligne's \(G^o\) equals \(G\). Positivity is explicitly supported by the quadratic expression in [Polar.lean:127–150](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/QM/Polar.lean#L127-L150), together with M, §§8.3–8.14. This is an identification argument, not a sentence naming this algebra in D, Example 5.8.

The algebra is indefinite division of discriminant six: the Hilbert symbols are negative at 2 and 3 and positive at infinity and all other primes. The trace-pairing determinant of the displayed order basis is \(-36\), giving reduced discriminant 6 and hence maximality. Exact rational checks reproduced that determinant and the manuscript's determinant-one \(E_0\) Gram matrix.

### 2. Identify the Hodge homomorphism and its sign

For \(\tau=x+iy\), the project's operator is

\[
J_\tau=\frac1y\begin{pmatrix}x&-(x^2+y^2)\\1&-x\end{pmatrix},
\qquad J_\tau(\tau,1)^t=i(\tau,1)^t.
\]

On homology, the Hodge homomorphism acts as right multiplication by \(a+bJ_\tau\). With the preceding group identification, its element of \(B_{\mathbf R}^\times\) is \((a+bJ_\tau)^{-1}\), not the same matrix acting by left multiplication. Conjugating the module by the canonical quaternion involution sends right multiplication by \(J_\tau\) to left multiplication by \(-J_\tau\).

In the modern convention,
\(F^0=\{M:MJ_\tau=-iM\}=\{M:M(\tau,1)^t=0\}\), a holomorphic filtration. The relevant project checks are [Y3HodgePrint.lean:773–876](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L773-L876). They agree with M, §2, pp. 281–283. D, §1.2 has a different exponent convention, so the docstring's attribution of the modern convention to Deligne must be read with this translation. No change to the actual Hodge clause is required.

### 3. Compute the reflex field and retain the whole curve

On \(V_{\mathbf C}/F^0\), the left action of \(B_{\mathbf C}\simeq M_2(\mathbf C)\) is its two-dimensional standard module. Therefore

\[
\operatorname{Tr}_X(b)=\operatorname{trd}(b)\in\mathbf Q,
\qquad E(G,X)=\mathbf Q
\]

by M, Example 12.4(c). The Lie trace/determinant condition of the PEL problem is consequently automatic for a characteristic-zero QM surface of dimension two; it is not being dropped without an argument. “Simple PEL datum” does not exclude CM surfaces.

The rational field is the field of the entire adelic Shimura variety. It is not a claim that each geometric component is defined over \(\mathbf Q\). The component formula M, §5.17 and §13 gives, at this level,
\(\pi_0\simeq\mathbf Q_{>0}^\times\backslash\mathbf A_f^\times/\operatorname{nrd}(K_3)\simeq(\mathbf Z/3\mathbf Z)^\times\): there are two determinant components, exchanged by the nontrivial automorphism of \(\mathbf Q(\zeta_3)/\mathbf Q\). Here the norm subgroup is maximal away from 3 and \(1+3\mathbf Z_3\) at 3. The inverse multiplier of \(\rho\) gives the same subgroup. The Lean premise does not require geometric connectedness, so this field/component distinction is respected.

### 4. Recover the integral object and the exact full level

D, §§4.11–4.12 distinguishes the rational/isogeny description from the integral Tate-lattice object. Apply that lattice construction to \(V_{\mathbf Z}=\mathcal O\), with its perfect \(E_0\) form. Under \(\rho\), the stabilizer of this lattice is \(\widehat{\mathcal O}^\times\), and its principal congruence subgroup at 3 is exactly the code's \(K_3\). A quasi-isogeny identifying these integral lattices is an actual isomorphism; M, Theorem 6.8 supplies the integral Hodge dictionary.

The level marking is allowed to be a similitude, not an exact symplectic marking with a preselected primitive cube root. Every \(\mathcal O\)-linear automorphism of \(\mathcal O/3\mathcal O\) is right multiplication by a unit, and

\[
E_0(ar,br)=\operatorname{nrd}(r)E_0(a,b).
\]

Thus the polarization-compatible level condition is automatic up to its multiplier, rather than omitted arbitrarily. Reduction at the ramified prime still gives 81 elements and 72 units, with 36 of each nonzero multiplier; exact rational/residue checks confirmed this. Restricting to multiplier one or one chosen Weil-pairing value would change the moduli problem and its component field.

At \(u\in\widehat{\mathcal O}^\times\), \(L_u=\mathcal O\); only the marking changes. The leaf's Hodge assertion at these units is therefore the appropriate weakening of the printed moduli description. It does not assert that the same integral lattice describes every nonunit \(g\).

### 5. Justify forgetting the polarization and the fine family

Here is the significant R1 comparison, not merely “neatness”. In B, §1, set \(D=B\), \(d=6\), and \(t=\mu=2j+k\). The hypotheses \(t\in\mathcal O\) and \(t^2=-6\) hold, and the printed involution is exactly \(\dagger\). Buzzard's statement gives a unique principal polarization of that fixed type on every QM surface/family over \(\mathbf Q\), including CM fibres. It makes forgetting that polarization an equivalence of the relevant moduli problems. Uniqueness concerns the polarization homomorphism, not uniqueness of an ample line bundle or uniqueness without fixing \(\dagger\).

The project theorem `lemmaP_H1` identifies the resulting Riemann form with \(E_0\) when the Hodge data have already been supplied; [Y3HodgePrint.lean:1462–1491](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L1462-L1491). That theorem alone is not a global existence statement for all polarization-free objects, because it assumes the Hodge identification. The supplementary printed Buzzard assertion supplies the missing global/family qualification without a circular appeal to the leaf's conclusion.

A fine universal family at full level 3 is an additional moduli construction, not the conclusion of D, §4.15's coarse-model sentence. One explicit characteristic-zero construction uses B, Theorem 2.1 and Corollary 2.3 at \(V_1(5)\), adds full five-markings and the finite étale sheaf \(\operatorname{Isom}_{\mathcal O}(\mathcal O/3\mathcal O,A[3])\), then takes the free quotient changing only the five-marking. The 3-adic Tate lattice is free of rank one over the maximal order of the division algebra \(B_3\); this makes the added marking sheaf nonempty geometrically. A stabilizer would be a polarization-preserving automorphism acting trivially on \(A[3]\); it has finite order and lies in the torsion-free group \(1+3M_4(\mathbf Z_3)\), hence is the identity. Finite étale descent then descends the abelian family, order action, and three-marking. This retains all determinant components.

This names the extra representability/descent argument. It is not an application of Buzzard's level theorem directly at \(3\mid d\), and it is not a certification of the integral version of that construction in another open leaf.

### 6. Pass from the canonical moduli witness to every restricted witness

For the fine moduli model obtained above, D, Theorem 4.21 plus Corollary 5.7/Example 5.8, or M, §14's PEL argument, supplies its canonical rational structure and CM reciprocity. Its universal QM family and classifying property satisfy the restricted premise.

For any other \((Y,\Phi)\) satisfying `R1fpPropsAbP`, apply the restricted classifying property to the canonical model's family. This gives a \(\mathbf Q\)-morphism to \(Y\) agreeing with the moduli classes on field points. Conversely apply the canonical model's property to the family on \(Y\). The composites are the identity on field points; proper smooth curves are reduced, so they are identity morphisms. Thus there is a compatible \(\mathbf Q\)-isomorphism, along which \(\Psi\), holomorphy, and Galois action transfer.

The argument above, for two printed-P families, is external to the code. A related comparison is implemented in [ShimuraY3PrintedLeaves.lean:347–372](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/ShimuraY3PrintedLeaves.lean#L347-L372) for `R1fpPropsAbNP` witnesses (`compare_iso_np`); passing to the printed-P witnesses `R1fpPropsAbP` uses the P/NP conversion theorems at lines 328–337, which take the explicit prerequisite `ObjBridge.TorsionStructure` (corrected 2026-11-18). Canonical-body transport is in [ShimuraY3Print.lean:145–222](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/ShimuraY3Print.lean#L145-L222). The word “every” therefore has a genuine comparison step behind it; it is not a theorem that every arbitrary rational form is canonical.

### 7. Transfer the analytic/H₁ clauses and the half planes

M, pp. 317 and 319 identifies \(H_1(\mathbf C^2/\Lambda,\mathbf Z)\) with \(\Lambda\), and the exponential map identifies the period lattice with \(\ker(\exp_A)\). The straight-loop construction in `IsHodgeH1Print` realizes precisely this identification, including the actual endomorphism action. The project proves its equivalence with the earlier lattice/Hodge clause; [Y3HodgePrint.lean:618–655](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L618-L655).

The double quotient with \(B^\times\) and \(\mathfrak H^\pm\) is identified with the positive-norm quotient on \(\mathfrak H\). A negative-norm unit \(\nu=1+i\), \(\operatorname{nrd}(\nu)=-1\), moves the lower half plane to the upper one; [Y3HodgePrint.lean:697–748](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/Y3HodgePrint.lean#L697-L748). Do not confuse this unit with the different polarization element \(\mu=2j+k\).

Onto plus the fibre equivalence is the printed quotient bijection. Holomorphy of its parametrizations follows from the analytic uniformization and the algebraic comparison isomorphism. Requiring this rather than an explicit biholomorphism, and retaining the moduli clause only at order units, are weakenings.

### 8. Specialize the reciprocity law, with one consistent convention

For an imaginary quadratic embedding \(q:K\hookrightarrow B\) satisfying the eigenvector condition, the torus is \(\operatorname{Res}_{K/\mathbf Q}\mathbf G_m\). With the right-inverse group representation above and the matching embedding \(\kappa\), the Hodge cocharacter on this torus is \((z^{-1},1)\); the reflex norm in M, (52)–(53), becomes the corresponding inverse finite-idele embedding. Changing the Artin convention changes one uniform inversion; conjugating the selected embedding changes one uniform CM-type convention. This provides a fixed allowed pair \((\varepsilon,\delta)\), not choices made separately for each point or field.

M, Definition 12.8 and (54) then gives the actual Lean equation
\(\sigma\Psi(z,g)=\Psi(z,\widehat q(s_f)^\varepsilon g)\)
for every permitted \(g\), idele and automorphism. `ArtinCondC` in particular forces the automorphism to fix the embedded quadratic field and specifies its action on the finite abelian extensions, matching the printed restriction to \(E(x)^{\mathrm{ab}}\).

This clause does not assert an action of arbitrary elements of \(G(\mathbf A_f)\) on the fixed-level scheme. It is the special-point formula with a left torus factor and a fixed representative. D, §1.8 and M, §5.29 place the general right adelic action on the tower, not on each arbitrary fixed level. The second R1 risk about an unrestricted fixed-level action is therefore absent from this Prop.

## False, incomplete or unclear

- False: no counterexample or false assertion was found in the actual Prop.
- Incomplete attribution: D, §4.21 is the Siegel canonical-model theorem; Corollary 5.7 is an inclusion/descent theorem; Example 5.8 supplies the PEL canonical model. None of these alone prints the whole polarization-free, full-three, every-restricted-witness implication. The steps above, especially 4–6, must remain explicit GLUE.
- Unclear convention in the docstring: its “Deligne's convention” is not literally the exponent convention of the 1971 exposé. The modern H₁ interpretation, the opposite-algebra representation, and the Riemann-form sign need to be stated consistently. The actual Hodge condition is supported after that translation.
- Not a stronger integral assertion: the universal family and proper smooth rational curve occur in the premise. The conclusion does not give representability over \(\mathbf Z[1/6]\) or \(\mathbf Z[1/30]\), good reduction at 3, a universal family over an integral canonical model, or a rational model of each geometric component.
- Not discharged by an equivalence to an older open leaf: `print_iff_deligneH` is useful internal transport, but equivalence of two open hypotheses does not independently verify either against the literature.

## Manuscript passages checked

The [six-contact construction, lines 411–477](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/diophantine_zq.tex#L411-L477) fixes \(B,\mathcal O,\mu,E_0\), the level \(K_3\), all determinant components, and the auxiliary-five construction. The [homology argument, lines 564–577](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/diophantine_zq.tex#L564-L577) invokes the equivalence between polarizable complex tori and abelian varieties. These passages were read as the intended application. The integral model, the normalizer quotient, branch indices, and the ensuing height argument were not certified by this statement check.

## Not read

- Shimura's 1967 original Main Theorem I and its proof; its locator remains unverified here.
- A comparison of Buzzard's corrected author copy with the Duke journal typesetting.
- The originals cited for Buzzard's polarization assertion: Boutot–Carayol III.1.5 and the Proposition in §11 of reference [B]. This report relies on Buzzard's explicit primary-source restatement, not a claim to have read those originals.
- A complete audit of the proofs and cited suppliers behind Deligne's and Milne's canonical-model, Riemann, representability, and descent results was not performed. The cited statements, standing hypotheses, and selected arguments were read; not every proof or cited supplier was read.
- Other open research leaves, the integral auxiliary-five argument over general bases, or an unconditional proof of the project's final theorem.

No repository file, Git state, review record, issue, or comment was changed. No Lean compilation, build, or fresh transitive-axiom audit was run.

## AI use

An AI language model performed source discovery, reading of the pinned Lean definitions and legitimate source PDFs, mathematical comparison, and report drafting. `curl` retrieved the permitted copies; `pdftotext` extracted searchable text; rendered source pages were checked against decisive quotations and formulas. Exact rational arithmetic reproduced the order discriminant, principal-form Gram determinant, and the finite level-multiplier checks. Those computations verify the concrete dictionary only, not the canonical-model theorem.

Evidence: AI-READ. No human reading or human-review credit is claimed.

## Locator recommendation

Retain CONSEQUENCE / GLUE for the whole implication. A more precise source line would cite D, §§4.9–4.12, Theorem 4.21, Corollary 5.7 and Example 5.8; M, Theorems 6.8 and 8.17, Example 12.4(c), Definition 12.8 with (54), and the PEL canonical-model passage on pp. 354–355; plus B, §1 p. 3 for the global fixed-\(\mu\) polarization comparison. State the full-three fine-level/descent and every-witness transport steps separately. Do not mark Shimura's original locator or the integral-model leaf verified on the strength of this report.
