Recorded from the statement-check sweep of 2026-11-18, against OPEN.md commit `2895a9c195344cdbca2454ba9bf58d748a3a9ce5` (AI-READ). This report was produced by an AI agent run by the project. Jack McCarthy is accountable for the project's posted checks; that does not mean that this report was read or verified by a person. No person independently checked it. This recording changes no flags, ratings or counts and discharges no Lean theorem. Sources not read and AI use are disclosed below.

---

# Statement check: carayolThmAFrob

**Verdict: CONSEQUENCE.** The entire Lean proposition follows from Darmon–Diamond–Taylor (DDT), Theorem 3.1(a)–(d), using its standing definitions and Theorem 1.22 for the newform dictionary. No conclusion stronger than that printed package was found. It is not a verbatim transcription of Carayol's Théorème (A) alone.

**Evidence: AI-READ.** This is a source-based statement check, not a human reading or a new compilation/proof audit.

## Field and commit

- OPEN field: `HDec.HSyn.OpenResearchLeaves65.carayolThmAFrob`.
- Lean proposition: `CarayolRefold.CarayolThmAFrob`.
- Commit of OPEN and all project source examined: `2895a9c195344cdbca2454ba9bf58d748a3a9ce5`.
- [OPEN entry, lines 250–262](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/OPEN.md#L250-L262).
- [Definition, CarayolRefold.lean:245–275](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolRefold.lean#L245-L275); [docstring:218–244](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolRefold.lean#L218-L244).
- Checklist followed: [STATEMENT-CHECKS.md at the same commit](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/docs/one-proof/STATEMENT-CHECKS.md).
- Reading date: November 18, 2026. All project reads were revision-pinned Git object reads. No repository file, issue, comment, reading register, or classification was changed; no build was run.

All code locations below are public revision-pinned source links, not local checkout locations.

## Edition, page, display; copy; source URLs and hashes

### DDT — the sufficient printed package

Henri Darmon, Fred Diamond and Richard Taylor, *Fermat's Last Theorem*. **Copy:** author-hosted PDF, title page dated September 9, 2007. The author's [publication list](https://www.math.mcgill.ca/darmon/pub/pub.html) identifies this survey as *Current Developments in Mathematics* 1 (1995), pp. 1–157, and records its 1997 International Press reprint in *Elliptic curves, modular forms & Fermat's last theorem*, pp. 2–140.

- PDF: https://www.math.mcgill.ca/darmon/pub/Articles/Expository/05.DDT/paper.pdf
- SHA-256: `254f6e29957f95219eff046c29478f5ee584615bee12c8aa8357f499c8cbe8b3`
- Displays read: Definition 1.21 and Theorem 1.22, p. 31; §2.1 conventions and conductor definition, pp. 50–54; §3.1 construction, pp. 84–85; Theorem 3.1 heading, p. 85, with (a)–(d) on p. 86; accompanying discussion on pp. 86–87.
- These are the folios of the downloaded author copy, also its PDF page numbers. The separate 1995 journal and 1997 book layouts were not collated. Thus the theorem locator is checked in an author copy, not a claim that these folios are identical across editions.

### Carayol — normalization and local–global compatibility

Henri Carayol, *Sur les représentations l-adiques associées aux formes modulaires de Hilbert*, *Annales scientifiques de l'École Normale Supérieure*, fourth series, 19(3) (1986), pp. 409–468. **Copy:** NUMDAM journal scan.

- PDF: https://www.numdam.org/item/ASENS_1986_4_19_3_409_0.pdf
- SHA-256: `d4a5fb6b1cd76f944f8948e06df1c7ad5656ae5ee14b9189178ee1e8f2b0dab8`
- Displays read: §0.3 and the beginning of §0.4, p. 409; §0.4–§0.6 and the beginning of Théorème (A), p. 410; completion of Théorème (A) and the irreducibility remark, p. 411.
- PDF pages 2–4 are printed pp. 409–411; the first PDF page is the archive cover.

### Casselman — newvectors and the conductor calculation

William Casselman, *On Some Results of Atkin and Lehner*, *Mathematische Annalen* 201 (1973), pp. 301–314. **Copy:** Göttingen library digitization, including its archive cover, openly hosted among Didier Lesesvre's CNRS mathematical references.

- PDF: https://lesesvre.perso.math.cnrs.fr/newforms-references/casselman.pdf
- SHA-256: `7f91ebae1a8f5e695800f4afb9fc06d0e2ea0b3a476751a31a7c8c3f38ad537d`
- Displays read: local standing conventions, p. 301; Theorem 1 and (1.1), p. 302; local calculation, pp. 303–306; conductor/epsilon-factor remark beginning on p. 306 and ending at the top of p. 307.
- PDF pages 2–8 are printed pp. 301–307. The article pages are image-only: text extraction did not recover their statements, so the page images were read directly.

No inaccessible or unauthorized copy was used. The original Ribet and Shimura locators are distinguished below from the clauses proved by DDT.

## Quote

The following are short verbatim textual quotations; mathematical typography and subscripts are transcribed, not copied from the OCR's corrupted glyphs.

### DDT

Theorem 3.1(a), p. 86:

> If $p\nmid N\ell$ then $\rho$ is unramified at $p$ and $\rho(\mathrm{Frob}_p)$ has characteristic polynomial
> $$X^2-a_pX+p\psi(p).$$

Theorem 3.1(b), first assertion, p. 86:

> $\det(\rho)$ is the product of $\psi'$ with the $\ell$-adic cyclotomic character $\epsilon$,

Theorem 3.1(c) and (d), p. 86:

> $\rho$ is absolutely irreducible.

> The conductor $N(\rho)$ is the prime-to-$\ell$-part of $N$.

Theorem 1.22, first sentence, p. 31:

> If $f$ is in the new subspace of $S_2(\Gamma)$ and is an eigenvector for all the operators in $\mathbb T_0$, then it is also an eigenform for $\mathbb T$, and hence is unique up to scaling.

Frobenius convention, p. 50:

> the automorphism of $\overline{\mathbf F}_p$ which raises elements of $\overline{\mathbf F}_p$ to their $p$th power.

Conductor display and product convention, p. 54:

> $$m_p(\rho)=\int_{-1}^{\infty}\operatorname{codim}\rho^{I_p^u}\,du
> =\operatorname{codim}\rho^{I_p}+\int_0^{\infty}\operatorname{codim}\rho^{I_p^u}\,du.$$

> where the product is over all primes $p\ne\ell$ in the case of an $\ell$-adic or mod $\ell$ representation

### Carayol

§0.4, p. 409:

> Nous normalisons l'isomorphisme de la théorie du corps de classes de sorte que les éléments de Frobenius géométriques correspondent aux uniformisantes.

§0.5, p. 410, the principal-series formula:

> $$\sigma(\pi_{\mathfrak p})=\xi_1^{-1}\cdot\omega_{\mathfrak p}^{-1/2}\oplus\xi_2^{-1}\cdot\omega_{\mathfrak p}^{-1/2}.$$

Théorème (A), pp. 410–411:

> Soit $\pi$ comme en (0.3). Il existe alors une extension finie $E$ de $\mathbf Q(\pi)$ et un système strictement compatible $\{\sigma^\lambda\}$ de représentations continues $E_\lambda$-adiques de dimension 2 du groupe de Galois $\operatorname{Gal}(\overline F/F)$,

> pour toute place finie $\mathfrak p$ de $F$, et pour toute place finie $\lambda$ de $E$, de caractéristique résiduelle différente de celle de $\mathfrak p$, la restriction $\sigma_{\mathfrak p}^\lambda$ de $\sigma^\lambda$ au groupe de Weil local $W_{F_{\mathfrak p}}$ est équivalente à $\sigma^\lambda(\pi_{\mathfrak p})$.

Remark, p. 411:

> On peut montrer (K. Ribet, non publié) que la représentation $\sigma^\lambda$ est nécessairement irréductible.

The omitted connective in the theorem quotation is not a change to its quantifiers: its first quoted fragment gives the existence conclusion and its second gives the complete local compatibility clause.

### Casselman

Theorem 1, p. 302:

> Let $\varrho$ be an irreducible admissible infinite-dimensional representation of $\mathrm{GL}_2(k)$

For the space of vectors satisfying (1.1), at the largest permissible level ideal $\mathfrak c(\varrho)$ for which a nonzero vector exists, the theorem concludes:

> Then this space has dimension one.

Remark, p. 306:

> The conductor of a representation turns out to be the same conductor one would naturally associate to the representation through its zeta-function.

The continuation at the top of p. 307 gives the epsilon factor in the form

$$\epsilon(s,\varrho,\psi)=\epsilon(\varrho,\psi)\,N\mathfrak p^{(2c(\psi)-\delta)s}$$

and says:

> The ideal $\mathfrak p^\delta$ is the same as our $\mathfrak c(\varrho)$.

## Standing hypotheses

### DDT

- The form is a cuspidal, normalized **newform of weight two**, of its new level $N_f$; its character is the eigencharacter of the diamond operators. Definition 1.21 uses Petersson orthogonality to the span of the lower-level degeneracies $g(az)$.
- Theorem 1.22 promotes a newspace eigenvector for the good Hecke algebra $\mathbb T_0$ to a full Hecke eigenform. Thus requiring only good eigen-ness in the Lean structure does not admit an extra class of forms.
- $K_f$ is the number field generated in $\mathbf C$ by the Fourier coefficients. In §3.1 the character is a homomorphism into $K_f^\times$, not merely into $\mathbf C^\times$.
- The coefficient construction on p. 85 is over $K_f\otimes\mathbf Q_\ell$, a product of completions at **all** primes over $\ell$. Projecting to the desired factor gives $K_{f,\lambda}$. Alternatively, in its later $K_f'$ notation take the auxiliary field $K=\mathbf Q_\ell$ and embeddings inducing that $\lambda$.
- The Galois representation is continuous for the profinite Galois topology and the local coefficient topology. DDT additionally requires an $\ell$-adic representation to be unramified almost everywhere; the Lean good-prime clause already implies this.
- Frobenius is arithmetic: residue-field $p$th power. The cyclotomic character has value $p$ there.
- $m_p$ and $N(\rho)$ omit $p=\ell$ for an $\ell$-adic representation. DDT's $I_p^u$ agrees with the usual absolute upper filtration for $u>0$. Its different convention at $u=-1$ does not enter the Lean integral.
- The restrictions involving odd $\ell$ in the later parts of Theorem 3.1 do **not** apply to (a)–(d). No condition $\ell\nmid N$, squarefreeness of $N$, primitivity of the character, or absence of complex multiplication is imposed here.

### Carayol

- $F$ is totally real of finite degree $d$; the archimedean components are $D_{k_i,w}$, with $k_i\ge2$ and all $k_i,w$ of the same parity. The representations are cuspidal automorphic representations.
- When $d$ is even, §0.3 requires an essentially square-integrable component at a finite place. For the present specialization $F=\mathbf Q$, $d=1$, so that hypothesis is inapplicable. The unitary weight-two normalization has $w=0$.
- Induction in §0.5 is normalized/unitary induction. Reciprocity sends geometric Frobenius to a uniformizer. The character $\omega_{\mathfrak p}$ is the local absolute value, so over $\mathbf Q_p$ it takes value $p^{-1}$ at geometric Frobenius and $p$ at arithmetic Frobenius.
- Théorème (A) is over a **finite extension $E$** of the rationality field. It gives local compatibility at every finite place whose residue characteristic differs from that of the coefficient place. It does not require the local prime to be odd.

### Casselman

- In §1, $k$ is a locally compact non-archimedean field, $\mathfrak o_k$ its integers, $\mathfrak p$ its maximal ideal, and $\varpi$ a uniformizer.
- $\varrho$ is irreducible, admissible and infinite-dimensional. Its scalar/central character is denoted $\varepsilon$ in Theorem 1.
- $\Gamma_0(\mathfrak b)$ consists of integral invertible matrices whose lower-left entry is in $\mathfrak b$. Equation (1.1) uses the **upper-left** character $\varepsilon(a)$; its largest level ideal with a nonzero vector is $\mathfrak c(\varrho)$.
- The conductor exponents of principal, special and cuspidal representations are discussed in the proof, not all in the one-dimensionality statement of Theorem 1. The epsilon-factor identification is a separate concluding remark, pp. 306–307.

## Unfolding the Lean objects

The project revision's [dependency manifest](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/lake-manifest.json) pins Mathlib to `56a005855ea17e0b0958f73ec801ae140b0a1679`. Mathlib locations below refer to that revision, obtained from its public source, not from a moving dependency checkout.

### 1. The form, level, weight and newness

[`Newform.lean:85–109`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Newform.lean#L85-L109) defines `EigenformAwayFromLevel` as a nonzero Mathlib cusp form on $\Gamma_1(N)$, with a unit-valued character, membership in its diamond eigenspace, and simultaneous Hecke eigen-ness at positive indices coprime to $N$. `Newform` adds membership in the new subspace and $(qExpansion\ 1\ f).coeff\ 1=1$.

- [`LadicCond.lean:125–130`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Conductor/LadicCond.lean#L125-L130) makes `CF N k` a Mathlib `CuspForm` and `coeff f m` its period-one q-expansion coefficient. The coefficient field uses the identical formula in [`I4Layer.lean:1233–1238`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/G9/I4Layer.lean#L1233-L1238), imported by [`DSCoeffExt.lean:39–42`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L39-L42).
- Mathlib [`ModularForms/Basic.lean:75–85`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ModularForms/Basic.lean#L75-L85): a `CuspForm` is a slash-invariant function, holomorphic on the upper half-plane and vanishing at every cusp.
- Mathlib [`CongruenceSubgroups.lean:78–97`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L78-L97) and [`132–137`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/ModularForms/CongruenceSubgroups.lean#L132-L137) are the usual $\Gamma_0(N)$ and $\Gamma_1(N)$ matrix congruences.
- [`Newforms/Basic.lean:106–110`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Basic.lean#L106-L110) defines the oldspace as the span/supremum of degeneracies from $M\ne N$ with $dM\mid N$; [`203–205`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Basic.lean#L203-L205) defines the newspace as its Petersson-orthogonal complement. These conditions force $M<N$ and $d>0$, since $N>0$.
- [`Degeneracy.lean:389–405`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Degeneracy.lean#L389-L405) identifies the degeneracy with $f(dz)$, without a stray power of $d$.
- [`Petersson/Orthogonal.lean:99–106`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Petersson/Orthogonal.lean#L99-L106) means pairing to zero against every oldform. The pairing is the coset sum in [`Petersson/FiniteIndex.lean:95–102`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Petersson/FiniteIndex.lean#L95-L102), with each summand the actual Petersson integral in [`Petersson/Basic.lean:100–107`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Petersson/Basic.lean#L100-L107).
- The ring/classical Hecke dictionary is [`Nebentypus/Eigenvector.lean:89–95`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/HeckeSlash/Nebentypus/Eigenvector.lean#L89-L95). The source also contains the promotion to a full eigenform in [`FullEigenform.lean:122–157`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/FullEigenform.lean#L122-L157). The printed promotion needed for this statement check is DDT Theorem 1.22.

### 2. The character is the printed nebentypus, not its inverse

[`DiamondOperators.lean:225–240`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/DiamondOperators.lean#L225-L240) defines the diamond operator by slashing with a $\Gamma_0(N)$ matrix of the specified **lower-right** entry. [`280–295`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/DiamondOperators.lean#L280-L295) defines `cuspFormCharSpace` as its joint $\chi(d)$ eigenspace. [`377–380`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/DiamondOperators.lean#L377-L380) gives exactly the classical relation $f|_k\gamma=\chi(d_\gamma)f$.

Thus $\psi=f.\chi$ agrees with DDT's diamond eigencharacter. At a good prime, the unique unit $u=p\bmod N$ exists because $p\nmid N$. The zero-extended Dirichlet version is defined in [`Newform.lean:133–160`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/TauCeti/NumberTheory/ModularForms/Newforms/Newform.lean#L133-L160). Weight-two parity $\psi(-1)=1$ is recorded in [`CarayolDDTOdd.lean:138–141`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolDDTOdd.lean#L138-L141).

### 3. $K_f$, $\lambda$ and $K_{f,\lambda}$

[`DSCoeffExt.lean:348–354`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/DSCoeffExt.lean#L348-L354) defines

$$K_f=\operatorname{IntermediateField.adjoin}_{\mathbf Q}(\operatorname{range}(n\mapsto a_n(f)))\subseteq\mathbf C.$$

It is not an arbitrary coefficient field. The Lean assumption `[NumberField K_f]` means characteristic zero and finite dimension over $\mathbf Q$: Mathlib [`NumberField/Basic.lean:40–45`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/NumberField/Basic.lean#L40-L45).

`HeightOneSpectrum (𝓞 K_f)` is a nonzero prime ideal of the ring of integers, hence maximal: Mathlib [`Ideal/Lemmas.lean:487–501`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/DedekindDomain/Ideal/Lemmas.lean#L487-L501). The hypothesis $\ell\in\lambda$ says that it lies over $\ell$.

`lam.adicCompletion K_f` wraps the uniform-space completion of the $\lambda$-adic valued field: Mathlib [`AdicValuation.lean:601–608`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L601-L608), with the transported topology at [`660–663`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L660-L663) and canonical algebra map at [`896–922`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/DedekindDomain/AdicValuation.lean#L896-L922). Its local norm is in Mathlib [`FinitePlace.lean:161–163`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/NumberTheory/NumberField/Completion/FinitePlace.lean#L161-L163). In particular $\ell\in\lambda$ gives $\|\ell\|<1$; see [`CarayolHerbrand.lean:263–270`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolHerbrand.lean#L263-L270).

### 4. Global/local groups and the representation

[`LadicCond.lean:43–54`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Conductor/LadicCond.lean#L43-L54) defines `Qbar := AlgebraicClosure ℚ` and `GQ := Qbar ≃ₐ[ℚ] Qbar`. The Krull topology is Mathlib's Galois topology. The witness in the target is a group homomorphism into the invertible $2\times2$ matrices over $K_{f,\lambda}$, with `Continuous ρ` as a separate required conjunct; it is not a finite-image or residual representation.

[`LadicCond.lean:107–116`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Conductor/LadicCond.lean#L107-L116) defines `GQp p` using `PadicAlgCl p`, and `decomp p` by Mathlib's absolute Galois group map for $\mathbf Q\to\mathbf Q_p$. Precomposing $\rho$ with this map is its local restriction. DDT p. 51 explains the decomposition subgroup identification and conjugacy dependence of the chosen place.

### 5. Places, inertia and arithmetic Frobenius

`LiesOver v p` is $(p:\overline{\mathbf Q})\in v.nonunits$. `IsArithFrob σ v p` means that $\sigma$ stabilizes $v$ and

$$\sigma(x)-x^p\in\mathfrak m_v\quad\text{for every }x\in v.$$

The defining equations are [`LadicCond.lean:48–54`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Conductor/LadicCond.lean#L48-L54). Mathlib [`ValuationSubring.lean:595–620`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Valuation/ValuationSubring.lean#L595-L620) identifies `nonunits` with the image of the maximal ideal. These are ordinary places of $\overline{\mathbf Q}$ over $p$, not a choice of geometric Frobenius.

Mathlib [`RamificationGroup.lean:27–30`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Valuation/RamificationGroup.lean#L27-L30) defines the decomposition subgroup as the stabilizer of the valuation subring, and [`47–51`](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/RingTheory/Valuation/RamificationGroup.lean#L47-L51) defines inertia as the kernel of its action on the residue field. Thus the target's equation $\rho(\sigma)=1$ on every inertia group is exactly unramifiedness.

### 6. Irreducibility

[`CarayolRefold.lean:252–256`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolRefold.lean#L252-L256) quantifies over every Mathlib `Submodule` of $K_{f,\lambda}^2$. A subspace stable under multiplication by every $\rho(\sigma)$ must be zero or the whole space. This is ordinary irreducibility over $K_{f,\lambda}$, not absolute irreducibility, irreducibility of a residual reduction, or a Burnside spanning assertion.

### 7. The conductor really uses absolute upper numbering

All definitions in this paragraph are in [`LadicCond.lean:188–300`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/HDecomp/Conductor/LadicCond.lean#L188-L300):

- `inertiaSet`, line 196: $\|\sigma x-x\|<1$ for every integral $x\in\overline{\mathbf Q}_p$; this is the kernel of the residue-field action.
- `invariants`, lines 228–238: the subspace of vectors fixed by every element of the given set.
- `codimInv`, lines 241–242: $n-\dim V^S$. The invariant subspace lies in finite-dimensional $V$, so natural-number subtraction is the usual nonnegative codimension.
- `Fld`, `IsFinGal`, `ramSet`, `ramCard`, lines 192, 223, 213–220: finite Galois intermediate fields $L/\mathbf Q_p$; the preimages of the lower groups defined by $v_L(\sigma x-x)\ge i+1$ on $\mathfrak o_L$; and their finite restriction-image cardinalities $g_i$.
- `ramSetR`, line 282: real lower numbering by the ceiling index; `phiAt`, lines 289–290: $\varphi(u)=\int_0^u g_t/g_0\,dt$; `upperSet`, lines 294–295: lower numbering at its inverse threshold.
- `upperAbs`, lines 299–300: the elements whose restriction lies in the upper group at every finite Galois level. It is the absolute upper filtration, not lower numbering or an arbitrary finite-level substitute.

The target, [`CarayolRefold.lean:272–275`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolRefold.lean#L272-L275), uses the real Lebesgue integral over $u>0$, with the inertia codimension added separately. `N.factorization p` is $v_p(N)$ for a prime $p$ and $N>0$.

The existing [`CarayolHerbrand.lean:324–332`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolHerbrand.lean#L324-L332) explicitly relates this integral to `condExp` for a continuous representation over the indicated completion, when $p\ne\ell$. The printed DDT definition already has the integral form required here; reliance on a lower/upper conversion is not needed merely to read this leaf against DDT.

## Comparison, clause by clause

1. **Quantifier order and common witness — YES.** For every positive $N$, every indicated normalized weight-two newform, every prime $\ell$, and every prime $\lambda$ of $K_f$ over $\ell$, the Lean chooses **one** $\rho$ satisfying all the subsequent conjuncts. DDT constructs one such representation and lists its simultaneous properties. Lean does not choose a different representation for each property, nor assert the properties of every representation.

2. **Newform hypothesis and exact level — CONSEQUENCE.** The oldspace and Petersson newspace agree with DDT Definition 1.21. The Lean structure initially assumes only good Hecke eigen-ness; DDT Theorem 1.22 supplies the full eigenform hypothesis. Thus $N$ is the actual new level, not an arbitrarily enlarged oldform level. This step matters for the conductor equality.

3. **Weight, character, and boundary conditions — YES.** Weight is exactly two. The diamond eigencharacter is $\psi$, not $\psi^{-1}$; $a_1=1$ and cuspidality are present. $N=0$ is excluded; $N=1$ is not excluded. Character values at bad primes are not invoked in the Frobenius clause. There is no missing squarefree-level, primitive-character, non-CM, or odd-$\ell$ hypothesis.

4. **Coefficient field and every $\lambda$ — CONSEQUENCE.** Use the $\lambda$ factor of the printed $K_f\otimes\mathbf Q_\ell$ construction on p. 85 and identify it with the completion used by Lean, respecting the canonical image of $K_f$. This supplies every place over $\ell$, including $\ell=2$ and $\ell\mid N$. It requires no descent from Carayol's extension field $E$: the DDT construction already supplies the smaller field.

5. **Continuity and dimension — YES.** The representation is continuous and two-dimensional over the characteristic-zero local field. The good-prime condition also gives the almost-everywhere unramifiedness included in DDT's terminology. No finiteness of the image or irreducibility modulo $\lambda$ is demanded.

6. **(i) Irreducibility — CONSEQUENCE.** The stable-$K_{f,\lambda}$-subspace condition follows from DDT 3.1(c)'s absolute irreducibility: a nonzero proper stable subspace remains such after scalar extension to an algebraic closure. The precise existing scalar-extension argument is [`CarayolDDTOdd.lean:145–208`](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolDDTOdd.lean#L145-L208). No original Ribet theorem-number verification is needed for this implication.

7. **Unramifiedness and all places/lifts — YES.** For a prime $p$, $p\nmid N\ell$ is exactly the printed good-prime condition. Triviality on every inertia group is the printed definition of unramifiedness. DDT pp. 51–52 makes the place dependence conjugacy-invariant; after killing inertia, all lifts of arithmetic Frobenius give the same image at a fixed place. Trace and determinant are conjugacy-invariant, so the universal formulation over places and Frobenius lifts adds no condition beyond the print.

8. **(ii) Trace, determinant, and characteristic polynomial — CONSEQUENCE.** From DDT 3.1(a), extract the trace and determinant coefficients of the $2\times2$ characteristic polynomial. The result is $\operatorname{tr}=a_p$ and $\det=p\psi(p)$, mapped from $K_f$ into $K_{f,\lambda}$. Conversely these two coefficients describe that characteristic polynomial. Arithmetic Frobenius is the $p$th-power residue automorphism in both sources. The determinant has a **positive** $p\psi(p)$ term, not $p^{-1}\psi(p)$ or $p\psi(p)^{-1}$.

   The literal Lean determinant clause is conditional: for every $u$ and $b\in K_f$ satisfying $u=p\bmod N$ and $b=p\psi(u)$ in $\mathbf C$, it asserts $\det\rho(\sigma)=b$ in the completion. It does not independently assert existence of $b$. DDT §3.1 supplies $\psi(u)\in K_f$, so the unique intended $b$ exists. This packaging is not stronger than the print; without the field-membership fact it would be weaker, potentially vacuous at that value.

9. **(iii) Prime-to-$\ell$ conductor — CONSEQUENCE.** DDT 3.1(d) gives $N(\rho)=N/\ell^{v_\ell(N)}$. Taking the exponent at each $p\ne\ell$ and substituting DDT's definition on p. 54 gives

   $$\operatorname{codim}V^{I_p}+\int_{u>0}\operatorname{codim}V^{G_{\mathbf Q_p}^u}\,du=v_p(N).$$

   For $u>0$, DDT's $I_p^u$ and the Lean absolute upper group are the same. The endpoint $u=0$ has zero Lebesgue measure. DDT also notes finiteness of the wild-inertia image, making the Swan integral well-defined; the intended printed witness therefore has the required integrable conductor function. The Lean statement does **not** claim an Artin-conductor equality at $p=\ell$, where such a claim would be problematic for an $\ell$-adic representation. It includes all primes $p\ne\ell$, not only $p\mid N$ or the primes of conductor exponent one.

10. **No extra conclusions — YES.** The leaf does not assert a compatible family as $\lambda$ varies, an integral lattice, absolute irreducibility, a global determinant identity, a specified matrix for complex conjugation, local Weil–Deligne compatibility, or the extra local-at-$\ell$ conclusions in DDT 3.1(f)–(g). Those printed conclusions are not silently added to the Lean proposition. Oddness is proved downstream, not an additional open clause here.

## Arithmetic versus geometric Frobenius: checking the manuscript normalization

The manuscript passage examined is [diophantine_zq.tex:9773–9806](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/diophantine_zq.tex#L9773-L9806), particularly lines 9778–9797.

Let the good local component of the unitary automorphic representation be $\Pi_{f,p}=\operatorname{Ind}(\mu_1,\mu_2)$, with

$$a_p=\sqrt p\,(\mu_1(p)+\mu_2(p)),\qquad \mu_1(p)\mu_2(p)=\psi(p).$$

Carayol §0.5 applied to $\Pi_{f,p}^{\vee}$ gives

$$\sigma(\Pi_{f,p}^{\vee})=\mu_1\omega_p^{-1/2}\oplus\mu_2\omega_p^{-1/2}.$$

On **geometric** Frobenius its eigenvalues are $\sqrt p\,\mu_i(p)$, because the uniformizer corresponds to geometric Frobenius and $\omega_p(p)=p^{-1}$. Now set $\rho_f=\sigma(\Pi_f^{\vee})^{\vee}$, as the manuscript does. Passing from geometric to arithmetic Frobenius inverts eigenvalues; taking the Galois dual also inverts them. Therefore $\rho_f$ on **arithmetic** Frobenius has eigenvalues $\sqrt p\,\mu_i(p)$, giving exactly

$$X^2-a_pX+p\psi(p).$$

Both the automorphic contragredient and the Galois dual are essential to this comparison. There is no convention mismatch in the cited manuscript calculation. For the same final $\rho_f$, using geometric Frobenius instead would give reciprocal eigenvalues and reciprocal determinant, not the polynomial asserted in Lean.

The alternate route used in [`frob_of_DDT31`, CarayolRefold.lean:309–332](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolRefold.lean#L309-L332) also has the correct normalization: the mod-$N$ cyclotomic character sends arithmetic Frobenius to $p\bmod N$, and the $\ell$-adic cyclotomic character sends it to $p$. DDT 3.1(b)'s global determinant becomes $\psi(p)p$ there. This existing implication was inspected as source text; its input [`CarayolDDT31`, CarayolDDTOdd.lean:275–312](https://github.com/Deicyde/diophantine-z-q/blob/2895a9c195344cdbca2454ba9bf58d748a3a9ce5/ZInQKernel/Contrib/OneProof/CarayolDDTOdd.lean#L275-L312) was unfolded rather than trusted merely because the implication already existed.

## Locator findings and the additional steps actually needed

- **DDT 3.1(a)–(d): confirmed in the author copy.** The heading starts on p. 85 and all four clauses are printed on p. 86. The conductor convention is in §2.1 on p. 54. Add **Theorem 1.22, p. 31**, when documenting the equivalence of this good-eigenform-based Lean structure with the printed full-newform definition.
- **Carayol §§0.3–0.7 and Théorème (A), pp. 409–411: correct locator.** However, Théorème (A) itself gives a system over a finite extension $E/\mathbf Q(\pi)$ and local compatibility. It does not itself print ordinary/absolute irreducibility as a theorem clause or assert realization over the exact field $K_{f,\lambda}$. The irreducibility sentence on p. 411 explicitly says **“K. Ribet, non publié.”** It should not be used as the sole printed proof of clause (i). DDT 3.1(c) supplies a printed statement, and its p. 85 construction supplies the exact coefficient-field realization.
- **Casselman Theorem 1, p. 302: correct for newvector uniqueness.** Principal-series conductor is the product of the two inducing-character conductor ideals; the special-representation calculation on p. 306 gives exponent one for an unramified twist and twice the character exponent for a ramified twist. The cuspidal argument on pp. 303–304 has exponent at least two. These agree with the manuscript's local classification, but are not themselves a global Galois-conductor theorem.
- **Casselman conductor/epsilon-factor locator needs precision.** The identification needed in a Carayol-plus-local-correspondence derivation is the concluding remark on **pp. 306–307**, not just Theorem 1's statement on p. 302. The final equality of its level conductor with the epsilon-factor exponent is printed at the top of p. 307, outside the recorded “pp. 302–306” range. For that narrower identification, citing only Theorem 1 or only pp. 302–306 is incomplete; the corrected locator is the closing remark, pp. 306–307. DDT 3.1(d) already packages the required equality, so this does not invalidate the overall CONSEQUENCE verdict.
- **Ribet LNM 601, Theorem 2.3: UNVERIFIED auxiliary locator.** DDT p. 86 cites §2 of Ribet's survey for absolute irreducibility; its bibliography identifies *The ℓ-adic representations attached to an eigenform with Nebentypus: a survey*, pp. 17–52. The original theorem-numbered pages were not obtained/read. An attempted author-index fetch returned HTTP 403; no restriction was bypassed. Clause (i) is nevertheless verified from the obtained DDT 3.1(c), not left dependent on that locator.
- **Shimura 1971, Theorem 7.14: UNVERIFIED auxiliary locator.** The original book theorem was not read. DDT 3.1(a), together with the construction preceding it, is the sufficient printed existence/Frobenius statement used here.

The sufficient route is consequently: **DDT 1.22 + its §2.1 definitions and §3.1 construction + DDT 3.1(a)–(d)**; scalar-extension descent of irreducibility to the ground coefficient field; extraction of trace/determinant from the good characteristic polynomial; and extraction of local exponents from the prime-to-$\ell$ conductor identity. There is no additional unproved mathematical hypothesis introduced by these steps.

## False, incomplete or unclear

**No false, missing-hypothesis, or strengthened conclusion was found relative to the DDT package.** The overall statement is a consequence, not a direct transcription, for the reasons above.

Two attribution/encoding cautions remain:

1. Calling the full package simply “Carayol Théorème (A)” would be incomplete evidence: the exact coefficient field and printed absolute irreducibility are supplied by DDT, while Carayol states local compatibility over an extension field. The current combined source line avoids that mistake.
2. The determinant's universal conditional over $b$ does not itself assert the character-value field-membership fact. That is a weaker literal encoding than an unconditional determinant formula if the membership fact is unavailable, not a stronger open hypothesis. DDT §3.1 explicitly provides that fact for the intended newforms.

The Casselman page-range refinement is a locator issue for an auxiliary step, not a reason to report the whole Lean proposition as NO-statement. The original Ribet and Shimura theorem numbers remain UNVERIFIED rather than being silently certified by an indirect reference.

## Not read

- The separate 1995 journal scan and 1997 book reprint of DDT were not compared with the September 9, 2007 author copy.
- DDT's cited original proofs of Eichler–Shimura/Shimura, Ribet's irreducibility argument, and its conductor theorem were not independently audited. The report reads the survey's printed theorem and the relevant definitions/construction.
- The original pages of Ribet LNM 601 Theorem 2.3 and Shimura 1971 Theorem 7.14 were not read. They are not required as additional hypotheses for the sufficient DDT route.
- Carayol's geometric construction, full proof of local–global compatibility, base-change argument, and appendix were not audited; the introductory theorem and normalization were read.
- Casselman's global proof and later applications were not audited, nor were the cited Jacquet–Langlands and Kutzko sources read. The local theorem, calculation pages and conductor remark listed above were read.
- No new Lean execution, build, kernel check, or exhaustive dependency/proof audit was performed. The scope is this one proposition and its mathematical meanings.

## AI use

An AI language model performed public-source discovery, read the extracted text and page images, transcribed the displayed formulas, interpreted the French conventions, unfolded the Lean definitions, and authored the comparison and verdict. `curl` downloaded the freely accessible copies; `pdftotext` extracted searchable text. Carayol's formulas and the image-only Casselman statements were checked against the page images rather than inferred from OCR alone. No human reading is claimed.

## Evidence

**AI-READ.** This report records an AI reading of the cited pages. It is not HUMAN-READ evidence, does not clear a human-reading or statement-risk flag, and makes no change to the project's reading registers or classifications.
