# Conrad, Appendix B, pp. 32–33: verbatim quotes for the leaf `conradAppBWeil`

Source: Brian Conrad, *Lifting global representations with local properties*, author preprint dated December 11, 2011 ("Date: December 11, 2011", p. 1). PDF from the author's page `math.stanford.edu/~conrad/papers/locchar.pdf`, as cited by the manuscript (bibitem `conrad-local-characters`, diophantine_zq.tex L11046–11049). File sha256 `782fe71a3c7f26ccd67943d468f73540d384e2de5d474bf8369475b8b631d9bd`, 528,777 bytes.

Method: transcribed from page images of printed pp. 32–34 (PDF pages 32–34), checked against `pdftotext`. Mathematical symbols are written in TeX; underlines on the tori (written `\underline{L}^\times`) are as printed. Read by an AI agent (AI-READ), not by a person.

## p. 32: setting and Definition B.1

> **Appendix B. Local algebraicity and crystalline representations**
>
> Let $L$ be a finite extension of $\mathbf{Q}_p$ and $\psi : G_L^{\mathrm{ab}} \to K^\times$ a continuous character, with $K$ a finite extension of $\mathbf{Q}_p$. Upon composing with the local Artin map $r_L : L^\times \to G_L^{\mathrm{ab}}$ (using either normalization) we get a continuous composite map $L^\times \to K^\times$ whose source and target are respectively identified (as topological groups) with the groups of $\mathbf{Q}_p$-points of the $\mathbf{Q}_p$-tori $\underline{L}^\times = \mathrm{R}_{L/\mathbf{Q}_p}(\mathbf{G}_m)$ and $\underline{K}^\times = \mathrm{R}_{K/\mathbf{Q}_p}(\mathbf{G}_m)$ defined by Weil restriction of scalars.
>
> **Definition B.1.** The representation $\psi$ is *locally algebraic* if there exists a (necessarily unique) $\mathbf{Q}_p$-homomorphism $\underline{L}^\times \to \underline{K}^\times$ whose restriction to $\mathbf{Q}_p$-points agrees with $\psi \circ r_L$ near 1.

## p. 32: the paragraph after Definition B.1 (Hodge–Tate iff locally algebraic)

> Since $\psi$ is semisimple when viewed as a $\mathbf{Q}_p$-linear abelian representative of $G_L$ (as we see by applying $(\cdot)\otimes_{\mathbf{Q}_p}\overline{\mathbf{Q}}_p$), it follows from a result of Tate (see [S6, III, A6, Cor. 2]) that $\psi$ is locally algebraic if and only if its underlying $\mathbf{Q}_p$-linear representation is Hodge–Tate. In this appendix we address two useful refinements for which there do not seem to be suitable references in the literature: computing the Hodge–Tate weights for a Hodge–Tate $\psi$ without requiring $L$ to be "sufficiently large" ([S6, III, A.5] settles the case when $L$ splits $K$ over $\mathbf{Q}_p$), and relating the crystalline condition to local algebraicity.
>
> Define the local Artin map $r_L : L^\times \to G_L^{\mathrm{ab}}$ using the arithmetic normalization. Assuming $\psi$ is Hodge–Tate, we seek a formula for its Hodge–Tate weights in terms of $K$ and $L$. Choose an auxiliary finite extension $K'/K$ that splits $L$ over $\mathbf{Q}_p$ (i.e., every factor field of the $K'$-algebra $K'\otimes_{\mathbf{Q}_p} L$ is equal to $K'$). By local algebaicity of $\psi$, near 1 the composite homomorphism
> $$L^\times \xrightarrow{r_L} G_L^{\mathrm{ab}} \xrightarrow{\psi} K^\times \hookrightarrow K'^\times$$

## p. 33: the display, the lines $V_\sigma$, Lemma B.2, (B.1)

> agrees with
> $$x \mapsto \prod_{\tau\in\mathrm{Hom}_{\mathbf{Q}_p}(L,K')} \tau(x)^{-n_\tau}$$
> for integers $n_\tau$ indexed by the set of $\mathbf{Q}_p$-embeddings of fields $\tau : L \to K'$. For the $\mathbf{Q}_p$-linear representation $V = K$ of $G_L$ via $\psi$, the semi-linear representation $\mathbf{C}_L\otimes_{\mathbf{Q}_p} V$ of $G_L$ naturally decomposes into $G_L$-stable $\mathbf{C}_L$-lines $V_\sigma$ indexed by the $\mathbf{Q}_p$-embeddings $\sigma : K \to \mathbf{C}_L$, and $V_\sigma = \mathbf{C}_L(w_\sigma)$ for some $w_\sigma\in\mathbf{Z}$ (i.e., $\{w_\sigma\}$ is the set of Hodge–Tate weights of $\psi$). If $\psi' : G_L^{\mathrm{ab}} \to K^\times$ is a second Hodge–Tate homomorphism (with underlying $\mathbf{Q}_p$-linear representation $V'$), and its Hodge–Tate weights are $\{w'_\sigma\}$, then the product homomorphism $\psi\psi' : G_L^{\mathrm{ab}} \to K^\times$ is Hodge–Tate with weights $\{w_\sigma + w'_\sigma\}$ because $(V\otimes_K V')_\sigma = V_\sigma\otimes_{\mathbf{C}_L} V'_\sigma$ as $\mathbf{C}_L$-semilinear representations of $G_L$.
>
> We shall compute the integers $w_\sigma$ in terms of the factor fields of $K\otimes_{\mathbf{Q}_p} L$ viewed as both a $K$-algebra and an $L$-algebra. The first step is to encode in terms of the $n_\tau$'s the property that $\prod_\tau \tau(x)^{-n_\tau}$ is valued in the subfield $K\subset K'$ for $x\in L^\times$. (It is equivalent to require the same only for $x\in L^\times$ near 1). This is given by the following lemma.
>
> **Lemma B.2.** *For each $\mathbf{Q}_p$-embedding $\tau : L\to K'$, let $n_\tau$ be an integer and let $1\otimes\tau$ denote the unique $K$-algebra map $K\otimes_{\mathbf{Q}_p} L\to K'$ extending $\tau$ (i.e., $a\otimes b\mapsto a\tau(b)$). Let $\prod F_i$ denote the decomposition of $K\otimes_{\mathbf{Q}_p} L$ into a finite product of fields, and let $q_i : K\otimes_{\mathbf{Q}_p} L\to F_i$ denote the canonical quotient map.*
>
> *The product homomorphism $L^\times\to K'^\times$ defined by $x\mapsto\prod_\tau\tau(x)^{-n_\tau}$ is valued in $K^\times$ if and only if $n_\tau$ only depends on the index $i$ for which $1\otimes\tau$ factors through $q_i$.*
>
> *Proof.* We may assume that $K'$ is finite Galois over $\mathbf{Q}_p$, and then invariance under $\mathrm{Gal}(K'/K)$ encodes the property of being valued in $K$. It is straightforward to check that such invariance is equivalent to the property that $n_\tau$ only depends on the factor field of $K\otimes_{\mathbf{Q}_p} L$ through which $1\otimes\tau$ factors. ∎
>
> By Lemma B.2, for each factor field $F_i$ of $K\otimes_{\mathbf{Q}_p} L$ we may define $n_i$ to be the common value of the integers $n_\tau$ for those $\tau$ such that $1\otimes\tau$ factors through $q_i$. In more intrinsic terms (i.e., without mentioning $K'/K$), $\psi\circ r_L : L^\times\to K^\times$ agrees near 1 with the homomorphism
> $$\text{(B.1)}\qquad x\mapsto\prod_i \mathrm{N}_{F_i/K}(q_i(1\otimes x))^{-n_i}.$$
> Here is a formula for the $w_\sigma$'s in terms of the $n_i$'s:

## p. 33: Proposition B.3

> **Proposition B.3.** *With notation as above, for each $\mathbf{Q}_p$-embedding $\sigma : K\to\mathbf{C}_L$ the Hodge–Tate weight $w_\sigma$ is equal to $n_i$ for the unique $i$ such that the $L$-algebra map $\sigma\otimes 1 : K\otimes_{\mathbf{Q}_p} L\to\mathbf{C}_L$ extending $\sigma$ factors through $q_i$.*

The proof of Proposition B.3 is on pp. 33–34; it is not quoted here.

## Readings that bear on the leaf

1. **B.3 assumes ψ Hodge–Tate.** "With notation as above" refers back to the setting on p. 32: "Assuming ψ is Hodge–Tate, we seek a formula for its Hodge–Tate weights", with the integers $n_\tau$, and hence $n_i$ in (B.1), obtained "by local algebaicity of ψ". The leaf therefore carries a Hodge–Tate hypothesis.
2. **Definition B.1 is a homomorphism of $\mathbf{Q}_p$-tori** $\mathrm{R}_{L/\mathbf{Q}_p}\mathbf{G}_m\to\mathrm{R}_{K/\mathbf{Q}_p}\mathbf{G}_m$ agreeing with $\psi\circ r_L$ on $\mathbf{Q}_p$-points near 1. The integer exponents first appear in the p. 33 display, derived by Conrad from the torus homomorphism after base change to $K'$, and in (B.1) for the $n_i$.
3. **Hodge–Tate iff locally algebraic** is printed (p. 32, attributed to Tate, [S6] = Serre, *Abelian ℓ-adic representations*, III, A6, Cor. 2).
4. **For $L = \mathbf{Q}_p$:** $K\otimes_{\mathbf{Q}_p}\mathbf{Q}_p = K$ has one factor field $F_1 = K$ with $q_1 = \mathrm{id}$, and $\mathrm{N}_{K/K} = \mathrm{id}$. So (B.1) reads $x\mapsto x^{-n}$, and B.3 gives $w_\sigma = n$ for every $\sigma : K\to\mathbf{C}_p$.
5. **Caveat on the line form.** For $L = \mathbf{Q}_p$ and $K\ne\mathbf{Q}_p$, the eigenlines $V_\sigma$ of the $K$-action in $\mathbf{C}_p\otimes_{\mathbf{Q}_p}K$ are permuted by $G_{\mathbf{Q}_p}$: $g$ sends $V_\sigma$ to $V_{g\sigma}$. So "$G_L$-stable lines $V_\sigma$" cannot be read literally, and the faithful reading of "$\{w_\sigma\}$ is the set of Hodge–Tate weights" is a $G_L$-semilinear decomposition of $\mathbf{C}_L\otimes V$ into lines $\mathbf{C}_L(w)$, one per $\sigma$. An independent review of the earlier B.3 leaf reached the same reading.
