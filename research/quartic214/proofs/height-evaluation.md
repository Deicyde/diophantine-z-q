# Integral evaluation and the trace-dual lattice

Author: internal model agent `/root/d214_integral_evaluation`, 2026-11-10. This is a proposed source/application bridge, not independent acceptance. Frozen private repository: `a81afd7996a20e6b7bb5e48670418541c036d7aa`. The exact target is Brox v17, `research/quadratic-ten-contact-integration/height/sources/brox-v17.tex`, lines 87–99, 117–209 and its consumer at 218–225. Whole-file and passage bindings are in `SOURCE_USES.json` and `CONTRACT.json`.

The conclusion proposed here is exactly the integral map

\[
H^0(\mathcal X,\omega_{\mathcal X/R})\longrightarrow C^\vee,
\quad\alpha\longmapsto ((\alpha/dt)(P_i))_{i=1}^d,
\]

and, for every subset I of g coordinate positions, the bound
\(\widehat{\deg}\operatorname{pr}_I C^\vee\le\frac12\log N\mathfrak D(C)\).
Here R=O_K and **C is the unsaturated specialization of the actual normalization algebra**, not its integral closure R^d. There is no change in constants or curve. The stable-height metric, analytic rank estimate, vertical different, torsion different and modular realization are outside this component's claimed conclusion.

## 1. Objects and finite flatness

Let F=K(t), L=K(X), A=R[t]. The smooth geometrically connected curve X/K and its finite map to P1 have degree d. Characteristic zero makes L/F separable. Let Y be the normalization of P1_R in L, and B its algebra over Spec A. The generic fibre of Y is the original X: a smooth curve is normal, and the finite map X→P1_K has the defining normalization property. The chosen t=2 fibre is unramified and split into the distinct K-points P_1,…,P_d. These are the hypotheses actually supplied by v17:79–98.

For completeness, finiteness here can be proved directly, without an unchecked general appeal to excellence. Choose an F-basis e_1,…,e_d of L integral over A; multiply arbitrary basis elements by suitable nonzero elements of A to arrange this. D=A[e_1,…,e_d] is finite over A and spans L. If b is integral over A, each Tr(b e_i) is in A: it is integral over A, belongs to F, and A is integrally closed. The trace pairing is nondegenerate. Its Gram matrix in the e_i basis is invertible over F. Therefore all such b lie in the finitely generated A-module obtained by applying that inverse matrix to A^d. The integral closure B is an A-submodule of that module, hence finite because A is Noetherian. The same argument on R[1/t] glues the finite normalization Y.

A is regular of dimension 2. At q∈Spec B, with p=q∩A, the normal local domain B_q has dimension at most 2 and is Cohen–Macaulay: Serre's criterion gives depth ≥min(2,dim B_q), hence full depth in these dimensions (Stacks 031S). Going down for the integral inclusion A⊂B with A normal (00H8), together with incomparability, gives ht(q)=ht(p). Incomparability itself follows by localizing at p and reducing modulo p: an integral algebra over a field has only maximal primes, so two comparable primes over p coincide. Thus the local fibre dimension is zero and

\[
\dim B_q=\dim A_p+\dim(B_q/pB_q)=\dim A_p.
\]

All three hypotheses of miracle flatness 00R4 are now checked, including its dimension equality. Hence B_q is A_p-flat at every q. Flatness is local, so B is finite flat, consequently finite projective, of rank d. The same holds on the second target chart. Y is an integral normal proper flat arithmetic surface, finite over P1_R. No smoothness of its special fibres and no Gorenstein property of Y is asserted.

Consequently C=B⊗_A R=B/(t−2)B is finite projective of rank d over R. Its generic fibre is the **specified** K^d via evaluation at P_i. Its map into K^d is injective because C is R-torsion-free. Each coordinate of an element of C is integral over R and belongs to K, hence lies in R. Thus C⊂O:=R^d with full rank. No claim that C is reduced modulo a finite prime, étale over R, or normal is needed.

## 2. A common regular model with the required direction

Write M=\mathcal X for the given minimal regular semistable model. Take the reduced closure Γ of the graph of the identity X→Y_K=X inside M×_R Y. Both projections are proper birational morphisms. Stacks 0BFP, parts (1)–(2), says that the maximal isomorphism locus of Γ→M contains all codimension-zero and codimension-one points, since the codimension-one local rings of M are DVRs. Its complement T is a finite set of closed points: it is closed in a Noetherian surface and has dimension zero. If T is empty take Z=M. Otherwise Stacks 0AHI applies to Γ→M and supplies a finite sequence of point blowups

\[
Z=M_n\to M_{n-1}\to\cdots\to M_0=M
\]

dominating Γ. Blowing up a closed regular point of a regular surface is regular: for regular parameters u,v its charts are T[v/u] and T[u/v], and at an exceptional point u and a lift of a uniformizer of the local ring of P1_{κ(x)} form regular parameters. This also covers non-rational closed centres. The resulting Z is integral, proper over R and R-flat (its coordinate rings have no R-torsion); the generic fibre is X, because every centre lies over a finite prime. Indeed Γ→M was already an isomorphism on the entire generic fibre. The two maps are α:Z→M and β:Z→Y, both proper birational, with identity on X.

In the published Javanpeykar paper, Lemma 2.3.1, proof on p.99, the point-blowup calculation is

\[
\omega_{M_i/R}=a_i^*\omega_{M_{i-1}/R}\otimes O_{M_i}(E_i).
\]

This is used from the **proof**, rather than confusing the lemma's point-height conclusion with the required sheaf statement. Since E_i is effective, pullback of a section of ω_{M_{i−1}/R} is a section of ω_{M_i/R}; iterate to get α^*E⊂H^0(Z,ω_{Z/R}). The formula is identified by the generic differential, so this operation does not multiply a differential by a rational function. Equivalently the local calculation is the Cartier hypersurface uV−vU=0 in P1_T; adjunction gives the exceptional twist +E.

Apply 0BFP again to β. Y is normal, hence its codimension-one local rings are DVRs; Z is reduced. There is an open U⊂Y containing every codimension-one point with β^{-1}(U)≅U. The complement has codimension at least two. The regular differential on Z therefore gives a section of ω_{Y/R}|_U, compatible with the same generic differential α. This direction descends sections from a regular model; it does **not** claim every canonical section on Y pulls back regularly to a resolution. Such a converse could require singularity hypotheses and is not used.

## 3. The canonical module and its extension

Use relative dualizing complexes normalized over R, with ω_{P1_R/R}[1] the relative dualizing complex of P1_R. Transitivity (0ATX) and finite duality (0BUL, whose proof identifies the finite pushforward with Hom) identify the relative canonical module on the affine target chart with

\[
M_B\,dt:=\operatorname{Hom}_A(B,A)\,dt.
\]

B is projective, so higher Ext_A(B,A) vanish; there is only the indicated sheaf in relative degree −1. The dt is the usual smooth differential generator on A1_R. The construction respects restrictions to affine opens, as explicitly required in 0BUL, so these local modules are one global ω_{Y/R}. One may also use the Cohen–Macaulay canonical-module statement in 0AWQ. The more general algebraic assertion 0C0I is **nonunique** and is insufficient by itself to choose the generic trace normalization; it is not used to choose that map.

Here is also a direct check of the reflexivity needed in v17. The trace isomorphism

\[
M_B\cong\{f\in L:\operatorname{Tr}_{L/F}(fB)\subset A\}
\tag{*}
\]

is Stacks 0BW2: A→B is finite, A-nonzerodivisors remain nonzerodivisors in the domain B, and L/F is finite separable. In particular M_B is B-torsion-free and has B-rank one. At a height-two q of B, choose regular parameters x,y in A_p (p=q∩A). M_B is A-projective. Thus x,y is an M_B-regular sequence before localizing and remains so after localizing at q. Both belong to q; hence depth_{B_q}(M_B)_q≥2. At a height-one prime torsion-freeness gives depth≥1. Thus M_B satisfies S2, and the normal-scheme criterion 0AVT Lemma 31.13.13 makes it reflexive. The same reasoning on the second chart gives global reflexivity. This argument does not require invertibility of M_B as a B-module.

The normal surface Y is S2; at points outside U its local depth is at least two. Lemma 31.13.12 in 0AVT then identifies ω_{Y/R} with j_*(ω_{Y/R}|_U). Therefore the section from §2 extends uniquely to all of Y. We have a well-defined R-linear map E→H^0(Y,ω_{Y/R}), taking each section to the same differential on X.

## 4. Trace normalization and specialization are the actual evaluation

There are two separate comparisons; both are necessary.

First, on an open of the generic t-line avoiding branch points, the finite map is étale. The usual smooth identification of the canonical module with Ω^1 is the one obtained from the conormal/adjunction construction of Stacks 0E9Z. Its construction uses the determinant of the conormal exact sequence, and therefore commutes with flat base change. Duality transitivity is 0ATX, the tensor comparison is 0B6U, and the flat base-change isomorphism is 0E9U. All schemes here are separated and finite type over the Noetherian base R (the category defined in 0F42); on the generic chart one can equally work over K.

To compute the identification, use an étale neighbourhood splitting the finite étale cover (04HN). On that neighbourhood B becomes A^d. Both the exterior/conormal construction and finite Hom duality are compatible with this flat base change. For a product of identity morphisms, the i-th differential f_i dt defines the coordinate functional b_i↦f_i b_i, and finite pushforward sums these functionals. Thus the map is

\[
(f_i\,dt)_i\longmapsto [\,(b_i)_i\mapsto\sum_i f_i b_i\,]\,dt.
\]

This formula is invariant under permuting the sheets and descends by faithful flatness. The sum is precisely the algebra trace. Consequently the trace map in (*) identifies the literal rational differential f dt with b↦Tr(fb). There is no degree factor d, different factor, or chosen scalar. This argument also explains why a bare nonunique identification such as 0C0I would not settle the issue. At t=2 all sheets are unramified in characteristic zero, so f=α/dt is regular at every P_i.

Second, because B is finite projective the natural map

\[
\operatorname{Hom}_A(B,A)\otimes_A R
\xrightarrow{\sim}\operatorname{Hom}_R(B\otimes_A R,R)
\tag{**}
\]

is an isomorphism. Explicitly (λ⊗1)(b mod(t−2))=λ(b) mod(t−2); it is independent of the lift since λ((t−2)b)=(t−2)λ(b). It is an isomorphism for free modules, and therefore for finite projective modules by expressing them as direct summands of finite free modules. This proves the required base change without assuming the map A→R is flat.

After tensoring (**) with K, C_K=K^d. The preceding trace computation and compatibility of the trace of a finite projective algebra with base change (the trace of a matrix is unchanged by reducing its entries) give

\[
\bar\lambda(c)=\sum_i (\alpha/dt)(P_i)c(P_i).
\]

Since \barλ(C)⊂R, the vector ((α/dt)(P_i)) belongs to exactly C^vee⊂K^d. Nondegeneracy of the dot-product trace on K^d identifies Hom_R(C,R) with C^vee; it does not identify it with O unless C=O. Thus the integral map asserted in v17:157–168 is obtained with its exact coordinate convention. No assumption about reduction of t=2 at bad primes was needed.

## 5. Trace-dual projection and arithmetic degree

This part is an elementary local calculation, reconstructed here rather than imported from a review verdict. For every nonzero prime p of R, choose an R_p-basis of C_p, with matrix U in the coordinate basis of O_p. U has nonzero determinant; trace on K^d is the dot product. The dual basis matrix is (U^T)^{-1}, and the trace Gram matrix is U^T U. Therefore

\[
\ell_{R_p}(C_p^\vee/O_p)=\ell_{R_p}(O_p/C_p)
=v_p(\det U)=\tfrac12v_p(\mathfrak D(C)).
\]

The inclusion O⊂C^vee follows directly from C⊂O. For every coordinate subset I (no special prime-dependent choice), the induced projection C^vee/O→pr_I(C^vee)/R^I is surjective: lift an element by its definition as an image and note pr_I(O)=R^I. Its finite-prime lengths cannot increase. F_I=pr_I(C^vee) is finite and torsion-free, hence projective over the Dedekind ring R, and contains R^I with finite quotient.

Equip F_I at every complex embedding with the standard Euclidean metric on K^I. Its determinant basis e_I has norm 1. The determinant line is a fractional ideal containing R e_I. Locally its length relative to R e_I equals ℓ(F_I/R^I). By the arithmetic-degree convention of v17:49–60 (or by multiplying e_I by a nonzero denominator and applying the product formula),

\[
\widehat{\deg}F_I=\sum_p\ell(F_{I,p}/R_p^I)\log\#\kappa(p)
\le\tfrac12\log N\mathfrak D(C).
\]

This also checks the sign for an overlattice. The proof treats nonprincipal global modules by local bases, all finite primes including residue characteristic 2, and every I with |I|=g≤d. The existence of an I for which evaluation has rank g belongs to the separate analytic/rank component; this component supplies the lattice conclusion for every such I once chosen.

## 6. Exact consumer and bounded status

The output is the same integral map and same trace discriminant used at v17:218–225. Composing with a chosen coordinate projection gives E→F_I; its generic determinant is nonzero only after the rank argument. Combining with the separate metric/determinant proof gives the unchanged Theorem 1.1 estimate. The modular-height consequence feeds height/PROOF.md H0.3 and H4 and the retained existence/global bound, including the downstream 256 route. No replacement order, normalization, extension field, curve or metric has entered this component.

History: the earlier foundation report had already read a complete project proof of this route and specifically requested source/application closure. The retained quadratic integration review explicitly checked v17 at component scope and kept inherited foundational qualifications. Accordingly this is prior justification found plus an expanded source bridge, proposed for incorporation; it is not evidence that no earlier reviewer had supplied these details. No historical verdict is rewritten. A non-author must review this frozen bridge and its sources before the application can be called independently accepted. This component does not close the full arithmetic theorem or all of Protocol D.
