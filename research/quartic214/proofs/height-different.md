# Different and modular-model bridge for the retained height bound

Author: internal model `/root/d214_different_bounds`, 2026-11-10. This is an author proposal for fresh non-author review. It neither writes nor supplies an independent acceptance. Frozen target: private repository commit `a81afd7996a20e6b7bb5e48670418541c036d7aa`, `research/quadratic-ten-contact-integration/height/sources/brox-v17.tex`, SHA-256 `2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c`.

The proposed conclusion is that Brox v17:274–328, 354–451 and 461–488 have the required different bounds, including at every imperfect-residue vertical generic DVR. The resulting bound is unchanged:

`log Norm disc(C)/[K:Q] <= d_H (log12 + logN + 2log d_H)`.

Together with the separate integral and analytic evaluation interfaces, which require their own non-author review, this is exactly the input to `height/PROOF.md` H0.3. No full-torsion splitting-field degree, extra factor two, or changed height constant is introduced. The source citation to Lemma49.12.6 is valid and now bound to its exact current tag0BWJ. The mathematical argument below supplies the expanded explicit source comparisons; incorporation and current independent acceptance remain pending.

## 1. Fixed objects and the trace-discriminant identity

Put R=O_K[t], where K is any finite extension used for semistability and splitting the t=2 fibre. Let B be the normalization of R in K(X); let d=[K(X):K(t)]. The integral-evaluation lane supplies finite projectivity of this same B of rank d. Put **C=B/(t−2)B**, retaining this order rather than replacing it with its normalization O. Its generic algebra is K^d after the chosen splitting extension. The determinant of B→Hom_R(B,R), b↦(b'↦Tr(bb')), is a nonzero section of an invertible line. Base change t↦2 gives exactly the trace determinant of C, since trace of multiplication on a finite projective module commutes with base change. Thus the section's arithmetic intersection with t=2 is log Norm disc(C). This is an equality of determinant ideals and does not assert that C is maximal.

At every height-one point q of Spec R, V=R_q is a DVR and T=B⊗_R V is its finite normal integral closure in the generic separable algebra. T can be semilocal; do not silently identify a single localization T_m with a finite V-algebra. Complete V. Then T⊗_V Vhat is the product of the complete DVRs U_j over every m_j above q, with generic fields F_j. Let e_j be the ramification index, f_j the full residue degree (including its inseparable degree), and r_j the Dedekind different exponent. Each U_j is finite free over Vhat. Filtering U_j/π_V U_j by powers of its uniformizer gives

`rank_Vhat U_j = dim_k(U_j/π_V U_j) = e_j f_j`, hence `Σ_j e_j f_j=d`.

This dimension calculation uses finiteness and flatness, not residue separability or a defectless-extension assertion for arbitrary valued fields. The completion decomposition and its whole degree d include every place; no preferred component is selected.

Under the generic trace, T^vee={x:Tr(xT)⊂V}=Hom_V(T,V). The valuation of the trace determinant is length_V(T^vee/T): choose a V-basis, whose trace Gram matrix presents this cokernel. On each completed component U_j^vee=π_j^(−r_j)U_j. The length there is f_j r_j. Consequently

`v_q(disc(B/R)) = Σ_j f_j r_j`.

This proves the local trace/discriminant formula used here directly. It removes dependence on an unchecked reading of Serre's book for this formula. Integrality r_j≥0 follows because traces of integral elements lie in the integrally closed DVR V, so U_j⊂U_j^vee. Completion preserves the trace pairing, its determinant valuation and the fractional duals by finite freeness.

## 2. Lenstra's estimate really covers the vertical DVR

The actual published source is Javanpeykar, ANT8(2014), §4.1, printed pp112–113, Propositions4.1.1 and4.1.3 and Remark4.1.2. The retained PDF is the final publisher article, DOI10.2140/ant.2014.8.89; see `SOURCE_USES.json`. The setup is a characteristic-zero DVR and its finite separable field extension. No perfect-residue assumption occurs. The remark explicitly distinguishes the separable-residue result in Serre and the imperfect-residue application. Proposition4.1.3 obtains a bound for each maximal ideal by completing it; it does not require the original integral closure to be a local ring.

Here is a direct reconstruction useful for checking conventions. For a finite extension of complete DVRs V⊂U with fraction-field degree n, choose uniformizer π of V. The element y=1/(nπ) has field trace 1/π and is therefore outside U^vee. As U^vee is a fractional ideal of the DVR U, it is strictly smaller than yU. Taking inverse fractional ideals gives D_U/V strictly larger than nπU. With v_U(π)=e this yields

`r < e(v_V(n)+1)`, equivalently `r <= e−1+e v_V(n)`.

This uses only characteristic zero, finite freeness, nondegeneracy of generic trace and total ordering of fractional ideals in a DVR. In particular it applies when the residue extension is inseparable. For a component of an algebra of total degree d, its completed degree n is at most d. In residue characteristic p,

`v_V(n) = v_V(p) v_p(n) <= v_V(p) floor(log d/log p)`.

Now take the actual vertical point q=(pfrak) of Spec O_K[t]. Then V=O_K[t]_(pfrak), residue field k(pfrak)(t), which generally is **imperfect**, fraction field K(t), and v_V(p)=e_pfrak. V is excellent (a localization of a finite-type algebra over O_K), so the normalizations are finite. For **every** component j the displayed estimate gives

`r_j <= e_j−1 + e_j e_pfrak floor(log d/log p)`.

Multiplying by all f_j and using Σe_jf_j=d bounds the whole discriminant coefficient by

`d(1+e_pfrak floor(log d/log p))`.

There is no restriction p≤d needed: if p>d the floor is zero and the same estimate holds. At a horizontal branch point the residue characteristic is zero. In completed curve coordinates, after the unramified coefficient-field extension one has t−a=u^e v(u), v(0)≠0. The derivative has order e−1 because e is a unit. The local complete-intersection/Jacobian formula for the different therefore gives r=e−1. Thus its discriminant coefficient is at most d. This applies to the horizontal branch divisor at t=0; t=1 and infinity contribute no intersection with the section t=2.

If normalization is finite étale over O_K0[S^−1,t,t^−1,(t−1)^−1], then after any finite K/K0 it stays finite étale there. The base is normal and a finite étale algebra over a normal ring is normal; its generic algebra is the base-changed cover. It is therefore the normalization of that algebra on the open. This identifies the actual B there, and rules out additional vertical discriminant components outside S after the auxiliary extension. It does not assert that normalization commutes with arbitrary base change everywhere.

The horizontal intersection with t=0 has normalized value log2. At pfrak above p the vertical intersection is f_pfrak logp. Summing the last bound, using Σ_(pfrak|p)e_pfrak f_pfrak=[K:Q] and Σf_pfrak≤[K:Q], gives

`log Norm disc(C)/[K:Q] <= d(log2 + log R_S + |S|log d)`.

The determinant Cartier divisor has no additional codimension-two divisor terms. Its proper pullback to t=2 incorporates the intersections even when several divisors meet there. These statements concern the same nonmaximal fibre order C of §1.

## 3. Torsion different as an identity of fractional ideals

Let V be the excellent characteristic-zero DVR occurring above, E/V an elliptic scheme, n≥1, and E[n]=Spec A. Its generic algebra L is finite étale; it need not be a field. The fact that [n] is finite locally free of rank n² can be checked using the field theorem Stacks0BFG, Lemma39.9.8, on every fibre: properness and finite fibres give finiteness. Stacks49.12.6/0BWJ applies with S=Spec V, X=Y=E smooth of relative dimension1, and f=[n] locally quasi-finite. It gives flatness, and its proof gives the LCI property. Thus the rank is n² by its fibre ranks. The same application works over the regular base U used in §4. Where n is invertible, the differential below is invertible, so [n] is étale.

The graph of [n] is the base change of the diagonal of the smooth relative curve E/V, hence a regular immersion into E×_V E. Projection is smooth. This gives an explicit local-complete-intersection factorization of [n]. Invariant differentials trivialize Ω_E/V as a line pulled back from V. The group law differentiates as addition at the identity; induction gives [n]^*ω=nω for positive n. Therefore the relative differentials of [n] have presentation O_E --n--> O_E and Fitt_0 Ω_[n]=(n). This is n, **not the degree n²**.

Base change by the zero section E[n]→Spec V preserves finite flatness, the local-complete-intersection property, the displayed presentation and its Fitting ideal. For this finite flat LCI V→A, Stacks0BWE (Lemma49.10.1) checks the exact syntomic hypotheses, Stacks0BWF (49.10.4) gives invertibility of ω_A/V, and Stacks0BWG (49.12.3, on the archived section0BWB) identifies the scheme different with Fitt_0 Ω_A/V=(n). Stacks Definition49.9.1/0BW4 defines that scheme different as Ann(ω_A/V / Aτ).

The generic trace identification is fixed, rather than an unspecified module isomorphism: Stacks0BW2 (49.8.2) maps x∈A^vee to b↦Tr_L/Frac(V)(xb). Stacks0BW3 (49.8.3) maps **1 to τ**. Under this map, the annihilator in the preceding paragraph is

`{a∈A: a A^vee⊂A}`.

Since A^vee is an invertible fractional A-ideal (from0BWF) and contains1, this is exactly its inverse fractional ideal. Thus `(A^vee)^−1=nA`, and inverting again gives the literal equality inside L

`A^vee=n^−1 A`.

This argument checks the scalar fixed by trace; an abstract isomorphism ω≅A by itself would not do so. It also explains how the Kähler different equals the Dedekind different here. In Stacks49.12.4/0BWH the local generator is mapped so that the Jacobian determinant maps to τ, consistently with the same equality. Brox’s citation49.12.6 is the valid current tag0BWJ. It applies directly to [n] as checked above and gives the same differential-determinant formula. The archived section0BWB includes Lemmas49.12.1–4, Example49.12.5 and Lemma49.12.6; a shortened web-text extraction had omitted the latter part. This author initially misclassified the citation as absent; fresh review caught that error before freeze. `FINDINGS.md` preserves the correction.

Normalize A in L, obtaining finite Atilde (excellence of V). Both A and Atilde are finite torsion-free V-modules with generic algebra L. Trace duality reverses the actual inclusion A⊂Atilde:

`Atilde^vee ⊂ A^vee = n^−1 A ⊂ n^−1 Atilde`.

Hence n Atilde^vee⊂Atilde. Componentwise, the Dedekind different contains nAtilde; equivalently **r_j≤v_j(n)**. No perfect-residue or monogenic-normalization hypothesis is needed. This is also valid for n=1, when every exponent is zero.

For clarity, the intermediate-field direction can be proved rather than inferred from a slogan. Complete at each chosen place in a tower V⊂W⊂U of normal finite extensions. Write W^vee_V=αW, possible since W is a DVR. Trace transitivity, tested also on every multiplication by b∈W, says

`U^vee_V = {x: Tr_U/W(xU)⊂W^vee_V} = α U^vee_W`.

Taking inverse fractional ideals yields D_U/V=D_U/W D_W/V U, with exponent r_U/V=r_U/W+e_U/W r_W/V. All differents have nonnegative exponents. Thus r_U/V≤v_U(n)=e_U/W v_W(n) implies r_W/V≤v_W(n). Passing to completions is legitimate by §1; this proves the assertion at every place of every intermediate field. The estimate concerns a single-point field and its subfields; it requires no bound on a torsion splitting field.

## 4. The actual primitive torsion quotient

For N≥1 and H⊂(Z/NZ)^× containing−1, let t_H=[(Z/NZ)^×:H]. Set

`U=Spec Z[1/(6N),t,t^−1,(t−1)^−1]`,

`E_t: y²=x³−3t/(t−1)x−2t/(t−1)`.

Direct substitution into Δ=−16(4a³+27b²), c4=−48a and j=c4³/Δ gives Δ=1728t²/(t−1)³ and j=1728t. All denominators and Δ are units on U. It is an elliptic scheme there. As N is invertible, E_t[N] is finite étale. Its primitive locus is open and closed: remove E_t[m] for the finitely many proper divisors m|N; these are unions of components étale locally on U. Thus the exact-order-N locus is finite étale as well, including N=1 with the usual order-one point.

The constant H action is scalar multiplication. On primitive points aP=P implies (a−1)P=0, hence a=1 modN. Étale locally the algebra is a product of copies of the base ring and H permutes these copies; the quotient is the product indexed by the H-orbits. This constructs a finite étale quotient even at residue characteristics dividing |H|. No averaging by |H| and no assumption |H| invertible is used. Freeness makes every orbit have |H| points.

Identify its generic fibre over Q(t) by the moduli definition of X_1(N). Over an algebraic closure, j≠0,1728, an elliptic curve has automorphism group {±1}. Given another curve with that j and a primitive point, choose an isomorphism to E_t; two choices differ by±1 and hence give the same H-orbit. This bijection is Galois compatible: changing the chosen isomorphism after a Galois action again differs only by±1. Thus it is an isomorphism of the finite étale Q(t)-algebras, not just a count of their geometric points. Quadratic twisting is exactly this ±1 ambiguity, already killed in H. The generic cover is the actual X_H=X_1(N)/H with t=j/1728. A normal finite étale cover over normal U is its normalization there.

Geometric primitive vectors are a single SL2(Z/NZ) orbit: a primitive pair (a,b) can be completed to a determinant-one matrix by Bézout modN. This is compatible with the standard analytic model of the connected modular curve; the construction introduces no full-level cyclotomic component. Counting primitive vectors gives N²∏_(p|N)(1−p^−2); dividing by |H|=φ(N)/t_H yields

`d_H=N t_H ∏_(p|N)(1+p^−1)`.

For N=1 the products and φ(1) are one, and d_H=1; the positive-genus hypothesis later simply excludes irrelevant small-genus cases. Published von Känel2021 §4, p8, (4.1) independently records the degree/index convention: the factor two occurs exactly when−I is absent, and the only possible branch values are the elliptic points and cusp. Here−I is present because−1∈H, so no additional two divides the formula. The finite étale model already proves absence of branch away from0,1,∞ in characteristic zero.

A geometric H-orbit has Galois stabilizer containing the stabilizer of any chosen primitive point P in it. Consequently its field of definition is an intermediate field of Q(t)(P)/Q(t). This remains true after replacing Q by the auxiliary K and completing at a vertical generic point: each component field and each chosen place is covered by §3. The quotient need not itself be a subalgebra factor of the integral nonnormal A; the generic field inclusion and its normalizations are the objects to which the intermediate-field conclusion applies.

## 5. Same constant at every prime

For every prime pfrak|p>3 of K, take V=O_K[t]_(pfrak). Both t and t−1 are units there, and1728 is a unit, so E_t/V is an elliptic scheme even if p|N. Do **not** use the finite étale model U at such p, since U inverted N; instead use the finite flat torsion theorem of §3. The quotient component field identified in §4 is an intermediate field of a single N-torsion-point field. Its different exponent is at most v_j(N)=e_j v_V(N). By §1 the full vertical discriminant coefficient is therefore

`Σ_j f_j r_j <= (Σ_j f_j e_j) v_V(N) = d_H v_pfrak(N)`.

After intersection with the section, summation over pfrak and division by [K:Q], this contributes at most d_H Σ_(p>3)v_p(N)logp≤d_H logN. Every component is included; the algebra's rank is d_H, not N² and not the degree of a full torsion field.

At p=2 and3 use §2 rather than the elliptic model, which is not asserted smooth there. Their combined normalized bound is at most d_H(log6+2log d_H). This includes primes not dividing N and levels with d_H<p. The horizontal t=0 contribution is at most d_H log2. Altogether

`log Norm disc(C)/[K:Q] <= d_H(log12+logN+2log d_H)`.

This is Broxv17:461–488 with every local supplier matched to the actual objects. The independent evaluation conclusion, if accepted for this same C, gives

`hF(J_H) <= d_H/2 (log12+logN+2log d_H) + g_H log(2/sqrt(pi))`.

The stable-height metric and the evaluation lattice are separate interfaces assigned to the other two author lanes; this document does not self-approve their conclusions. The prime summations show why the auxiliary K cancels, so no [K:Q] enters H0.3 or the later surface-isogeny field degree.

## 6. History, incorporation and limits

Actual earlier proof text read: frozen Broxv17 §§3–4 at274–488; height/PROOF.md H0.3 and H4; `research/v14-brox-order8/PROOF.md`45–56; its actual `review/SOURCE_ASSESSMENT.md` sections “The lattice and discriminant argument” and “The modular cover and surface”; its `review/REPORT.md`19–33; `research/v14-small-prime-conductor/review/REPORT.md` section “Fresh height estimate”; and retained Protocol-D foundationREPORT/H04. The earlier source assessment already states the imperfect-residue Lenstra application, exact torsion derivative n, reversed trace dual and intermediate-field conclusion. Its final review expressly retains published-source/whole-assembly limits. Therefore **prior justification found and read** is the historical disposition for these arguments. This packet is a source-pinned expansion and precise current-tag binding, not a claim to have first repaired a newly discovered arithmetic error.

Current incorporation: Broxv17 contains the substantive arguments but not this expanded bridge and current-tag expansion; the private height H0.3 retains their inherited status. This packet proposes the bridge for additive incorporation. Current acceptance: pending a reviewer other than this author after the packet is frozen, including the precise joins to the other two evaluation lanes. No global modularity, height-transfer, 214 existence or256 theorem is accepted by this bounded work. The source inventory records what was inspected; it does not claim exhaustive search of every historical archive, nor a new inspection of the complete Serre book. The relevant trace, different, tower and tame-horizontal assertions are instead derived explicitly above.
