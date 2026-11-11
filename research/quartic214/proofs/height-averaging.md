# Published product route for the multiplicity saving

Author: `/root`, 2026-11-11. This is a new application proof for independent review, not an acceptance record. It changes the supplier and auxiliary surfaces in H3 of the frozen private quadratic-height proof. It preserves the inequality H3.1, H4's constants and all polynomial rows.

## Sources and historical disposition

The original H3 applies the stable subvariety/quotient inequality in Rémond, *Propriétés de la hauteur de Faltings*, Annali SNS Pisa 23 (2022), 1589–1596. Its June 2021 author version was read, including Corollary 1.2 and the stable-height statement after Corollary 1.3. On 2026-11-11 the final publisher body again redirected to subscriptions. That final-body comparison remains unavailable; no claim about its absence or incorrectness follows.

There is an existing alternative argument in the current public Version 15, `v15:height:lem:surface`, especially lines 30617–30636. I read that argument and its recorded source-route disposition. It consumes the construction in the published proof of Gaudron–Rémond, *Nouveaux théorèmes d'isogénie*, Mémoires SMF 176 (2023), Lemma 16.2(1), printed pp. 97–98. I independently downloaded the final publisher PDF, SHA256 `b1e2e32bec626cf6d27fb7d6d8702b5c707e0c3dc002d979088e62d8cda514a4`, and read the text and image of printed p. 98. The source constructs, over its given number field, an isogenous abelian variety of no larger original stable Faltings height which is a product of simple abelian varieties over that field. Its factors are explicitly allowed to repeat.

This published proof uses Rémond 2022, Corollary 1.3, and Rémond 2017, Theorem 1.6. They remain indirect dependencies. The present route does not assert that the inaccessible final 2022 text was read, and does not re-prove the published product supplier. It uses that construction at its exact stated scope. Public Version 15's accepted single-surface application is historical support for the route, not approval of the new multiplicity application below.

## Fixed-field product and multiplicity

Retain the actual objects of H0–H2: the number field L', the absolutely simple abelian surface A=A_a, the Jacobian J=Jac(X_1(N)/ker epsilon) over L', its dimension g, and an L'-defined subvariety B_0 isogenous over L' to A^r, with r=e/2>=1. In particular g>=2r. The auxiliary field used to split the evaluation fibre is not substituted for L'. Geometry and the H2 realization are premises of this lemma and have their own source/application obligations.

Apply the construction in the proof of GR2023 Lemma 16.2(1) to J over L'. It gives J_0=product D_j, where every D_j is simple over L', J_0 is L'-isogenous to J, and hF(J_0)<=hF(J). This is an isomorphism to a product, not merely an isogeny between the displayed factors and J_0. No invariance of height under arbitrary isogeny is asserted.

Poincaré complete reducibility over L' and uniqueness of simple isogeny factors imply that the isogeny class of A occurs in this product with multiplicity at least r. To see the multiplicity explicitly, B_0~A^r is a subobject of J in the semisimple category up to L'-isogeny. Passing to the isomorphic object J_0 in that category preserves the multiplicity of every simple constituent. Since A is absolutely simple, it is simple over L'; each constituent in its class has dimension two. Choose r distinct occurrences, name them C_1,...,C_r, and denote the product of all remaining factors by E. Then

    J_0 = C_1 x ... x C_r x E,
    dim(E)=g-2r,
    C_i ~ A over L' for every i=1,...,r.

Every index is covered, even when r grows with the nebentypus order. These C_i are new product factors, not the old filtration quotients D_i/D_(i-1). The only subsequent consumer of those old quotients was their dimension, L'-isogeny class and height bound. Those are supplied for the new factors here; no assertion identifies the two collections literally.

## Height average and transfer

Use the original stable Faltings normalization throughout. Height is additive on products. The original-normalization lower bound is hF(E)>=-3 dim(E)/2, from the actual GR2014 §2.3 and Corollary 8.4 calculation recorded in `quartic214-protocol-d/PRIMARY_SOURCE_BRIDGES.md`. It holds without a polarization hypothesis; if dim(E)=0 its height is zero. Consequently

    sum_i hF(C_i) = hF(J_0)-hF(E)
                   <= hF(J)+3(g-2r)/2
                   <= H_J,
    H_J=max(1,hF(J)+3g/2).

At least one of these actual r surfaces therefore has hF(C_i)<=H_J/r. No assertion about a minimum on a varying field, or about average height over isogeny classes, is needed beyond the published product construction.

For this C_i apply GR2023 Theorem 1.9(1) over K=L', with extension K itself, source C_i and target A. Both are dimension-two varieties over the same field and are L'-isogenous. With d'=[L':Q], the degree bound in the final publisher statement gives an isogeny C_i -> A of degree at most

    [14^32 d' max(1,log d',hF(C_i))]^16.

The one-sided stable-height change is at most half the logarithm of the degree in this direction. Thus for any X>=max(1,H_J/r),

    hF(A) <= X+8[32 log14+log d'+log max(1,log d',X)].

This is exactly H3.1. The later calculation in H4 uses only this displayed inequality, the H2 bound s/r<=4 and its separately supplied modular-Jacobian estimate. Neither H4 nor its rational certificate uses the old quotient presentation. The full-family domain, both CM/non-CM branches and the two transformed arguments used in 214 are unchanged. This proof does not itself accept those receiving applications or their other premises.

## Nine application obligations

1. **Source hypotheses.** GR2023's construction is over a number field and begins with an abelian variety over that field. Here they are the actual L' and J of H2. The later isogeny theorem requires L'-isogenous dimension-two varieties: these are C_i and A, not J and A.
2. **Constructed objects.** J_0 and all simple product factors are defined over L'. The realization of B_0~A^r inside J is retained as a separate H2 premise. The GR construction supplies the height comparison, not an informal change to an arbitrary isogenous product.
3. **Index-set coverage.** Select r separate occurrences in the A-isogeny class. The entire family i=1,...,r participates in the sum; the repeated factors permitted by the source cannot be replaced by the set of distinct isogeny classes.
4. **Maps.** Pass along the L'-isogeny J_0~J only in the isogeny category to count constituents. Use the actual product isomorphism for height additivity. Apply the final small isogeny in direction C_i -> A, with half-logarithmic cost retained.
5. **Consumed object.** H3.1 bounds the same original A_a. The new C_i replace auxiliary quotient surfaces; their identity with the old C_i is neither needed nor claimed. The received X and H_J/r are exactly those consumed in H4.
6. **Conventions.** All heights are original stable hF; all logarithms are natural; d' is the degree of L', not the evaluation splitting field. No Tate/cohomology change is made.
7. **Local conditions.** These published height/isogeny statements impose no new conductor, good-prime or integral-model constraint on the selected surfaces. Existing H0–H2 local hypotheses remain upstream; enlarging L' is not used.
8. **Exceptions.** r>=1 and g>=2r; E of dimension zero is included. Absolute simplicity is required in the non-CM H2 branch. The original separate CM estimate does not use this lemma. Negative individual heights are allowed, and the maximum with 1 is retained.
9. **Downstream dependencies.** Only the supplier for the H3 average and the auxiliary C_i change. H3.1 and all constants are identical, so downstream numerical arguments and rows need no modification, subject to review of this substitution. The indirect Rémond dependencies and final-body access limitation remain recorded.

Acceptance, if obtained, must bind this proof, these nine obligations, the actual H2 construction, H3/H4 consumer and published source version. The author makes no whole-214 Protocol D completion claim.
