# Assembly at the actual modular-Jacobian consumer

Author/integrator: `/root`, 2026-11-10. This is an author proposal for a fresh non-author review. It supplements the two immutable packets at private commit `a81afd7996a20e6b7bb5e48670418541c036d7aa`. The source/application target is Brox v17, SHA-256 `2ba5dd497276073d92db95f0119bede82d182997c66375e5be294157de6d9f7c`, lines 47–488, and H0.3/H4 in `research/quadratic-ten-contact-integration/height/PROOF.md`. No polynomial, parameter choice or constant is changed.

## A. The scoped theorem

For a positive integer N and a subgroup H of `(Z/NZ)^×` containing −1, put `X_H=X_1(N)/H`, `J_H=Jac(X_H)`, `s=[(Z/NZ)^×:H]`, and suppose its genus g is positive. For the map `t=j/1728` set

`d=N s product_(p|N)(1+1/p)`.

The statement assembled here is

`hF(J_H) <= d/2 (log12+log N+2log d) + g log(2/sqrt(pi))`,

where hF is the original stable Faltings height. This is the exact modular-Jacobian supplier already used by H0.3. It is a theorem about the actual quotient Jacobian, not a bound for an isogenous replacement or a full-level cover. Its proof is the following three linked project proofs, with their primary theorem applications recorded in their own contracts and source inventories.

## B. Same curve, order, lattice and maps

The modular-model construction in `different/PROOF.md` §4 identifies the generic primitive N-torsion points modulo H with the actual modular quotient, compatibly with Galois action. It provides the finite étale model away from 6N and the degree d. The ±1 ambiguity of a chosen elliptic-curve isomorphism is already killed in H. At a prime dividing N we use the finite flat torsion argument, not the model with N inverted. Every component and every place is included in the discriminant sum. The positive-genus hypothesis removes the genus-zero cases without imposing an unrecorded large-level condition.

Choose one finite number field K defining the cover, making the curve semistable, and splitting its unramified fibre over t=2. Existence of such an extension follows from semistable reduction and adjoining finitely many point coordinates. Its degree is not bounded. Let B be the normalization of `O_K[t]` in `K(X_H)`, and put `C=B/(t−2)B`. The integral-evaluation proof uses this same B and this possibly nonmaximal order C. Let `E=H0(𝒳,ω_𝒳/O_K)` for the minimal regular semistable model 𝒳 of X_H. Then `evaluation/PROOF.md` supplies the literal integral map

`ev:E -> C^vee`, `ω -> (ω/dt(P_j))_(j=1,...,d)`.

Here `C^vee` is defined by the generic field trace, not by an arbitrary isomorphism of dualizing modules. The canonical finite-duality and specialization comparison fixes this normalization. The common regular model and codimension-one descent justify using the lattice of the regular semistable model even when the finite normalization model is singular. No claim that the latter is Gorenstein is used.

The metric proof fixes one coordinate set I of size g over K for which the evaluation minor is nonzero. It uses every fibre point to prove rank, then the same I at every embedding. Set `F=pr_I(C^vee)` with its standard Euclidean metric. The evaluation proof gives

`Ardeg(F) <= (1/2) log Norm disc(C)`.

The metric proof supplies the original stable identification `Ardeg(E)=[K:Q] hF(J_H)` and the determinant bound `(2/sqrt(pi))^g` at every embedding. Its arithmetic degree calculation therefore gives

`hF(J_H) <= log Norm disc(C)/(2[K:Q]) + g log(2/sqrt(pi))`.

This chain keeps the same order, projected lattice, trace map, curve, metric and determinant convention throughout. It does not replace an integral lattice by its generic vector space.

## C. Same discriminant and constant

The different proof computes the trace determinant of the same B and its specialization to C. Its local component formula is `v(disc)=sum_j f_j r_j` with full residue degrees, including inseparable degrees. At p>3 the torsion argument and intermediate-field comparison give the full vertical contribution at most `d v_p(N)`. The possibly imperfect-residue estimate at 2 and 3 contributes at most `d(log6+2log d)` after normalization. The horizontal t=0 intersection contributes at most `d log2`; t=1 and infinity do not meet the section. Summing over all places of K cancels `[K:Q]`, so

`log Norm disc(C)/[K:Q] <= d(log12+log N+2log d)`.

Inserting this in B proves A with exactly its stated constant. In particular, the auxiliary K is never inserted into the surface-isogeny field degree `d'=[L':Q]` used later. K only occurs in a normalized stable-height calculation.

## D. Actual H0.3 and the two downstream families

The existing H1 constructs a final primitive weight-two form f with character epsilon, and H2 constructs an L'-defined surface-power subvariety of `J=Jac(X_1(N)/ker epsilon)`. Those constructions are retained inputs to the present application; this supplement does not re-prove normalized modularity. Weight two gives `epsilon(−1)=1`, so `H=ker epsilon` meets the subgroup hypothesis. Its index is `ord(epsilon)=s`, and the actual surface factor gives `g>=2`. Thus A applies to that exact J for every rational parameter in the full H0 domain. No restriction to the eventual distinguished beta is introduced.

The genus bound `g<=d` used in H4 follows from Riemann–Hurwitz in the same Belyi cover: `2g−2<=d−3`, hence `g<d` for positive g. The remaining H4 relaxations, including `log(2/sqrt(pi))<log2`, are unchanged. They retain the same rational numerical certificate, conductor, character order and multiplicity assumptions. Consequently this supplement changes no value of `C2`, alpha, anchor exponent, 256-variable table or 214-variable parameter family. It supplies only the modular-Jacobian interface within their existing chains.

The 214 construction remains an existence family with an ineffective threshold N0; the separate condition N>=53 only bounds coefficients. Neither this height supplier nor a passing finite checker makes N0 effective. No effective construction is asserted in this public package.

## E. History and remaining closure

The earlier source assessment and review already explained integral evaluation, trace duality, different bounds and the metric constant. This round compares those actual arguments to final primary sources and expands the joins. It does not claim a newly discovered arithmetic error or priority for the underlying proof. The old packets and verdicts stay immutable; the new reviewer decision applies only to the exact new supplement and its stated interfaces.

Acceptance of A does not accept H0 geometry/CM bounds, normalized modularity and companion trace assembly, the entire analytic/restricted-converse chain, or every remaining final-publication/source qualification in the prior foundation map. In particular the final 2022 Rémond body comparison remains a separate item. The current status overlay must carry those obligations forward rather than infer whole-proof closure from the success of this supplier.
