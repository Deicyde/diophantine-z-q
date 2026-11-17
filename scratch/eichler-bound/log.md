# eichler-bound results log

Task: prove `GR56.R5fpCountLe` (the only half of `gonzalezRotgerProp56X6` the chain reads) without Eichler's
formula, for the maximal order O of B = (2,-3 | Q).

## Plan (2026-11-16 13:xx)
Target theorem: `#(OptEmb k R / O^x) <= 2^{inertCount6 k} * #Pic(R)` for R of conductor prime to 6, by an
explicit injection `Quot (ConjRel R) -> Pic R x T`, `#T = 2^b`, where T = types at 2 and 3
(`Phi(omega) - Phi0(omega)` in the two-sided prime P_l of O). Ingredients: class number one of O (Euclidean
algorithm), the intertwiner lattice `J = {c in O : c Phi0(a) = Phi(a) c}`, and a "Key" lemma
(J O = O = O J when types agree) proved prime by prime:
* l not dividing 6: polynomial certificate (6 * minor in the ideal of coords of conj(c) d, c conj(d)) + descent;
* l | 6: P_l = pi O = O pi (pi = i, j), conjugation by pi = quaternion conjugation mod P_l.

## Findings
* VERIFIED (sympy, cert_L.py): each 2x2 minor a_i b_j - a_j b_i of the O-coordinates of c, d is a rational
  linear combination, with denominators dividing 6, of the 8 O-coordinates of conj(c)*d and c*conj(d).
* VERIFIED (python, checkP.py, |n_i| <= 3 exhaustive / random): P_2 = {n0, n2 even} = {2 | nrd},
  P_3 = {n0 = n2, n1 = n3 mod 3} = {3 | nrd}; conj(pi) z pi - nrd(pi) conj(z) in l*P_l; commutators in P_2, P_3.

## Compile log (modules under ZInQKernel/Contrib/OneProof/EichlerBound/, lake build)
* Order.lean (part A: norm/trace, l*O, P_2 = iO, P_3 = jO, frob, minor certificate, Euclid/principal): compiles, no sorry. VERIFIED.
* Quadratic.lean (part C: R = Z + Z omega for conductor prime to 6; ramified element; Lemma D at 2): compiles. VERIFIED.
* Embed.lean (embeddings, conjugation sk, centralizer, intertwiners J, Skolem-Noether-lite): compiles. VERIFIED.
* Unit.lean (Bad, conjugation trick Bad => Bad'): compiles. VERIFIED.
* Crit.lean (unit criterion J O = O and O J = O from no bad prime, via principal_of_lattice): compiles. VERIFIED.
* Key.lean (no bad prime l not dividing 6: minor certificate + descent): compiles. VERIFIED.
* Key6.lean (l | 6: ramified element contradiction, unramified type argument, type dichotomy): compiles. VERIFIED.
* Inv.lean (lattices a, b; Lemma D): compiles. VERIFIED.
* Count.lean (a*b = R, injectivity, unitsToPic kernel): compiles. VERIFIED.
* Bound.lean (inertness, types card = 2^b, conjRel_card_le): compiles. VERIFIED 14:27.
* `#print axioms EichlerBound.conjRel_card_le` = [propext, Classical.choice, Quot.sound] (with the development copy
  of OptEmb/ConjRel, verbatim from GRCountX6). VERIFIED.

## Statement proved
`EichlerBound.conjRel_card_le : finrank 2 -> R <= O_k -> Coprime (conductor R) 6 -> Nat.card (Pic R) != 0 ->
 Finite (Quot (ConjRel R)) /\ Nat.card (Quot (ConjRel R)) <= 2^inertCount6 k * Nat.card (Pic R)`.
Final file ZInQKernel/Contrib/OneProof/R5fpCountLe.lean: `eichlerOptEmbBound6` (= the above over GRCountX6's
definitions) and `r5fpCountLe_proof : UniformizationLeafAll -> GAGAMorphism -> MumfordTorsionAlgClosed ->
GR56.R5fpCountLe`.

## Fold counts (autofold --dry-run, count-only spec scratch/eichler-bound/autofold.json, no new leaf)
* tree kinds.tsv (prop56 rated LEAF): 34/11 on 45 -> 33/11 on 44 (strictest same). VERIFIED.
* simulated re-rating of the prop56 row to GLUE (/tmp/ebsim copy): 33/12 on 45 -> 33/11 on 44. VERIFIED.
* Final module R5fpCountLe.lean (imports GR56Lattice; Defs imports GRCountX6, dev copies removed): lake build OK
  (12938 jobs). VERIFIED. Axioms of eichlerOptEmbBound6 and r5fpCountLe_proof: standard. VERIFIED.
* #discharges: 56 open, 3322 checked, 10 discharge one (none from this task: R5fpCountLe is weaker; bypass). VERIFIED.
* BypassFold.lean (gen_bypass.py, E-variant only): compiles; sixContactMin_of_open35E and frozenTarget_E use
  standard axioms; no EichlerOptEmbCount6, no gonzalezRotgerProp56X6 field. VERIFIED.
