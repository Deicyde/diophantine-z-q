# rc-model-generic6

**Retired frozen fields: none yet.** No field of SamePlaceData and no hypothesis of GoodRowWire.oddStagedOfSamePlace is discharged, and no named piece of one is supplied yet. The hRC GLUE row (docs/one-proof/OPEN.md, section hRC: docs/one-proof/OPEN.md#hrc) and PreLeaves.odd_staged (RC/Wiring/Leaves.lean:305) are unchanged.

**No error verdict.** No leaf was added or proposed.

**Main result: item 2 over ℂ, complete; scoped stop for the rest.** At every complex point y of the pinned rational open, for every pair (E, C) representing rationalPoints y and every seam g from E to the actual vendored Vélu composite E' = E.cyclicQuotientCurve C_Q Q with g.ker = C_Q = (N/Q) • C: rationalPoints (y ∘ atkinRatAlg) = [(E', g(E[Q] ⊔ C))] (ModelGeneric6.rationalPoints_atkinRat_complex_moduli). It is choice-free; independence of the choices is a corollary (atkinClass_independent), and no uniqueness of quotients is used. Also complete: item 2a in every characteristic prime to 2N (isAddCyclic_map_atkinSum_curve), and item 3a, separable seams with finrankAlong = n for the vendored composite in every characteristic prime to n (exists_quotientSeam). Open: item 2c (transfer to every algebraically closed field of characteristic 0) and items 3b, 3c (the special fibre).

**Piece of SamePlaceData.point_W supplied: none yet.** The special-fibre action of Wint (item 3) is open. Item 2 at complex points and item 3a are inputs of that piece. point_W also needs point and the X.W comparison (hCM lane), and uniqueness of separable quotients in characteristic ℓ (Silverman III.4.11–4.12, UNVERIFIED) unless the X.W comparison is stated for every separable seam.

**What compiles.** Six Lean modules under ZInQKernel/Contrib/OneProof/RC/ModelGeneric6/: Cyclicity, VariableChangeSeam, SeamLift, ComplexStep, CharFreeSeam and CharFreeSeamTwo. VariableChangeSeam is ON THE SPOT (c): the explicit function-field map of a Weierstrass variable change, whose restriction of places is Point.addEquivVariableChange, in any characteristic. Each module builds with lake build, with no sorry and no axiom declaration. Every #print axioms lists only propext, Classical.choice and Quot.sound. Item 1 (the reviewer's doc fixes to the generic4, generic5 and target reports) is one commit, doc only. The report is docs/research/rc-model-generic6.md.

**What remains** (exact statements in the report).
- 2c: naturality of rationalPoints on classes (needs PairClasses.map); the Vélu composite under field embeddings; seams under base change; injectivity of PairClasses.map; descent (only for fields larger than 𝔠).
- 3b: a Y0LevelPoints computation lemma at cover points, and the Hensel lift over W(k) (EGA IV 18.5.17, UNVERIFIED).
- 3c: reduction of the order-two Vélu step and of the composite (the odd step's reduction is in the tree).

Work tip (all modules and the report): f569bfb11a958bd76172d55ef7ae6b08dfbf9540. This file is committed on top of it.
