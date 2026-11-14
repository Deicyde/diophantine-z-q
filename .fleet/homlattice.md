# homlattice — summary

**Verdict.** `HomLatticeCorr` (hom-unify's proposed single leaf) is true and no stronger than the
literature, but it is **not a published theorem in this form**. It bundles four pieces:
- (a) `A(ℂ)_σ ≅ ℂ^g/Λ` (Mumford §1/§4);
- (b) GAGA (Serre 1956; SGA 1 XII 4.4);
- (c) "algebraic ⇒ holomorphic";
- (d) the lifting argument of Birkenhake–Lange Prop. 1.2.1.

It is also stated over leaf-push2's weak `IsUniformization`. All theorem numbers are UNVERIFIED
(no network). Pieces (c) and (d), and the comparison of a weak uniformization with a strong one,
are now Lean proofs.

**Main result (compiled, standard axioms only).** `scratch/homlattice/HomLattice.lean`:
- `homLatticeCorr_of_strong_gaga : StrongUniformizationExists → GAGAMorphism → HomLatticeCorr`
  (hence `HomLinearLift` for G10 over number fields, `T11aHom`, `T11a_RiemannEnd`);
- `t11a_riemannEnd_of_leaf_gaga`, `t11aHom_of_leaf_gaga`: over `ℂ`, the existing leaf
  `UniformizationLeafAll` plus `GAGAMorphism` suffice; the lifting half needs no new leaf;
- `leafAll_of_strong : StrongUniformizationExists → UniformizationLeafAll`.

The two hypotheses:
- `StrongUniformizationExists` is bp-analytic's AN3 predicate, copied field by field with `σ`
  added (equivalent to it at `σ = id`, proved).
- `GAGAMorphism` says a holomorphic homomorphism `A^an → B^an` is an algebraic morphism.
  Rigidity is proved (copied from mul-rigidity).

**What compiles.** `lake env lean scratch/homlattice/HomLattice.lean`: exit 0, about 10 s, 45
`#print axioms` reports, all `[propext, Classical.choice, Quot.sound]`, no sorry. The copied
rigidity block passes the verbatim check.

**Recommendation.** Replace `UniformizationLeafAll` by `StrongUniformizationExists`, and
`T11a_RiemannEnd`/`HomLatticeCorr` by `GAGAMorphism`. The leaf count is unchanged.

**What remains.**
- The theorem numbers are unchecked.
- The general-`σ` truth argument for clauses (ii)/(iii) has had one independent model review, which found no problem; no human has reviewed it.
- The flat assembly with `GluePieces3Hom` was not re-run with `homLinearLift_of_strong` (a
  one-line composition).
- `StrongUniformizationExists → UniformizationExists` (T35, `g = dim A`) needs dimension theory
  and is not done.

Report: docs/research/homlattice.md. Log: scratch/homlattice/log.md.
