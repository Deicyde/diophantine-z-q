# neron-sh-proof (fleet summary)

**Result.** The research field `neronBaseChangeStrictHenselization` (`GapSHPair.NeronBaseChangeStrictHenselization`,
BLR 1.2/2) is proved outright, statement unchanged, with no new leaf. The proof never uses "strictly henselian",
so it also proves the chain's stronger `ReductGlue.NeronBaseChangeUnramifiedDVR` (the BLR 7.2/1 form, dict-models'
proposed leaf `BLR_7_2_1`): any characteristic, any residue field, any separable algebraic `K'/K`.

* Part A (Mathlib only): an unramified extension `O ⊆ O'` (separable `K'/K`, separable residue extension) is
  ind-étale. Every finite subset of `O'` lies in an étale `O`-subalgebra: a localization of the integral closure
  of `O` in `K(s)` at its étale locus.
* Part B: Néron models commute with ind-smooth base change. Spread out over the smooth subalgebras (EGA IV
  8.8.2/17.7.8, proved in the tree), descend the generic morphism (Mathlib's Stacks 01ZC), apply the Néron
  property over `O`; uniqueness and gluing are gt-blr's lemmas.

**What compiles (VERIFIED).**
* `ZInQKernel/Contrib/OneProof/NeronBaseChangeStrictHenselization.lean` (56 KB) builds.
* `#discharges`: `OpenResearchLeaves26.neronBaseChangeStrictHenselization` by
  `NeronSH.neronBaseChangeStrictHenselization_proof`, still assumes `[]`, standard axioms.
* Verbatim statement copies check `rfl`.
* Autofold spec `scratch/neron-sh-proof/autofold.json`: dry run 34/11 on 45 → 33/11 on 44, and the dry-run fold
  module compiles with standard axioms.

**What remains.** Nothing for this field. Integrator: prefer this spec over dict-models' entry for the same field,
which adds the leaf `BLR_7_2_1`.

Report: docs/research/neron-sh-proof.md. Log: scratch/neron-sh-proof/log.md.
