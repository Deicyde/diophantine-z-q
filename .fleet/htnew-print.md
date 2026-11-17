# htnew-print (fleet note)

**Result: `eigenformHTNew` is discharged by one new leaf, `EigenformHTPrinted.ModularHTPrinted`, whose statement
takes in every reading point that kept ht-exists's leaf at "pending reading". Dry-run fold: strict 11/18 -> 12/17
(-1 GLUE), counting the leaf as published with flag `unread`.**

- Kato's own statement is about the étale-cohomological `V_{F_lambda}(f)`, which cannot be defined in Mathlib, so
  it cannot be restated verbatim. The leaf is the existence form: a newform (Tau Ceti `Newform`) of weight k >= 2,
  at every level, has a continuous rho over Qbar_l, unramified outside Nl. Either arithmetic Frobenius has trace
  a_p and the HT weights are {0,1-k}, or geometric Frobenius has trace a_p and the weights are {0,k-1}. No
  semisimplicity is asked. The trace clause is universal (no algebraicity of a_p asserted).
- Proved in Lean (`ZInQKernel/Contrib/OneProof/EigenformHTPrinted.lean`, standard axioms):
  - `exists_ss`: semisimplification of a 2-dim HT rep keeps its weights (Tate–Sen spaces of a triangular rep vs
    its diagonal);
  - the dual (HTDual, with Tate's theorems already proved on main);
  - the newform dictionary (newform-dict's `NewformDict.lean`, copied byte-identical);
  - the Chebotarev/Brauer–Nesbitt transport;
  - the converse over the LEAF fields dsThm965Printed, eigenformCoeffFieldFinite, dsThm966Printed.
- `#discharges`: `eigenformHTNew` by `eigenformHTNew_of_printed`; it still assumes ModularHTPrinted and
  EigenformCoeffFieldFinite (the latter is an existing LEAF field).
- Autofold spec: `scratch/htnew-print/autofold.json`. The dry-run module compiles.
- Open: the survey locators (Taylor 2004 Toulouse; Gee 2022 ENT §2) are UNVERIFIED. If a rater holds that only
  Kato's V_{F_lambda}(f) statement is the print, the leaf is a consequence of it and the fold is count-neutral.
  Proposed locators.md row: report §3. The fold itself is left to the integrator.
- Report: `docs/research/htnew-print.md`.
