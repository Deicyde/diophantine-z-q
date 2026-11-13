# gz-license: Apache-2.0 §4 pass over the vendored Tau Ceti code (branch wip/gz-license)

**Result.** Every vendored Tau Ceti file that differs from its source beyond the mechanical
import rewrite now carries a `-- Modified for the Z-in-Q kernel: …` line under its provenance line.
`ThirdParty/TauCeti/NOTICE` lists gz-decomp's newly vendored modules and all 29 modified files.
No Lean declarations were proved; this is a licensing task.

**diffcheck2.py counts** (VERIFIED, `scratch/gz-license/diffcheck-{before,after}.txt`):

| | IDENT | NOTE-ONLY | MOD-NOTED | MOD-UNNOTED | NOPROV |
|---|---|---|---|---|---|
| before (after merging main) | 1395 | 0 | 9 | 20 | 39 |
| after | 1395 | 0 | 29 | **0** | 39 |

**Steps.**
1. Merged origin/main (578fb953). The only conflict was add/add on
   `NumberTheory/ModularForms/Basic.lean`; the two sides differed only by main's §4(b) note.
   Resolved with main's version (merge 09735e9b).
2. Added one note line to each of the 20 MOD-UNNOTED files: the 19 that kw-new took from commit
   97a5b235 and gz-decomp's `ModularForms/LFunction/Sign.lean`. Script: `scratch/gz-license/addnotes.py`.
3. Updated NOTICE: a source entry for gz-decomp (45 modules new relative to main, all from
   commit 5a01f5fe, list in `scratch/gz-license/new-modules.txt`), the 20 files added to the
   modified list, and the wording adjusted to cover kw-new's import-only changes.
4. Built the 20 touched modules with one `lake build`: it succeeded (5893 jobs), all 20 were
   rebuilt, and there was no `sorry`.

**Files changed** (paths under `ZInQKernel/Contrib/TauCeti/`; each gained one comment line only):
- GroupTheory/GroupAction/Norm.lean
- GroupTheory/SpecificGroups/Cyclic/PowMonoidHom.lean
- NumberTheory/ClassFieldTheory/ClassFields/KroneckerWeber.lean
- NumberTheory/ClassFieldTheory/ClassFields/RaySubgroup.lean
- NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Basic.lean
- NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Ramification.lean
- NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Reciprocity.lean
- NumberTheory/ClassFieldTheory/Global/ClassFormation.lean
- NumberTheory/ClassFieldTheory/Global/CorestrictionLocalization.lean
- NumberTheory/ClassFieldTheory/Global/Kummer/Index.lean
- NumberTheory/ClassFieldTheory/Global/LocalArtin/Compatibility.lean
- NumberTheory/ClassFieldTheory/Global/LocalArtin/Frobenius.lean
- NumberTheory/ClassFieldTheory/Global/Reciprocity.lean
- NumberTheory/ClassFieldTheory/GlobalExistence/NormLimitation.lean
- NumberTheory/ModularForms/LFunction/Sign.lean
- NumberTheory/NumberField/InfinitePlace/Completion/Real.lean
- RepresentationTheory/Cyclic/Norm.lean
- RepresentationTheory/Homological/ContCohomology/Corestriction/Mackey/Pullback.lean
- RingTheory/Polynomial/Cyclotomic/PrimePow.lean
- Topology/Algebra/Star/Completion.lean
- plus `ThirdParty/TauCeti/NOTICE`, and the merge resolution of `NumberTheory/ModularForms/Basic.lean`.

**For the integrator.** `Backport/Mathlib/Polynomial.lean` (task kw-new) has a Tau Ceti copyright
header but no provenance line. Its own comment says the proof was written for this project.
The rules did not allow me to edit the file, so NOTICE now states this instead. The
integrator may want to replace that header with the project's own.

**What remains:** nothing.

**NOTICE diff** (against main):
```diff
diff --git a/ThirdParty/TauCeti/NOTICE b/ThirdParty/TauCeti/NOTICE
index 70359064..59298327 100644
--- a/ThirdParty/TauCeti/NOTICE
+++ b/ThirdParty/TauCeti/NOTICE
@@ -19,6 +19,17 @@ Repository: https://github.com/TauCetiProject/TauCeti
 - Commit 5a01f5fe (as above): the 206 further modules vendored by the Z-in-Q task
   t25-newform (the closure of the newform decomposition; list in
   scratch/t25-newform/vendor-new.txt).
+- Commit 5a01f5fe (as above): the modules vendored by the Z-in-Q task gz-decomp
+  (the closure of ModularForms.LFunction.Sign, ModularForms.Twist.Basic,
+  EllipticCurve.CanonicalHeight.Basic, EllipticCurve.MordellWeil.NaiveHeight and
+  EllipticCurve.GaloisDescent; list in scratch/gz-decomp/tc-modules.txt). Most of
+  them are also vendored by t25-newform, with identical content; the 45 not vendored
+  by an earlier task fill AlgebraicGeometry/EllipticCurve/ (CanonicalHeight,
+  MordellWeil, VariableChange, Weierstrass, GaloisDescent),
+  NumberTheory/ModularForms/ (AtkinLehner/, Fricke/, Newforms/, Petersson/,
+  LFunction/, Twist/, HeckeSlash/ and four top-level files), and single modules in
+  Analysis/, FieldTheory/Galois/, LinearAlgebra/, NumberTheory/LSeries/ and
+  NumberTheory/MulChar/ (list in scratch/gz-license/new-modules.txt).
 
 Location in this repository
 ---------------------------
@@ -42,7 +53,9 @@ Modified files
 --------------
 
 Some vendored files were modified beyond these mechanical changes, to compile against
-the Mathlib revision pinned by this repository (older than the one Tau Ceti used).
+the Mathlib revision pinned by this repository (older than the one Tau Ceti used), or,
+for files taken from commit 97a5b235, to use the Backport/ files and the commit-5a01f5fe
+modules vendored here.
 Each such file carries, directly under its provenance line, a line
 
   -- Modified for the Z-in-Q kernel: <what changed>.
@@ -51,20 +64,46 @@ Each such file carries, directly under its provenance line, a line
 modifications are distributed under the same license. At the time of writing these
 are (paths relative to ZInQKernel/Contrib/TauCeti/):
 
+- GroupTheory/GroupAction/Norm.lean
+- GroupTheory/SpecificGroups/Cyclic/PowMonoidHom.lean
+- NumberTheory/ClassFieldTheory/ClassFields/KroneckerWeber.lean
+- NumberTheory/ClassFieldTheory/ClassFields/RaySubgroup.lean
 - NumberTheory/ClassFieldTheory/Formation/InvariantKernel.lean
+- NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Basic.lean
+- NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Ramification.lean
+- NumberTheory/ClassFieldTheory/Global/AdmissibleModulus/Reciprocity.lean
+- NumberTheory/ClassFieldTheory/Global/ClassFormation.lean
+- NumberTheory/ClassFieldTheory/Global/CorestrictionLocalization.lean
+- NumberTheory/ClassFieldTheory/Global/Kummer/Index.lean
+- NumberTheory/ClassFieldTheory/Global/LocalArtin/Compatibility.lean
+- NumberTheory/ClassFieldTheory/Global/LocalArtin/Frobenius.lean
+- NumberTheory/ClassFieldTheory/Global/Reciprocity.lean
+- NumberTheory/ClassFieldTheory/GlobalExistence/NormLimitation.lean
 - NumberTheory/ModularForms/Basic.lean
+- NumberTheory/ModularForms/LFunction/Sign.lean
+- NumberTheory/NumberField/InfinitePlace/Completion/Real.lean
+- RepresentationTheory/Cyclic/Norm.lean
 - RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete.lean
+- RepresentationTheory/Homological/ContCohomology/Corestriction/Mackey/Pullback.lean
 - RepresentationTheory/Homological/GroupCohomology/PrimeIndex.lean
 - RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean
+- RingTheory/Polynomial/Cyclotomic/PrimePow.lean
 - Topology/Algebra/Group/Profinite/Generation.lean
 - Topology/Algebra/Group/Profinite/Sylow/Basic.lean
 - Topology/Algebra/Group/Profinite/Sylow/Containment.lean
 - Topology/Algebra/Group/Profinite/Sylow/Existence.lean
+- Topology/Algebra/Star/Completion.lean
 
-The changes are described one line per file in docs/research/tc-port.md. Comparing a
-vendored file with the source module at the commit named in its provenance line
-shows every edit.
+Each file's note line says in a few words what changed. The 19 files with a
+commit-97a5b235 provenance line (task kw-new) mostly differ from their source only by
+extra imports of Backport/ modules; ModularForms/LFunction/Sign.lean is task gz-decomp's;
+the changes in the remaining files are also described in docs/research/tc-port.md.
+Comparing a vendored file with the source module at the commit named in its provenance
+line shows every edit.
 
 Files under ZInQKernel/Contrib/TauCeti/ without a Tau Ceti copyright header are
 original to this project and are not part of Tau Ceti: MathlibBackport/Sylow.lean
 (a backport of a Mathlib declaration) and Notice.lean (an attribution docstring).
+Backport/Mathlib/Polynomial.lean (task kw-new) carries a Tau Ceti copyright header but
+no provenance line: it states a Mathlib lemma (Polynomial.X_pow_sub_X_ne_zero, absent
+from the pinned Mathlib) with a proof written for this project, as its comment says.
```
