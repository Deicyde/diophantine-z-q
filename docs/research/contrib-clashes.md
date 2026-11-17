# contrib-clashes: every Contrib module now imports in one environment

**Result (VERIFIED).** On branch `wip/contrib-clashes` (based on main e1b31749), a single file importing all 4368
modules of `ZInQKernel/Contrib/` elaborates. So does a file importing those modules plus `ZInQKernel`,
`ZInQKernel.OneProof.Main` and `ZInQKernel.OneProof.Discharges`; in that file `frozenTarget` and the headline theorem
still depend only on `[propext, Classical.choice, Quot.sound]`. The aggregate `ZInQKernel/Contrib/AllContrib.lean`
was stale: it had 3047 imports and none from OneProof. It now imports all 4368 other Contrib modules, and
`lake build ZInQKernel.Contrib.AllContrib` succeeds (14381 jobs). Every Contrib module builds: `lake build` of all
4368 modules takes 14380 jobs with 0 errors. No statement of any hypothesis, open or closed, changed. The
`#discharges` results are unchanged; one summary count changed, see §4.

## 1. The clash list before (main e1b31749)

`scratch/contrib-clashes/ClashScan.lean` reads the `.olean` of every module in the import closure of all Contrib
modules: 16744 modules and 810239 constants. It does not build an environment, and it lists every constant
stored by two modules. It also applies Lean 4.35's own import rule. In `Lean/Environment.lean`, `finalizeImport`
calls `subsumesInfo`, which accepts a duplicate in only these cases:
- both are theorems with the same type, universe parameters and `all` list;
- a theorem and the axiom made from it;
- two Prop-typed axioms.

Any other duplicate aborts the import with "environment already contains" (VERIFIED, read in the source).

Project modules had **72 duplicated declaration names, in 74 module pairs**, excluding realized auxiliary
lemmas (`eq_N`, `congr_simp`, …). The full list is `scratch/contrib-clashes/clashes-before.txt`.

| pair | names | fatal |
|---|---|---|
| `HDecomp.Textbook.Different` / `Contrib.Different.Local` | 66 (`TDifferent.*`, `PkgI6.*`) | **6 definitions**: `TDifferent.phiF`, `phiExpl`, `filtR`, `resHom`, `PkgI6.MonogenicDVR`, `PkgI6.TraceContainsRamificationIdx` |
| `OneProof.GrossZagierHeegner.WeilJacobi` / `…JacobiLambdaDeriv` | 3: `ZInQ.GZWeil.jacobiLambdaDeriv`, `etaModelDifferential`, `modularParamC1` | no (identical theorems) |
| CloudW07 `Modules/Extension` / `Cohomology/{Flasque, DirectImage/Affine, AcyclicResolution}` | 1 auto-named local instance `AlgebraicGeometry.Scheme.Modules.instPreservesZeroMorphisms…_zInQKernel` (3 pairs) | no |
| `OneProof.HP23Proof.Case1` / `Case3` | `ZInQ.Contrib.HP23Proof.instFactPrimeValNat_zInQKernel_1` | no |
| `OneProof.TYZGenusFold.Ideles` / `Local` | `ZInQ.Contrib.TYZGenusFold.instFactPrimeValNat_zInQKernel` | no |

Only the six definitions block the import. The memory note's figure of "103 clashes" counted accepted duplicates
too, over an older tree. Before the fix, the all-import file failed at once (VERIFIED):
`import ZInQKernel.HDecomp.Textbook.Different failed, environment already contains
'PkgI6.TraceContainsRamificationIdx' from ZInQKernel.Contrib.Different.Local`. The accepted duplicates were
harmless; for example, `TYZLcalOne` already imported both GZWeil files. They were removed anyway, as the task
asked.

The scan also finds duplicates inside Lean core and Mathlib: realized lemmas exported as axioms by `module`
files, and two identical Mathlib instance theorems. Lean accepts all of them, and they are outside the project.

## 2. Fixes (one canonical declaration per name)

Only Contrib files were edited, and no importer needed a change.

1. **`Contrib/Different/Local.lean`** now re-exports the canonical `ZInQKernel.HDecomp.Textbook.Different`. Its old
   body matched that file character for character, up to line breaks and comments (checked with `diff`). All 66
   names stay available to its importers (`Different/SerreLocal`, `G15/LadicBridge`) with the same types and
   values.
2. **`GrossZagierHeegner/WeilJacobi.lean`** (gz-weil) now imports `JacobiLambdaDeriv.lean` (jacobi-lambda), which is
   canonical.
   - gz-weil's own proof of the same statement is kept as `ZInQ.GZWeil.jacobiLambdaDeriv_viaCuspForms`, with the
     same type, and its `shimuraCMParamCd_proved` still uses it.
   - Its copies of `etaModelDifferential` and `modularParamC1` are removed. They are identical statements, now
     imported.
3. **`HP23Proof/Case3.lean`, `TYZGenusFold/Local.lean`**: `local instance (p : Nat.Primes) : Fact p.1.Prime` became
   `private local instance`, so its generated name is private to the module.
4. **CloudW07 `Cohomology/Flasque.lean`, `Cohomology/DirectImage/Affine.lean`, `Cohomology/AcyclicResolution.lean`**
   (vendored, Apache-2.0): the anonymous local `PreservesZeroMorphisms` instance became `private`, and
   `Modules/Extension.lean` keeps the public one. Each file's third comment line and the directory's NOTICE record
   the change.
5. **`Contrib/AllContrib.lean`** is regenerated to import all 4368 other Contrib modules.

None of these files is pinned by upstream (`scratch/upstream/baseline-lean-files.txt`; VERIFIED).

## 3. The clash list after

`scratch/contrib-clashes/scan-after.txt` and `clashes-after.txt` show:
- **0 fatal clashes**;
- **0 duplicated non-auxiliary names between project modules**;
- the only remaining non-auxiliary duplicates are Mathlib's own two identical instance theorems, in
  `Mathlib.CategoryTheory.Abelian.CommSq` and `Mathlib.CategoryTheory.Abelian.Monomorphisms`.

## 4. Invariants (VERIFIED)

`scratch/contrib-clashes/Baseline.lean` was run before and after the fixes; the outputs are `baseline-before.txt`
and `baseline-after.txt`.
- **Unchanged, byte for byte:** `#check` and `#print axioms` of `ZInQ.OneProof.frozenTarget` (standard axioms) and of
  `HDec.HSyn.sixContactMin_of_open55`, and all 49 `DISCHARGES` blocks (hypothesis, theorem, still-assumes,
  axioms).
- **Changed:** only the summary line, where "11113 theorems checked" became 11116. The 3 extra theorems are new
  distinct constants in Main's closure, and none of them discharges anything:
  - `jacobiLambdaDeriv_viaCuspForms`;
  - the two private local instances. Before the fix, each was merged with its identical twin.
- `scripts/print_axioms.lean`: all 542 declarations still use only the standard axioms.

## 5. Deliverable format

No hypothesis was discharged, and none was reduced, so there is no new `Contrib/OneProof/<Name>.lean` theorem, no
`autofold.json` and no new leaf to rate. The branch is a maintenance fold. The integrator can merge
`wip/contrib-clashes` as is, because it touches only the Contrib files listed in §2, the NOTICE and the scratch,
docs and fleet notes. To keep the property, rerun `lake env lean scratch/contrib-clashes/ClashScan.lean` (4 s,
oleans only) or `lake build ZInQKernel.Contrib.AllContrib` after adding modules. New modules must be appended to
`AllContrib.lean`.
