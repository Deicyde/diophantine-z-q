# lane74b: the lane74 follow-ups (checklist items 1, 3, 4, 5, 7 and the H-reach / hash-waiver part of item 2)

**Result.** Every item on the list is done or answered, and no statement was changed or added. Section 6 lists the
checks.

* **Item 2 (H reach, hash waiver).** No Route K file that the H chain reaches was cut, so nothing was moved. A hash
  comparison over every `ZInQKernel` constant, from the pre-lane74 tip be9a6ba4a to this branch, finds exactly 20
  changed constants:
  * the pole-polynomial set: `polePoly`, `poleT1`, `poleT2`, `abscissa_val_even` and 12 dependents;
  * `frozenTarget`;
  * three auto-generated equation lemmas, whose module field changed only.

  No constant of `ZInQKernel/OneProof/H/` changed: 17 686 records, byte-identical. The waiver is
  `scratch/lane74/HASH-WAIVER.md`.
* **Item 5 (blueprint).** The 59 blueprint pages that named the 199 deleted declarations are marked:
  * 51 lose their `lean:`/`statement:`/`proof:` keys and get a removal note;
  * 8 keep the names that still exist.

  `autoform check blueprint --lean-root .` and `render --require-declarations` now pass.
* **Item 1 (autofold).** `autofold.py` now checks the Main it writes, and `scratch/lane74/gate.sh` is the dry-run
  gate.
* **Item 3 (Pole.lean).** `Pole.lean` is reverted byte for byte, docstrings with body, to b570b14ee.
* **Item 4 (axiom recipe).** STATUS.md's recipe names the new headline and `frozenTarget`.
* **Item 7 (TYZ/GZ modules).** The TYZ/GZ modules that H still compiles are listed, with the constants H actually
  uses from them. Re-homing them is not cheap: H genuinely uses the Shimura/CM development in `Contrib/TYZGenus`.

## Item 1: autofold and the gate

`ZInQKernel/OneProof/Main.lean` at f558b164 already has the shape that `autofold.py`'s parser (line 68) needs:
* the literal `theorem _root_.ZInQ.OneProof.frozenTarget`, then the binders, then `(hPC : ZInQ.PoleCompleteness) :`,
  a newline and `ZInQ.FrozenTarget`, with no binder comments;
* the call `(HDec.HSyn.sixContactMin_of_open72 r t l) hPC`;
* the imports `OneProof.H.TailZ79`, `MainGreenTao` and `Contrib.OneProof.DeRhamRange`.

Change to `scripts/one_proof/autofold.py`. `main_state` now also parses a given text, and its docstring states the
required shape. After switching Main, autofold parses the switched text again and stops with an error unless all of
these hold:
* the top theorem is `sixContactMin_of_open{N+1}`;
* the `TailZ` import is the new module;
* every other import line is unchanged;
* the binders are the old ones with the bumped bundle generations.

Before, a `str.replace` that matched nothing would have written an unchanged or half-switched Main without an error.
`--dry-run` keeps its stdout (the count line, then the module) and prints the switched Main on stderr.

Dry runs, both VERIFIED. Neither wrote anything to the tree.
* A no-op spec (no discharge) gives `sixContactMin_of_open73 r t l := sixContactMin_of_open72 r t l` over TailZ79.
  The switched Main keeps MainGreenTao, DeRhamRange and `hPC`.
* A one-field spec (`picRepresentableAbVar`) gives `OpenAddedLeaves28`, with `(l : HDec.HSyn.OpenAddedLeaves28)`
  in the switched Main.

**Gate.** The chain scripts live outside the repository, so the gate change is a script for the lead,
`scratch/lane74/gate.sh`, to run after `lake build +ZInQKernel.OneProof.Main`. It:
1. runs the no-op `autofold.py <spec> --dry-run`;
2. checks that the tree is unchanged;
3. compiles the printed fold module against TailZ79;
4. requires the standard axioms;
5. prints `GATE=ok`.

Result on this branch: `AUTOFOLD-DRYRUN-EXIT=0`, `TREE-UNCHANGED=yes`, `GATEFOLD-EXIT=0`,
`GATEFOLD-AXIOMS=standard`, `GATE=ok` (VERIFIED, `scratch/lane74b/gate-output.txt`).

## Item 2 (part): what H reaches under Route K, and the hash waiver

* **Nothing is cut.**
  * The import closure of `OneProof/H/**`, `HDecomp/**` and `OneProof/Main` reaches 58 `RouteK` modules
    (`scratch/lane74b/h-reach-routek.txt`; tool `scratch/lane74b/reach.py`).
  * All 58 files exist, and they build in `lake build +ZInQKernel.OneProof.Main`.
  * `RouteK.Slots.Theta` → `Multiplication.Certificate.Parity` → `Hypotheses.Pole` is intact (Theta's 27 and
    Slots.Basic's 39 constants have the same records before and after), and so is
    `OneProof/H/LPrefix` → `Multiplication.Certificate.ConstantsProperties` → `Hypotheses.Pole`.
  * Every path from H into Route K starts at `OneProof/H/TailZ34` → `Contrib/OneProof/RayClassShimura` →
    `Contrib/TYZGenus/ShimuraModFn` (`scratch/lane74b/paths.py`).
* **What H actually uses** (`scratch/lane74b/Uses.lean`, `Uses2.lean`; VERIFIED, compiled):
  * `ZInQ.OneProof.frozenTarget`'s closure has 292 948 constants. From the 79 kept Route K/TYZ/CR3 modules it uses
    only two: `ZInQ.Contrib.TYZGenus.Shimura.sqrt_mul_self_C` and the instance
    `ZInQ.Contrib.TYZGenus.X0.instDecidableEqComplex_zInQKernel`. It also uses 12 constants of
    `RouteK.Selmer.CharSum` through `Density.CharSum` (the headline's Proposition D, not H).
  * Every constant that an H-side module declares, not only those in that closure, was scanned too. Such constants
    reference 62 kept constants, from 10 modules:
    * `TYZGenus.{CM, RingClass, ShimuraField, ShimuraMain, ShimuraModFn, ShimuraRecip, ShimuraZn, X0}`;
    * `TYZDecomp.CurveA` (`Qbar`);
    * `RouteK.Rank5b.Sec3.RedeiStatement` (`QNeg`, `QNeg.factNotIsSquare`, `QNeg.numberField`).

    The referencing modules are `Contrib/OneProof/RingClassLattice` (T5Glue, 55 references), `RayClassShimura`
    (7), `DeligneComponentsY3Used`, `GR56Lattice` and `WeberField` (one each).
* **Nothing was moved.** No `ZInQKernel/OneProof/H/` import line changed, because lane74 deleted none of the files H
  reaches. Moving the 58 RouteK files to a non-RouteK path would only rename them, since the TYZGenus files H uses
  import them. It would also rename their private constants, which changes hashes. A cut that lets them go is
  under item 7.
* **Hash waiver.** `scratch/lane74/HASH-WAIVER.md`. The tools are `scratch/lane74b/HashDump.lean` (the
  `DumpCompact.lean` record for every `ZInQKernel` constant of the environment of `ZInQKernel` + `OneProof.Main`)
  and `scratch/lane74b/cmp_hashes_full.py`. From be9a6ba4a (pre-lane74 tip, 188 726 constants) to f558b164
  (179 119 constants):
  * **Changed:** 20 constants.
    * #76: `ZInQ.polePoly`, `Manuscript.{polePoly, PoleSoluble, PoleCompleteness}`, `Syntax.{poleT1, poleT2,
      poleT1.eq_1, poleT2.eq_1, VarsIn.polePoly, ev_polePolyX}`, `Size.poleTemplate_maj`,
      `Mult.{abscissa_val_even, poleSystem_of_polePoly_eq_zero, pole_obstruction}`,
      `Assembly.poleSoluble_no_negative_odd` and `polePoly.eq_1`.
    * #78: `OneProof.frozenTarget`.
    * Module field only: `poleS0.eq_1`, `RouteK.natConfig.congr_simp` and `RouteK.signBit.eq_1`. These equation
      lemmas are now generated first in another module, because the module that generated them was deleted.
  * **Removed:** 9613 constants.
    * 8538 are in the 195 deleted files.
    * 1055 are in 57 Tau Ceti files that are no longer imported.
    * 20 are in surviving modules: the old CR₃ variants of `Main`/`MainGreenTao` and Parity's Route K copies.
  * **Added:** 6 constants, the new headline variants, `polePoly_eq` and one `_proof_1`.
  * `poleS0` and the `not_dvd_2730` lemmas are unchanged. OneProof/H is byte-identical. From f558b164 to this
    branch, after the rebuild with Pole.lean reverted: 0 changed, 0 removed, 0 added (VERIFIED).

## Item 3: Pole.lean

* Lane74's `Pole.lean` (f558b164) already had no Route K wording. The words "x + ℓ" and "PC is a theorem from CR₃"
  were in the Route K version, blob d61c9c41.
* As asked, the file is now reverted byte for byte, docstrings with body, to b570b14ee. That is the kernel skeleton
  cb193ab1b's file, blob 842f08ae. Only docstrings differ from f558b164, and no constant record changes (item 2).
* FINDING: upstream's contract (9c7b60ef) pins `ZInQKernel/Hypotheses/Pole.lean` at d61c9c41, the Route K
  polynomial. Any manuscript-polynomial `Pole.lean` therefore differs from the pinned hash, so landing upstream
  needs a contract change for this file.
* `ZInQKernel/Hypotheses/CertifiedRank.lean:10` still names the deleted `poleCompleteness_of_certifiedRank`. It is
  one of the kept H-reach files (item 7) and is not editable here.

## Item 4: print_axioms and the STATUS recipe

* `scripts/print_axioms.lean` already had lane74's update:
  * the headline `…_of_sixContactMin_poleCompleteness`, its variants, the replaced hypotheses and the H glue;
  * 463 declarations, none of them from the deleted TYZ/GZ cone. Run on this branch: 463 declarations, 0 nonstandard; 462 are
    defined in `ZInQKernel` modules and `Submission.green_tao` in ThirdParty; none is in a RouteK, TYZ, GZ, Hecke,
    CR₃, CertifiedRank, PSide or GaussFE module (VERIFIED, `scratch/lane74b/print_axioms-modules.txt`).
* Added: a header note that `frozenTarget` is checked by the `+ZInQKernel.OneProof.Main` build. The file imports only
  `ZInQKernel`, and the chain runs it before the OneProof build, so the import was not added.
* STATUS.md (the recipe after "To build and check"): it now builds `+ZInQKernel.OneProof.Main`, names the
  `frozenTarget` axiom check, and describes print_axioms' 463 declarations with the new headline. The paragraph about
  the 542 declarations at fork main 5e235a40 is a record of that landing and is unchanged. The other TYZ/GZ prose in
  STATUS.md is #81's.

## Item 5: blueprint pages

* `scratch/lane74b/blueprint_mark.py` reads the base `autoform check blueprint --lean-root .` output: 199 errors in
  59 articles. Ten of them (`route-k/realization`, names under `ZInQ.RouteK.Slots`, which is also a structure)
  carry an extra "is a structure" message.
* For each article it drops the missing names from `lean:`. If no name remains, it also drops `statement:` and
  `proof:`, and it puts this note after the title: removed with Route K (#77), at the tag `route-k-final`, kept until
  #81.
* No article was deleted and no link changed.

Pages touched (59; `scratch/lane74b/blueprint-touched.txt`):
* All names removed (51): `main/` main-theorem, -infinitely-many-points, -literature, -positive-rank,
  -reading-a-gross-zagier, -selmer, -two-curves, -two-hypotheses, -tyz; `rank-5b/` cross-checks, genus-sum/{genus-sum-values,
  proposition-3-3, proposition-3-4, proposition-3-5, roots-per-block}; `rank/infinitely-many-points/` (7 pages),
  `rank/literature/l-function-cd/` (8 of 9), `rank/mordell-weil/` (9), `rank/two-curves/` (9);
  `route-k/` descent-lemma, points-pole-solubility, pole-completeness-from-cr3.
* Some names removed (8): main/main-theorem-three-hypotheses, rank-5b/genus-sum/marked-sums,
  rank/certified-rank-{of,sel-of,tyz-cl-of,tyz-of}-rk, rank/literature/l-function-cd/prime-coefficients,
  route-k/realization.

After the change (autoform-bot 46b46d6d, the CI pin), all exit 0:
* `autoform check blueprint`;
* `--lean-root .`: 776 articles, 2328 names resolved;
* `autoform render blueprint --lean-root . --require-declarations`: 175 pages.

## Item 7: TYZ/GZ modules that still compile through H's imports

No TYZ or GZ *hypothesis* remains: `frozenTarget (r t l) (hPC)`. The following modules still compile because the H chain
imports them (`scratch/lane74b/h-reach-tyz-named.txt`, 28 modules, besides the 58 RouteK modules):
* `Contrib/TYZGenus/` (15): CM, Package, RingClass, RingClassBridge, RingClassGalois, RingClassGenus, RingClassTwo,
  ShimuraCusp, ShimuraField, ShimuraMain, ShimuraModFn, ShimuraQExp, ShimuraRecip, ShimuraZn, X0.
* `Contrib/TYZDecomp/` CurveA and Leaves; `Contrib/PSide/TYZInputsIff`; `Hypotheses/TYZInputs`,
  `Hypotheses/CertifiedRank`, `Hypotheses/CR3Literature` (the `GrossZagier` def, lines 70-72, with
  `FunctionalEquation5`, `HeckeContinuation` and `IsLContinuation`).
* `Contrib/HeckeFE/Basic`, `Contrib/HeckeAll/{Continuation, Iso, LocalCd, Provider}`,
  `Contrib/GaussFE/{FunctionalEquation5, Gauss}`.

**Not re-homed, because it is not cheap.** H's T5 glue (`RingClassLattice`, `RayClassShimura`) is built on the
Shimura/CM development in `TYZGenus.{CM, Shimura*, RingClass, X0}`; it uses 62 of its constants (item 2). Those files
import Route K for unrelated declarations:
* `TYZGenus.RingClass` imports `RouteK.Rank5b.Sec3.RedeiStatement` (for `QNeg` = ℚ(√−d)), `RouteK.Redei.FourRank`
  and `Hypotheses.TYZInputs`;
* the `Shimura*` chain imports `RingClassBridge` → `Package` → `RingClass`.

So a cut means splitting files, not moving them:
1. move `QNeg` (3 constants) and the 7 `RingClass` constants H uses into a file without Route K imports;
2. point `CM`/`ShimuraRecip` at it;
3. delete the remaining 78 files.

The moved constants keep their names, but private names would change. This edits Contrib files beyond this task's
allowance, so it is a follow-up (estimate: one task, and one H rebuild of about 35 min). Renaming alone (e.g.
`TYZGenus` → `ShimuraCM`) changes nothing in the proof and would rewrite the 34 import lines of `ZInQKernel.Contrib.TYZGenus.*` (VERIFIED by grep) and rename private constants, so it was not done.

Wording for the docs (#81): "No Tian–Yuan–Zhang or Gross–Zagier statement is a hypothesis of the main theorem. Some
Lean modules with TYZ, Hecke or CR₃ in their names still compile, because the H chain's Shimura/CM lemmas
(`Contrib/TYZGenus/Shimura*`, `CM`, `RingClass`) live in them. Among them is the unused statement
`Literature.GrossZagier` in `Hypotheses/CR3Literature.lean`."

## 6. Checks

Each run on this host after the last Lean change (Pole.lean), at most one Lean process at a time. All VERIFIED.

| check | result |
| --- | --- |
| `lake build ZInQKernel +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` | OK, 16053 jobs (227 rebuilt after the Pole.lean revert, 19m39; `scratch/lane74b/build1b.txt`) |
| `#print axioms ZInQ.OneProof.frozenTarget` | `[propext, Classical.choice, Quot.sound]` (printed by the build of `OneProof/Main.lean`) |
| `scripts/print_axioms.lean` + `~/dzq-runs/axcheck.py` | 463 declarations, 0 nonstandard, no sorry; `check_target.py` ok |
| `render_open.py --check` | ok, 30 open hypotheses, 4 generated files up to date |
| `frontier_crosswalk.py --check` | ok (232 IDs) |
| `autoform check blueprint` / `--lean-root .` | both OK: 776 articles, 2328 names resolved |
| `autoform render blueprint --lean-root . --require-declarations` | OK, 175 pages (run before the Pole revert; blueprint unchanged since) |
| `scratch/contrib-kit/DischargesTest.lean` | EXIT 0: 30 open hypotheses, 11256 theorems checked, 16 discharge one (`scratch/lane74b/DischargesTest-output.txt`). Its controls `t1` (`nvLocalInertia`) and `t3` (`cartierSmooth`) name fields that are no longer open, so they print nothing. Its saved output in `scratch/contrib-kit` is stale. |
| `scratch/lane74/gate.sh` | GATE=ok |
| hash dumps (be9a6ba4a / f558b164 / this branch) | 20 / 0 changed (section on item 2) |

Not run: CONTRIB-BUILD (every Contrib file), `Contrib.AllContrib`, `scratch/h-decomposition/Leaves.lean`, the site
check. No Contrib or H source changed, and the only Lean change after f558b164 is Pole.lean's docstrings, which
change no constant (hash dump). `scratch/lane74b/PoleRefs.lean`, a listing of which pole constants OneProof cites, was stopped after 10 min with
no output; it is UNCHECKED and not needed, because the OneProof/H records are identical.

No new mathematical statements and no on-the-spot statements: the Lean changes are a docstring revert (Pole.lean) and
a comment (print_axioms.lean).
