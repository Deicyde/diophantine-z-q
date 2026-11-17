# Hash-guard waiver for lane74 (fork issues #76-#79), written by lane74b

**Request.** Accept the `DumpCompact`/`cmp_hashes` differences below for the landing of `wip/lane74b` (= lane74 merged
into the integration tip, f558b164, plus lane74b's commits). They come from three changes: the pole polynomial back to the
manuscript's (#76), the new headline/`frozenTarget` (#78), and the Route K deletion (#77). **No constant of
`ZInQKernel/OneProof/H/` changed.** lane74b's own Lean change, `Hypotheses/Pole.lean` reverted byte for byte to
b570b14ee with its docstrings, changes no constant record (section 4). No RouteK file was moved (section 5).

## 1. How it was checked

`scratch/lane74b/HashDump.lean` writes `scratch/one-proof/DumpCompact.lean`'s record (name, module, universe parameters,
hash of the type, hash of the value) for **every constant of every `ZInQKernel` module** in the environment of
`import ZInQKernel` + `import ZInQKernel.OneProof.Main`. That is wider than DumpCompact, which covers only the
`ZInQKernel.OneProof` modules. `scratch/lane74b/cmp_hashes_full.py BEFORE AFTER` compares two dumps.

* base: be9a6ba4a (`f558b164^1`, the integration tip before the lane74 merge), in a detached worktree outside
  `~/dzq-wt` built from `~/dzq-check2`'s build (at be9a6ba4a; `lake build ZInQKernel +ZInQKernel.OneProof.Main` replayed
  16314 jobs with nothing rebuilt): 188 726 constants.
* f558b164 (lane74 merged): 179 119 constants.
* lane74b tip, after rebuilding with Pole.lean reverted: 179 119 constants (section 4).

The full output is `scratch/lane74b/hashcmp-base-f558.txt`. The dumps are 25 MB each, so they were not committed.
They are `~/l74b-hashes-{base,f558,after}.txt` on the devserver.

## 2. Changed constants (in both dumps, different record): exactly these 20

Changed because of the #76 revert of the pole polynomial (`A + e` → `A + 3e`, `Az² + eH` → `Az² + 3eH`; Parity,
PoleObstruction and Core restored from b570b14ee):

| constant | module | field that changed |
| --- | --- | --- |
| `ZInQ.polePoly` | Hypotheses.Pole | value |
| `ZInQ.Manuscript.polePoly` | Hypotheses.PoleManuscript | value (now an abbrev of `ZInQ.polePoly`) |
| `ZInQ.Manuscript.PoleSoluble` | Hypotheses.PoleManuscript | value (abbrev) |
| `ZInQ.Manuscript.PoleCompleteness` | Hypotheses.PoleManuscript | value (abbrev) |
| `ZInQ.Syntax.poleT1` | Syntax.Templates.Core | value |
| `ZInQ.Syntax.poleT2` | Syntax.Templates.Core | value |
| `ZInQ.Syntax.poleT1.eq_1` | Syntax.Templates.Core | type |
| `ZInQ.Syntax.poleT2.eq_1` | Syntax.Templates.Core | type |
| `ZInQ.Syntax.VarsIn.polePoly` | Syntax.Templates.Core | value |
| `ZInQ.Syntax.ev_polePolyX` | Syntax.Templates.Core | value |
| `ZInQ.Size.poleTemplate_maj` | Size.Majorants.Templates | value (source unchanged; its proof term follows `poleT1`/`poleT2`) |
| `ZInQ.Mult.abscissa_val_even` | Multiplication.Certificate.Parity | type, value |
| `ZInQ.Mult.poleSystem_of_polePoly_eq_zero` | Multiplication.Certificate.Parity | type, value |
| `ZInQ.Mult.pole_obstruction` | Multiplication.Certificate.Parity | value |
| `ZInQ.Assembly.poleSoluble_no_negative_odd` | Assembly.Local.PoleObstruction | value |
| `ZInQ.polePoly.eq_1` | Syntax.Templates.Core (before: RouteK.Assembly.Points) | module, type |

Changed because of #78 (the headline):

| `ZInQ.OneProof.frozenTarget` | OneProof.Main | type, value (`hPC : PoleCompleteness` replaces the five TYZ/GZ hypotheses; bundles as at the tip) |

Changed only in the module field: auto-generated equation lemmas that are now generated first in another module,
because the module that generated them before was deleted (#77). Type and value hashes are unchanged:

| `ZInQ.poleS0.eq_1` | Multiplication.Certificate.ConstantsProperties (before: Multiplication.Certificate.Parity) | module |
| `ZInQ.RouteK.natConfig.congr_simp` | RouteK.Selmer.Bits (before: RouteK.Assembly.PoleCompleteness) | module |
| `ZInQ.RouteK.signBit.eq_1` | RouteK.Selmer.Covering (before: RouteK.Assembly.SecondCurve) | module |

The brief expected `polePoly`, `poleT1`, `poleT2`, `abscissa_val_even` and their dependents. The dependents are the
rows above, and nothing else changed. In particular `poleS0` and every `not_dvd_2730…` lemma are unchanged.

## 3. Removed and added constants

* Removed: 9613 constants.
  * 8538 are in the 195 deleted files (`scratch/lane74/deleted-files.txt`).
  * 1055 are in 57 files that still exist but that neither `ZInQKernel` nor `OneProof.Main` imports any more
    (Tau Ceti modular-forms and canonical-height modules that only deleted files imported). They still build as
    Contrib files.
  * 20 are in modules that both environments contain. `Main.lean`: the 9 CR₃/22P variants
    (`…_of`, `…_of_addMulBound`, `…_of_certifiedRankSel`, `…_of_certifiedRankSel_greenTaoDense`, `…_of_goodPrimeAP`,
    `…_of_greenTaoDense`, `…_of_nodeCheck`, …). `MainGreenTao.lean`: 4 (`…_of_certifiedRankSel_goodPrimeDensity`,
    `…_of_goodPrimeDensity`, `…_of_sixContactMin_certifiedRank`, `…_of_sixContactMin_certifiedRankSel`).
    `Parity.lean`: 6, the Route K copies `ZInQ.Mult.poleSystem`, `poleSystem_no_negative_odd_valuation` (and its 3
    `_proof_1_k`) and `congruentCurve_rhs_nonzero_and_valuation`. `PoleManuscript.lean`: `ZInQ.Manuscript.polePoly._proof_1`.
* Added: 6 constants. `ZInQ.Manuscript.polePoly_eq`, `ZInQ.Syntax.poleT1._proof_1`, and the headline and its variants
  `…_of_sixContactMin_poleCompleteness`, `…_of_poleCompleteness_goodPrimeDensity`, `…_of_poleCompleteness_goodPrimeAP` and
  `…_of_poleCompleteness_greenTaoDense`.

## 4. OneProof scope (what DumpCompact checks)

* `ZInQKernel.OneProof.H.*`: 17 686 records before and after, byte-identical (`cmp` of the sorted record lists).
* Other `ZInQKernel.OneProof` modules: `frozenTarget` changed (section 2). The 140 constants of the deleted
  `OneProof/TYZSplit` (137) and `OneProof/TopChain` (3) are gone. `OneProof.Genus.*` is unchanged.
* lane74b tip (Pole.lean reverted, rebuilt) vs f558b164: 179 119 = 179 119 constants, **0 changed, 0 removed, 0 added**
  (`scratch/lane74b/hashcmp-f558-after.txt`); so be9a6ba4a vs the lane74b tip is exactly sections 2-3
  (`scratch/lane74b/hashcmp-base-after.txt`, identical to `hashcmp-base-f558.txt`).

## 5. Route K files the H chain reaches: none was cut, none moved

* H's import closure (OneProof/H/**, HDecomp/** and OneProof/Main) reaches 58 RouteK modules, among them
  `RouteK.Slots.Theta` → `Multiplication.Certificate.Parity` → `Hypotheses.Pole`. All 58 files exist and compile, and
  `RouteK.Slots.Theta` (27 constants) and `RouteK.Slots.Basic` (39) have the same records before and after.
  `OneProof/H/LPrefix` → `Multiplication.Certificate.ConstantsProperties` → `Hypotheses.Pole` is intact
  (ConstantsProperties gains only the relocated `poleS0.eq_1`).
* No file was moved, so no import line of `ZInQKernel/OneProof/H/` changed. lane74 deleted none of these files
  (its importer finding 1), so nothing has to move until the TYZ cone that H imports is cut
  (`docs/research/lane74b.md`, item 7).
