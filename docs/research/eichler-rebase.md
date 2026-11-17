# eichler-rebase: `gonzalezRotgerProp56X6` removed on current main, −1, no new leaf

Task eichler-rebase (2026-11-16/17). Branch wip/eichler-rebase: origin/wip/eichler-bound 09896d1f with origin/main
c0f3d085 (leaf-fold33, top `sixContactMin_of_open48`, TailZ55) merged in (commit 261ebb16, no conflicts). Results log:
`scratch/eichler-rebase/log.md`. Marks: VERIFIED (compiled, computed, or read in the tree), STANDARD (published, exact
reference), SPECULATIVE, UNVERIFIED (theorem numbers from memory; no network on this host). Model work, no human review.

## 1. Result

**eichler-bound's result is rebased onto main as a fold candidate.**
* Its modules build on the merged tree with no change at all (§2).
* They coexist with every Contrib module of main (§3).
* The bypass is regenerated against main's top and compiles with the standard axioms only (§4).

The bypass gives `ZInQ.Contrib.TYZChain.frozenTarget_E`. This is Main's `frozenTarget` verbatim, except that the
research bundle is `OpenResearchLeaves32`, which is `OpenResearchLeaves31` minus `gonzalezRotgerProp56X6`, with no
field added. VERIFIED, `scratch/eichler-rebase/bypass-compile.txt`:

```
'HDec.HSyn.sixContactMin_of_open49' depends on axioms: [propext, Classical.choice, Quot.sound]
'ZInQ.Contrib.TYZChain.frozenTarget_E' depends on axioms: [propext, Classical.choice, Quot.sound]
```

**Count on main's kinds.tsv** (VERIFIED, `autofold.py --dry-run` with the count-only spec
`scratch/eichler-rebase/autofold.json`, output in `autofold-dryrun.txt`):

`strict count: 11/18 on 29 -> 11/17 on 28; strictest 11/18 -> 11/17`

This is **−1 GLUE (the row is GLUE/GLUE since the 11-16 re-rating) with no new leaf**, as expected. The open
hypotheses of `frozenTarget` go from 35 to 34.

Theorems (unchanged from eichler-bound, `ZInQKernel/Contrib/OneProof/R5fpCountLe.lean`, imports `GR56Lattice`, never
Main):

```lean
theorem EichlerBound.eichlerOptEmbBound6 (k : Type) [Field k] [NumberField k] (hk : Module.finrank ℚ k = 2)
    (R : Subring k) (hR : R ≤ (integralClosure ℤ k).toSubring)
    (hc : Nat.Coprime (LeafQM.AV.conductor R) 6) (hh : Nat.card (CommRing.Pic R) ≠ 0) :
    Finite (Quot (GRCountX6.ConjRel R)) ∧
      Nat.card (Quot (GRCountX6.ConjRel R)) ≤ 2 ^ LeafQM.AV.inertCount6 k * Nat.card (CommRing.Pic R)
theorem EichlerBound.r5fpCountLe_proof (hU : BPAnalytic.Uniformization.UniformizationLeafAll)
    (hG : ZInQ.HomLattice.GAGAMorphism) (hM : AvSplit.MumfordTorsionAlgClosed) : GR56.R5fpCountLe
```

On main, `uniformizationLeafAll` is proved (`_root_.uniformizationLeafAll_proof`, Contrib/OneProof/UniformizationLeafAll.lean).
So the bypass reads only the textbook fields `gagaMorphism` and `mumfordTorsionAlgClosed` of `OpenTextbookLeaves16`.
Both are already open, so nothing is added. Fork PRs #54 and #55 would prove these two fields; they were not merged.

## 2. Step 1: build on the merged tree (VERIFIED)

The modules main lacks are listed by `git diff origin/main HEAD -- ZInQKernel`:
* `Contrib/OneProof/R5fpCountLe.lean`;
* `Contrib/OneProof/EichlerBound/{Order, Quadratic, Defs, Embed, Unit, Crit, Key, Key6, Inv, Count, Bound}.lean`;
* `Contrib/OneProof/GR56Lattice.lean` (gr56-prove, imported by R5fpCountLe);
* `Contrib/OneProof/GRDict.lean` (gr-dict; not needed by R5fpCountLe or by the bypass).

Build results:
* `lake build ZInQKernel.Contrib.OneProof.R5fpCountLe`: `Build completed successfully (12948 jobs)`. **No edit was
  needed**, so no statement or proof was touched (`build1.log`).
* `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.GRDict`: OK, 14229
  jobs; `frozenTarget` has the standard axioms (`build2.log`).

## 3. Step 2: name clashes

`scratch/eichler-rebase/AllContribNew.lean` imports the modules this branch adds (`GR56Lattice`, `R5fpCountLe`,
`GRDict`) together with the 244 top-level modules of `ZInQKernel/Contrib/` on origin/main. A top-level module is one
that no other Contrib module imports (`contrib-tops-main.txt`). Their import closures cover all 4326 Contrib modules
of main, including the 306 `Contrib/OneProof` modules that main's own `Contrib/AllContrib.lean` omits.

* **No clash involves this branch's modules** (VERIFIED, `scratch/eichler-rebase/ClashScan.lean`, output in
  `clashscan.txt`). The scan reads the `.olean` of every module in the joint import closure: 16716 modules, Mathlib
  included, and 809300 constant names. It lists every constant name that two different modules store.
  * Result: `clashes involving this branch's modules: 0`, out of the 561 constants of the 14 new modules. This count
    includes even realized auxiliary names.
  * Importing two modules fails exactly when they store the same non-realizable constant name, so this is the exact
    criterion behind "the file elaborates".
* **The file itself does not elaborate on main, independently of this branch** (VERIFIED, `allcontrib-compile.txt`):
  `import ZInQKernel.HDecomp.Textbook.Different failed, environment already contains
  'PkgI6.TraceContainsRamificationIdx' from ZInQKernel.Contrib.Different.Local`.
  * The same scan lists 103 pre-existing clashes among main's own modules (after dropping realized `eq_*` /
    `congr_simp` names). The main ones:
    * `TDifferent.*` / `PkgI6.*` between `HDecomp.Textbook.Different` and `Contrib.Different.Local`;
    * three `ZInQ.GZWeil.*` between `GrossZagierHeegner.WeilJacobi` and `GrossZagierHeegner.JacobiLambdaDeriv`;
    * an auto-named instance repeated across the `CloudW07JacobiansCurves` modules;
    * `ZInQ.Contrib.HP23Proof.instFactPrimeValNat_zInQKernel_1` in two `HP23Proof` case files;
    * auto-generated `hcongr_*` names in Mathlib/Batteries (harmless).
  * These are for main's maintainers, not for this fold.
* Every one of the 247 imported modules builds: `lake build` on all of them gives `Build completed successfully
  (14352 jobs)` (`build3.log`).

## 4. Step 3: the bypass regenerated against main's top

eichler-bound's generator no longer fits main, for three reasons:
* the chain now runs through fold33-copy's GM copies, homfree-noemb's `_hf` chain and fold33-pic's `_pz` copies;
* the top takes three bundles, not four;
* the live consumer of the count is a different theorem.

So the bypass is regenerated with the taint-driven copy tooling of fold33-copy and fold33-pic (copylib), adapted:

1. **`scratch/eichler-rebase/Taint.lean`** (imports TailZ55; output `taint_out.txt`, VERIFIED).
   * The closure of `sixContactMin_of_open48` has 242333 constants.
   * The tainted fields are `gonzalezRotgerProp56X6`, `gonzalezRotgerCountX6Ab` (computed from it in
     `openResearchLeaves16_of_OpenResearchLeaves17_gm`), `gonzalezRotgerCountX6` (in
     `researchLeaves9_of_open14_hf_gm_pz`) and `r5count` (in `researchLeaves8_of_open9_hf`).
   * There are 23 carrier structures, each with exactly one tainted field: `OpenResearchLeaves14GM`–`29GM`,
     `OpenResearchLeaves31`, `OpenResearchLeaves2`, `5`, `7`, `8`, `9` and `ResearchLeaves3`.
   * 80 constants are tainted by value; 601 more have a carrier in their type.
2. **The live consumer.** On main the count is consumed only by `gluePieces_of_open4_hf_pz` (PicZeroCharZeroCopy),
   through homfree-noemb's `FS5NoCM.fibreComTrivialFull_of_leaves_hf''`, whose argument is
   `t6 : HomFreeC.HomFreeFiniteC`. TailK's `fibreComTrivialFull_of_leaves''`, which eichler-bound patched, is no
   longer on the live path. Its `R5fpCountLe` analogue is one line of new glue, emitted in the generated module:
   ```lean
   theorem HDec.FS5NoCM.fibreComTrivialFull_of_leaves_hf''_le (hL : R1R2fpFull) (hM : LeafQM.AV.Pin.MobiusGlue)
       (hYu : QMLattice.YuB6Alg) (t6 : _root_.ZInQ.Contrib.OneProof.HomFreeC.HomFreeFiniteC) (hE : CMOptimalEmbedding)
       (hK : X6KummerFibre) (hC : _root_.GR56.R5fpCountLe) : FibreComTrivialFull :=
     fibreComTrivialFull_of_le hL hM (comIntOrQuadOrder_of_leaves_hf hYu t6) (cmConductorCoprime6_of hE) hK hC
   ```
   It uses gr56-prove's `fibreComTrivialFull_of_le`.
3. **`scratch/eichler-rebase/gen/gen.py`** copies the 104 source declarations of the taint list verbatim, up to the
   renaming `x ↦ x_eb` / `X ↦ XEB`. It makes these edits:
   * in each of the 23 carriers, the tainted field (with its docstring) becomes `r5le : GR56.R5fpCountLe`;
   * each of the 22 assignments of a tainted field becomes `r5le := v.r5le`;
   * the consumer becomes `fibreComTrivialFull_of_leaves_hf''_le … r.r5le`.

   It then adds:
   * `OpenResearchLeaves32`;
   * `openResearchLeaves31EB_of_OpenResearchLeaves32 (n) (t : OpenTextbookLeaves16)`, with
     `r5le := EichlerBound.r5fpCountLe_proof uniformizationLeafAll_proof t.gagaMorphism t.mumfordTorsionAlgClosed`;
   * `sixContactMin_of_open49 (r : OpenResearchLeaves32) (t : OpenTextbookLeaves16) (l : OpenAddedLeaves25)`;
   * `frozenTarget_E`.

   It asserts that, comments aside, no read of a tainted field is left. A check confirms 0 code occurrences of the
   four fields and of `EichlerOptEmbCount6`. The originals are unchanged.
4. `lake env lean scratch/eichler-rebase/BypassFold.lean` (3452 lines) compiles with no errors, and the axioms are
   standard (§1).

## 5. `#discharges` (VERIFIED, `scratch/eichler-rebase/discharges.txt`)

`#discharges: 35 open hypotheses, 10261 theorems checked, 36 discharge one`.

None of these discharges comes from this task, because `R5fpCountLe` is strictly weaker than
`gonzalezRotgerProp56X6`. The field is removed by the bypass, not filled. The four `gonzalezRotgerProp56X6`
discharges come from imported modules:
* GR56's `_of_leaves`, `_of_main` and `_of_st`, all three with the leaf `EichlerOptEmbCount6`;
* `GRCountX6.prop56X6_of_r5fpCount`, which assumes `R5fpCount`.

`#print axioms`: `EichlerBound.eichlerOptEmbBound6` and `EichlerBound.r5fpCountLe_proof` use
`[propext, Classical.choice, Quot.sound]`.

## 6. Autofold spec and leaf rating

* `scratch/eichler-rebase/autofold.json` is a **count-only** spec for the field `gonzalezRotgerProp56X6` with no
  leaves. A weaker statement cannot fill the old field, so its proof text names the bypass. It is for the count
  (§1), not for `autofold.py` without `--dry-run`.
* **New leaves: none**, so nothing needs a printed-form rating. `eichlerOptEmbBound6` is a theorem. It is the upper
  half of Eichler's count of optimal embeddings for the maximal order of `(2, −3 | ℚ)`, never stronger; the printed
  form of the full count is Voight, *Quaternion Algebras*, Thm 30.4.7 (UNVERIFIED). The one new glue lemma
  (`fibreComTrivialFull_of_leaves_hf''_le`, §4) is proved.

## 7. Fold recipe for the integrator

This is a copy reroute in the style of fold33-pic. No existing declaration changes.

1. Merge wip/eichler-rebase. It brings `Contrib/OneProof/{R5fpCountLe, GR56Lattice, GRDict}.lean` and
   `Contrib/OneProof/EichlerBound/`. GRDict is optional for this fold.
2. Regenerate against the top that is current at fold time:
   * `lake env lean scratch/eichler-rebase/Taint.lean > T.txt`, after changing its import and the root
     `sixContactMin_of_open48` if the top has moved;
   * `python3 scratch/eichler-rebase/gen/gen.py T.txt OUT.lean DIR`. This writes the single-file check `OUT.lean` and,
     in `DIR`, the two modules `EichlerBoundCopy.lean.txt` (header `import <top TailZ>` plus GR56Lattice and
     R5fpCountLe; the copies and the `_hf''_le` glue) and `TailZ<k+1>.lean.txt` (`OpenResearchLeaves32`, the map,
     `sixContactMin_of_open49`).
   * The versions for TailZ55 are in `scratch/eichler-rebase/fold/`.
   * The generator reads the top, the bundles and the next numbers from Main.lean.
3. Install them as `ZInQKernel/OneProof/H/EichlerBoundCopy.lean` and `H/TailZ56.lean`. Then patch Main as
   `frozenTarget_E` does:
   * `import …TailZ56`;
   * `r : HDec.HSyn.OpenResearchLeaves32`;
   * `HDec.HSyn.sixContactMin_of_open49 r t l`.
4. Remove the `gonzalezRotgerProp56X6` row from `docs/one-proof/kinds.tsv` (research, GLUE/GLUE) and from `claims.tsv`.
   Re-render OPEN.md. The expected count is 11/17 on 28 for H.
5. Run the usual checks: `lake build +ZInQKernel.OneProof.Main`, standard axioms for `frozenTarget`, and
   DumpCompact/`cmp_hashes.py` (no existing constant changes except `frozenTarget`).
6. If gr-dict's reroute (`gonzalezRotgerX6Ab`) is folded too, it is independent of this one: run the two copy
   generators in sequence, the second on the first's output top.

## 8. What remains

* The fold itself is the integrator's step (§7).
* Optionally, the lower half of Eichler's count, which would give `R5fpCount` itself (eichler-bound §8). The chain
  does not need it.
