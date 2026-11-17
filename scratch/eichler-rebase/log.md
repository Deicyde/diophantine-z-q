# eichler-rebase log

## Setup
* Merged origin/main c0f3d085 into wip/eichler-bound 09896d1f: no conflicts (commit 261ebb16). VERIFIED.
* Modules main lacks (git diff origin/main HEAD -- ZInQKernel): R5fpCountLe.lean, EichlerBound/{Order,Quadratic,Defs,
  Embed,Unit,Crit,Key,Key6,Inv,Count,Bound}.lean, GR56Lattice.lean (gr56-prove), GRDict.lean (gr-dict; not imported
  by R5fpCountLe). VERIFIED.
* Build tree seeded from ~/dzq-v-hfx-proof (TailZ42 base) by reflink copy; lake rebuilds the rest.

## Count (step 4)
* `autofold.py scratch/eichler-rebase/autofold.json --dry-run` (count-only spec, no new leaf) on main's kinds.tsv:
  `strict count: 11/18 on 29 -> 11/17 on 28; strictest 11/18 -> 11/17`. VERIFIED (autofold-dryrun.txt). The
  dry-run module itself is not a fold (dummy proof text): the field is removed by the bypass, not filled.

## Step 1: build on the merged tree
* `lake build ZInQKernel.Contrib.OneProof.R5fpCountLe` on the merged tree: Build completed successfully (12948 jobs),
  EXIT 0, no edits needed (EichlerBound/{Order..Bound}, GR56Lattice, R5fpCountLe all built). VERIFIED (build1.log).

## Step 3: bypass regenerated on main's top (open48, TailZ55)
* `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.GRDict`: OK (14229
  jobs); `ZInQ.OneProof.frozenTarget` standard axioms. VERIFIED (build2.log).
* `Taint.lean` (lake env lean, 3 min): closure of `sixContactMin_of_open48` 242333 constants; tainted fields
  `gonzalezRotgerProp56X6, gonzalezRotgerCountX6Ab, r5count, gonzalezRotgerCountX6`; 23 carriers
  (OpenResearchLeaves14GM..29GM, 31, 2, 5, 7, 8, 9, ResearchLeaves3), no carrier with two tainted fields; 80 value-
  tainted constants (T), 601 type-carrier constants (S, mostly projections). VERIFIED (taint_out.txt). (Part 1 of
  Taint.lean strips `let`, so it lists no TERM consumer; the T list shows the only live consumer:
  `gluePieces_of_open4_hf_pz` (PicZeroCharZeroCopy) through `FS5NoCM.fibreComTrivialFull_of_leaves_hf''`.)
* Finding: on main the live consumer of `r5count` is homfree-noemb's `fibreComTrivialFull_of_leaves_hf''`
  (`t6 : HomFreeC.HomFreeFiniteC`), not TailK's `fibreComTrivialFull_of_leaves''` (eichler-bound's generator
  patched the latter). New 1-line glue `HDec.FS5NoCM.fibreComTrivialFull_of_leaves_hf''_le` (in the generated file):
  `fibreComTrivialFull_of_le hL hM (comIntOrQuadOrder_of_leaves_hf hYu t6) (cmConductorCoprime6_of hE) hK hC`.
* `gen/gen.py` (fold33-pic copylib): 104 blocks copied (`_eb`/`EB`): 23 carrier structs (field -> `r5le`),
  22 assignments -> `r5le := _.r5le`, 1 consumer -> `_hf''_le`; top `OpenResearchLeaves32` (= 31 minus
  `gonzalezRotgerProp56X6`, no new field), `openResearchLeaves31EB_of_OpenResearchLeaves32` (r5le :=
  `EichlerBound.r5fpCountLe_proof uniformizationLeafAll_proof t.gagaMorphism t.mumfordTorsionAlgClosed`),
  `sixContactMin_of_open49`, `ZInQ.Contrib.TYZChain.frozenTarget_E`. Code (comments stripped) mentions none of the four
  tainted fields nor `EichlerOptEmbCount6`. 3452 lines.
* `lake env lean scratch/eichler-rebase/BypassFold.lean`: compiles, EXIT 0, no errors. VERIFIED (bypass-compile.txt):
  'HDec.HSyn.sixContactMin_of_open49' depends on axioms: [propext, Classical.choice, Quot.sound]
  'ZInQ.Contrib.TYZChain.frozenTarget_E' depends on axioms: [propext, Classical.choice, Quot.sound]
