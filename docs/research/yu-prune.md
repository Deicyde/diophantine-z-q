# yu-prune: `yuThm11` (Yu 2013 Thm 1.1) removed from `ZInQ.OneProof.frozenTarget`

Task yu-prune, 2026-11-15. Base 688b450d (fork main plus leaf-fold14 to leaf-fold19; `frozenTarget` through
`HDec.HSyn.sixContactMin_of_open26`, 58 bundle fields). I merged origin/wip/leaf-fold19 at c2ad4181 because the base
does not build at TailZ32 (§5). The finding this task applies is docs/research/gt-qm.md §5 (`scratch/gt-qm/Reach.lean`,
`Reroute.lean`). Results log: scratch/yu-prune/log.md. Model work, no human review.

Marks: **VERIFIED** = compiled, or read in a named file on this host; **STANDARD** = textbook mathematics;
**SPECULATIVE** = judgement.

## 1. Main result

**`frozenTarget` loses `OpenTextbookLeaves11.yuThm11 : HDec.QMSplit.Yu.YuThm11` and gains nothing.** This is VERIFIED:
* `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` succeeds;
* `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`;
* PruneScan finds 0 unused fields among the remaining 57.

| | H fields | strict (kinds.tsv, H rows) | strictest | all rows of kinds.tsv (with the 7 `frozenTarget` Props) |
|---|---|---|---|---|
| before (688b450d / c2ad4181) | 58 | 45 LEAF / 13 GLUE | 44 / 14 | strict 48 / 17, strictest 47 / 18 |
| after | **57** | **44 / 13** | **43 / 14** | strict 47 / 17, strictest 46 / 18 |

`yuThm11` was LEAF in both readings, so only the LEAF counts drop. No other field became unused: the scan after the
prune reports 0. claims.tsv had no row for `yuThm11`, so it is unchanged.

**Why the field was not needed** (VERIFIED by the compiled plumbing). The chain used Yu's theorem only through
`PkgI3.QMDichotomyYu` (T27), and only at four application sites. All four are at `B = (2, −3)`, with the embedding
`B → End⁰(A)` of a QM structure by the maximal order `𝒪`, over `AlgebraicClosure ℚ` or `AlgebraicClosure L'` with
`L'` finite over `ℚ`. That special case is `HDec.QMLattice.YuB6Alg` (gt-qm). It is a theorem of the chain:
`HDec.QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`, from three textbook
fields the bundle keeps and from T11(b), which the chain proves. `YuB6Alg` is never stronger than the published
statement (`yuB6Alg_of_yuThm11 : YuThm11 → YuB6Alg`, unchanged). The step "End⁰ of a QM fibre is `B` or
`M₂(ℚ(√d))`" (G5 / FS4 / N1a / QMEndRank) therefore rests on the complex-lattice argument of gt-qm and not on Yu's
paper.

### 1.1 The plumbing (step 1, compiled before any deletion; scratch/yu-prune/plumb.py)

The rule followed: a signature changes only by replacing a `PkgI3.QMDichotomyYu` argument with a
`HDec.QMLattice.YuB6Alg` argument. That is a weaker hypothesis: `QMDichotomyYu` implies `YuB6Alg` by taking
`(a, b) = (2, −3)` and `qm_embeds_end0`. The other allowed change adds a `YuB6Alg` argument to a theorem that read
a bundle's `t27`. No field statement changes. `frozenTarget`'s statement changes only by the deleted field.

* **The definition moves.** `HDec.QMLattice.YuB6Alg` (a `def … : Prop`) moves verbatim from
  `ZInQKernel/Contrib/OneProof/QMLattice.lean` to `ZInQKernel/OneProof/H/TailA.lean`, into `namespace QMLattice`
  just before `namespace G0FibreSimple`. QMLattice imports TailZ26, so the consumers in TailA–TailK could not import
  it. Its type and value hashes are unchanged (§4). QMLattice keeps every theorem, including `yuB6Alg_of`,
  `yuB6Alg_of'`, `yuB6Alg_of_yuThm11`, `YuB6Emb` and `isAlgebraic_algebraicClosure`. It now says in a comment where
  the definition lives.
* **The four application theorems** take `hYu : QMLattice.YuB6Alg` in place of T27. Each one's application line is
  `hYu k A hA q`, as in `scratch/gt-qm/Reroute.lean`:
  * `FS5NoCM.comIntOrQuadOrder_of` (TailC);
  * `G0ModField.KernelField.endEqOFibre_of` (TailC);
  * `G0FibreSimple.fibreSimple_of_pieces` (TailA);
  * `LTGoodRed.QM.qmEndRank_of` (TailF). This one also needs `Algebra.IsAlgebraic ℚ (AlgebraicClosure L')`, which is
    proved inline: `L'` is finite over `ℚ`, so it is algebraic, and algebraicity is transitive. It is the same
    argument as gt-qm's `isAlgebraic_algebraicClosure`.
* **Carriers** (binder type only; the binder is renamed `hYu`):
  * TailA: `fibreSimple_of_pieces'`, `fibreSimple_of_pieces''`;
  * TailC: `fibreComTrivialFull_of_leaves`, `comIntOrQuadOrder_of_leaves`, `fibreComTrivialFull_of_leaves'`,
    `fibreComTrivialFull_of_leaves''`, `kernelFieldExists_of_split''`, `kernelFieldExists_of_final`,
    `kernelFieldExists_of_final'`, `kernelFieldExists_of_rigidity`;
  * TailF: `kernelFieldExists_of_five`, `_of_semilinear`, `_of_twist`, `_of_descent`, `_of_kerUnitOpen`,
    `_of_kerUnitOpen'`, `_of_mulIsogeny`, `qmEndRank_of_leaves`;
  * TailI: `qmEndRank_of_leaves3`, `linkedTateLocal_of_leaves3`.
* **Readers of a bundle's `t27`.**
  * `G0FibreSimple.fibreSimple_of_leaves` (TailA) takes `hYu` after `t` instead of reading `t.t27`.
  * `HSyn.gluePieces_of_open4` (TailK) takes `hYu` and passes it at its three uses and to `fibreSimple_of_leaves`.
  * The off-chain readers (`gluePieces_of_open2`, `_open3`, `gluePieces_of_gluePieces3`, `fibreComTrivial_of_gp3`,
    `fibreSimple_of_gp3`) used a temporary bridge, `G0FibreSimple.yuB6Alg_of_qmDichotomyYu t.t27`, during step 1.
    Step 2 deletes them and the bridge.
* **Threading.** `sixContactMin_of_open4`, `_open6`–`_open23` take `(hYu : QMLattice.YuB6Alg)` as their last
  binder and pass it down. This includes the off-chain `_open12`–`_open16`, which call `_open11`.
  `sixContactMin_of_open24` (TailZ30, the first module after QMLattice) supplies
  `QMLattice.yuB6Alg_of' t.uniformizationLeafAll t.gagaMorphism t.mumfordTorsionAlgClosed`. `_open25`, `_open26` and
  `frozenTarget` are unchanged in step 1. The `example` after `_open6` (TailO) states the new binder.

After step 1, PruneScan (rooted at `sixContactMin_of_open25`, because Main did not build yet, §5) reports exactly
`OpenTextbookLeaves10.yuThm11` UNUSED. The prune set has 9 fields: `TextbookLeaves.t27`,
`OpenTextbookLeaves2/3/4/6.t27` and `OpenTextbookLeaves7/8/9/10.yuThm11`. It contains no constants
(scratch/yu-prune/prune-set-step1.txt).

### 1.2 The prune (step 2; scratch/yu-prune/prune_edit.py, every deleted line in prune_edit_out.txt)

Deleted:
* 10 fields: the scan's 9, plus `OpenTextbookLeaves11.yuThm11` (TailZ32, the top textbook bundle, which the
  open25-rooted scan could not see);
* the 11 assignments into them:
  * `textbookLeaves_of_open` (LPrefix);
  * `textbookLeaves_of_open2` (TailE);
  * `textbookLeaves2_of_open3` (TailI);
  * `textbookLeaves3_of_open4` (TailK);
  * `textbookLeaves4_of_open5` (TailN, off the chain: it set `OpenTextbookLeaves4.t27` from `OpenTextbookLeaves5.t27`);
  * `textbookLeaves4_of_open6` (TailO);
  * `textbookLeaves6_of_open7` (TailX, `t27 := qmDichotomyYu_of_yu t.yuThm11`);
  * `textbookLeaves7_of_open8`, `textbookLeaves8_of_open9`, `textbookLeaves9_of_open10`;
  * `openTextbookLeaves10_of_OpenTextbookLeaves11` (TailZ32);
* the 5 dead readers of DeadCascade (scratch/yu-prune/dead-cascade.txt, generated `casesOn`/`recOn` excluded), with
  their `#print axioms` lines: `fibreComTrivial_of_gp3`, `fibreSimple_of_gp3`, `gluePieces_of_gluePieces3` (TailD),
  `gluePieces_of_open2` (TailE), `gluePieces_of_open3` (TailI). All five were off the chain;
* the step-1 bridge `G0FibreSimple.yuB6Alg_of_qmDichotomyYu`, which lost every user.

Kept:
* Older generations off the chain keep their T27 fields, as in earlier prunes: `OpenTextbookLeaves.t27` (LPrefix)
  and `OpenTextbookLeaves5.t27` (TailN).
* The general theorems `QMSplit.Yu.qmDichotomyYu_of_yu`, `HSyn.qmDichotomyYu_ofK5` and `PkgI3.qmDichotomy_B6` are
  still declared. They are now off the closure.

## 2. Every hypothesis after the prune

The full statements are in docs/one-proof/OPEN.md (regenerated) and the kinds in docs/one-proof/kinds.tsv.

* **OpenResearchLeaves19** (30 fields), **OpenAddedLeaves16** (14) and **OpenGlue7** (1): unchanged.
* **OpenTextbookLeaves11** (12 fields, all `published`, LEAF/LEAF): `cartierSmooth`,
  `charPolyIndepOfEllAlgClosed`, `gagaMorphism`, `geomConnOfRationalPoint`, `groupSchemeEquidim`,
  `homFreeFiniteAlgClosed`, `igusaGL2`, `mumfordTorsionAlgClosed`, `neronSchemeExtensionExists`,
  `poincareComplement`, `regularSmoothPerfect`, `uniformizationLeafAll`.
* The 7 non-bundle hypotheses of `frozenTarget` (`h11`, `h29`, `hCM`, `hX`, `h33`, `hL2`, `hL3`): unchanged.

## 3. The remaining leaves by the theory they come from

Unchanged from leaf-fold19, except the group "abelian varieties with QM / quaternion algebras": it loses Yu's
Theorem 1.1. The QM dichotomy at `(2, −3)` now follows from three other leaves:
* the analytic uniformization of abelian surfaces over `ℂ` (`uniformizationLeafAll`);
* GAGA for morphisms (`gagaMorphism`);
* Mumford's torsion count over an algebraically closed field (`mumfordTorsionAlgClosed`).

All three were already leaves. The complex-lattice computation of gt-qm (QMLattice.lean §5–§7) does the rest
(STANDARD mathematics, VERIFIED in Lean).

## 4. Checks (all VERIFIED; one Lean process at a time)

* **Base (c2ad4181, separate worktree):** `lake build +ZInQKernel.OneProof.Main` OK; DumpCompact found 13761
  constants (OneProof modules plus QMLattice; scratch/yu-prune/hashes_before.txt); PruneScan found 0 unused of 58
  (prunescan-base-main.txt). On 688b450d itself, `sixContactMin_of_open25` was checked instead (hashes_before31.txt,
  13599 constants; PruneScan31 0 unused of 59).
* **After step 1 (plumbing):** `lake build ZInQKernel.OneProof.H.TailZ31` OK, with no error on the first try.
  PruneScan31 then reported exactly `yuThm11` unused (§1.1).
* **After step 2 (prune):**
  * `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` OK (12979 jobs);
  * `#print axioms ZInQ.OneProof.frozenTarget` gives `[propext, Classical.choice, Quot.sound]`;
  * the type of `frozenTarget` prints identically before and after (frozenTarget_before.txt, frozenTarget_after.txt);
    only `OpenTextbookLeaves11` has a field fewer.
* **PruneScan (rooted at `frozenTarget`):** OpenResearchLeaves19 30, OpenTextbookLeaves11 12, OpenAddedLeaves16 14,
  OpenGlue7 1 = 57 fields, 0 unused, prune set empty (used-fields.txt, prune-set.txt).
* **DumpCompact + cmp_hashes.py** (cmp_hashes_out.txt; classify.py → classify_out.txt): base 13761, after 13746.
  * **Removed 17:**
    * the 10 pruned fields' projections;
    * the 5 dead readers;
    * `G0FibreSimple.qmBasis._proof_8` and `G0Galois.G7Out._proof_3`. These are auxiliary-proof renumberings,
      explained below.
  * **New 2:** `HDec.QMLattice.YuB6Emb._proof_1/_proof_2`. Before the move, `YuB6Emb` reused `YuB6Alg`'s auxiliary
    proofs in the same module. Their hashes equal those of `YuB6Alg._proof_1/2`.
  * **Changed 198:**
    * 100 generated auxiliaries and projections (`mk`, `rec`, `casesOn`, …, field projections shifted by the deleted
      field) of the 10 edited bundle structures `TextbookLeaves` and `OpenTextbookLeaves2/3/4/6/7/8/9/10/11`.
    * 11 conversions, each changed in value by one deleted assignment: `textbookLeaves_of_open`,
      `textbookLeaves_of_open2`, `textbookLeaves2_of_open3`, `textbookLeaves3_of_open4`, `textbookLeaves4_of_open5`,
      `textbookLeaves4_of_open6`, `textbookLeaves6_of_open7`, `textbookLeaves7_of_open8`, `textbookLeaves8_of_open9`,
      `textbookLeaves9_of_open10`, `openTextbookLeaves10_of_OpenTextbookLeaves11`.
    * 20 stack theorems:
      * `sixContactMin_of_open4`, `_open6`–`_open23`: the type changed (the new binder `hYu`);
      * `sixContactMin_of_open24`: the value changed (it supplies `yuB6Alg_of'`);
      * `_open25`, `_open26` and `frozenTarget` have unchanged hashes.
    * 26 edited consumers, all with a changed type (the `YuB6Alg` binder):
      * FS5NoCM: `comIntOrQuadOrder_of`, `comIntOrQuadOrder_of_leaves`, `fibreComTrivialFull_of_leaves`, `'`, `''`;
      * G0FibreSimple: `fibreSimple_of_leaves`, `fibreSimple_of_pieces`, `'`, `''`;
      * KernelField: `endEqOFibre_of`, and `kernelFieldExists_of_split''`, `_final`, `_final'`, `_rigidity`, `_five`,
        `_semilinear`, `_twist`, `_descent`, `_kerUnitOpen`, `_kerUnitOpen'`, `_mulIsogeny`;
      * HSyn: `gluePieces_of_open4`, `linkedTateLocal_of_leaves3`, `qmEndRank_of_leaves3`;
      * LTGoodRed.QM: `qmEndRank_of`, `qmEndRank_of_leaves`.
    * 6 in QMLattice:
      * `YuB6Alg`, `YuB6Alg._proof_1/2`: the same type hash and value hash; only the module changed;
      * `YuB6Emb`, `yuB6Emb_of`, `yuB6Emb_of_yuThm11`: value only, through the auxiliary proofs above.
      * `yuB6Alg_of`, `yuB6Alg_of'` and `yuB6Alg_of_yuThm11` are unchanged.
    * 35 others in TailA, TailB, TailC, TailF and TailH, examples being `qmBasis`, `G9Glue`, `G7Out`, `g8_g12` and
      `tateBridge_of_pieces`, together with their `_proof_N`. All are value-only, except the `_proof_N` themselves.
      The cause is that Lean shares an identical auxiliary proof within a module. `YuB6Alg` (now earlier in TailA)
      creates `YuB6Alg._proof_1/2`. The later `qmBasis._proof_1` and `G7Out._proof_1` are the same statements, so they
      now point to those, and the remaining `_proof_N` renumber down by one.
      **VERIFIED by scratch/yu-prune/CanonHash.lean**, run in both trees. It hashes the type and value of each of the
      41 "other" and QMLattice constants after replacing every `_proof_N`, recursively, by the canonical hash of its
      statement. All 41 are equal except the `_proof_N` constants themselves, whose canonical hashes are the old ones
      shifted by one: new `qmBasis._proof_k` equals old `_proof_(k+1)`, old `qmBasis._proof_1` equals
      `YuB6Alg._proof_2`, and old `G7Out._proof_1` equals `YuB6Alg._proof_1`
      (canon-hashes-before.txt, canon-hashes-after.txt).
  * No other constant changed.
* **scratch/contrib-kit/DischargesTest.lean** (output in DischargesTest-output.txt): the same five discharges and
  controls as before (t1 still assumes `QuotientP1Coordinate`; t3 on `cartierSmooth` is flagged for `sorry`).
  The count is now 64 open hypotheses (was 65).
* **Docs:** `lake env lean scripts/one_proof/OpenStatements.lean` wrote 64 open hypotheses.
  `render_open.py` reported "57 H hypotheses, strictest 43/14, 7 others", and `render_open.py --check` reported "ok".
  `open-statements.json`, OPEN.md, CONTRIBUTING.md and STATUS.md were regenerated; pages-wanted.md is unchanged by
  the generator (no Yu entry).

## 5. Not done, and why

* **The base did not build at TailZ32** (VERIFIED, 688b450d). PR #19's vendored `StacksCore/Tactic` attribute
  modules duplicated `CloudW01Spread`'s ("environment already contains `Stacks.EgaSga.instInhabitedWork.default`").
  The leaf-fold19 integrator fixed this in 495ca918, and I merged origin/wip/leaf-fold19 (c2ad4181). The merge
  changes no OneProof/H module. Until the merge, the checks were rooted at `sixContactMin_of_open25`
  (scratch/yu-prune/*31.lean).
* FaithCheck: not needed (no HDec copy was replaced by a kernel declaration).
* `OpenTextbookLeaves.t27`, `OpenTextbookLeaves5.t27` (older generations off the chain) are kept (§1.2).
* docs/one-proof/frontier-crosswalk.tsv still has a row `H-128 yuThm11` (not a file this task may edit; its owner
  should mark the row closed by yu-prune).

## 6. `frozenTarget`: removed and added hypotheses

* **Removed:** `OpenTextbookLeaves11.yuThm11 : HDec.QMSplit.Yu.YuThm11`. This is Chia-Fu Yu, J. Pure Appl. Algebra
  217 (2013), Thm 1.1, with its splitting clause and with the case labels dropped. It was LEAF in both readings.
* **Added:** none. `frozenTarget` has the same four bundle binders and seven `Prop` binders; `OpenTextbookLeaves11`
  has one field fewer (12).
