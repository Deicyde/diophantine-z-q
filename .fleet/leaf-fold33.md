# leaf-fold33: report

**Head:** 26eaa3f94 before this report. This report is the next commit on wip/leaf-fold33. Base: 6b7a4544 (lf32b).
Results log: `.fleet/leaf-fold33-log.md`.

**Result.** Three of the four contributions are folded. Two autofolds were needed:
* TailZ46, `sixContactMin_of_open39`: poincareComplement and blr_7_2_1.
* TailZ47, `sixContactMin_of_open40`, the new top: picZeroAbVar.

Main and the supplier PRs are both included. The full check passes.

**Counts:**
* H fields: 37 → 38.
* Strict: 16 LEAF / 21 GLUE → 18 / 20. The autofold output was `15/20 on 35`, then `18/20 on 38`.
* Strictest: 16/21 → 18/20, from autofold and from OpenStatements ("38 H hypotheses, strictest 18/20, 8 others").
* frozenTarget has 46 open hypotheses: 38 H fields plus 8 others.

## The four contributions

1. **poincare-proof 5795bbc01: folded.**
   * Field `poincareComplement` (textbook, was LEAF) is discharged by
     `ZInQ.Contrib.OneProof.PoincareComplement.poincareComplement_of_open`. No new leaf.
   * Spec adaptations, with lf32b's terms copied from TailZ44/45:
     * `{l}.phiAmpleIsogeny` → `_root_.PicFix.phiAmpleIsogeny_of_printed {l}.mumfordKLFiniteSectionAC {l}.mumfordPhiSurjectiveAC`
     * `{l}.milneIsogenyQuasiInverse` → `_root_.ZInQ.Contrib.MilneQuasiInverse.milneIsogenyQuasiInverse_proof`
     * `{n}.cartierSmooth` → `_root_.ZInQ.Contrib.OneProof.CartierSmooth.cartierSmooth_proof`
   * `{l}.picZeroAbVar` is still read from `OpenAddedLeaves19`. Fold b then discharges that field.
2. **neron-sh-proof 3842078af: folded.**
   * `DictModels.NeronBLR72.BLR_7_2_1` is defined as `ReductGlue.NeronBaseChangeUnramifiedDVR`
     (NeronBaseChangeBLR72.lean:43). The contribution proves `NeronSH.neronBaseChangeUnramifiedDVR_proof`.
   * The adapter `ZInQ.Contrib.OneProof.Fold33.blr_7_2_1_proof` is in
     `ZInQKernel/Contrib/OneProof/Fold33/NeronBLR.lean`. It is a one-line term proof by unfolding.
   * It discharges the research leaf `blr_7_2_1` (was GLUE, pending reading). No new leaf.
   * The spec's original discharge of `neronBaseChangeStrictHenselization` was dropped: that field is gone in lf32b.
3. **pic-smooth 2128db760: folded with `scratch/pic-smooth/autofold.json` unchanged.**
   * The README recommends that spec once CartierSmooth.lean is on the base, and it is: byte-identical, from h98.
   * Field `picZeroAbVar` (added, consequence, GLUE) is discharged by `PicSmooth.picZeroAbVar_of_printed2`, with
     4 new leaves (table below).
4. **pic-fix2 45945e9ce, fold B: skipped, not merged.**
   * Fold B is `narrow.patch` + `autofold-narrow.json` (README; report §1, §3). The patch hand-edits the existing H
     modules TailZ24, 26, 30, 31 and 34: it renames and retypes the field `phiAmpleIsogeny` as `phiVeryAmpleIsogeny`
     and rewrites `addedLeaves12_of_open13`. This task may not make those edits; the fleet note itself calls it "a
     hand fold ... needs hash-guard exceptions".
   * In lf32b `phiAmpleIsogeny` is no longer a field: TailZ45 fills it from the leaves `mumfordKLFiniteSectionAC`
     (ample, nonzero section) and `mumfordPhiSurjectiveAC` (ample).
   * Fold B's leaves, `MumfordKLFiniteDivisorAC` and `MumfordPhiSurjectiveVAC`, also assume `IsVeryAmple`. That makes
     them weaker statements, so they cannot discharge the open leaves either.

## Discharged fields and new leaves

Discharged: `poincareComplement` (textbook), `blr_7_2_1` (research), `picZeroAbVar` (added).

New leaves, all in `OpenAddedLeaves20`, with kind and flag kept from the pic-smooth spec:

| leaf | kind | strict | flag |
|---|---|---|---|
| picLocFinType | published | LEAF | unread: new printed leaf (BLR 8.2 Thm 3 / Murre-Oort for proper X over a field; Kleiman 9.4.8 for projective X, A projective by the vendored lemma; any representing object by Yoneda uniqueness); locator UNVERIFIED |
| identityComponentLFT | published | LEAF | unread: new printed leaf; locator UNVERIFIED |
| picZeroSmoothPosChar | published | GLUE | pending reading: positive-characteristic case only (char 0 proved via Cartier, cartierSmooth_proof); one print over an arbitrary field of characteristic p not located (Mumford 13 is over Kbar and about Mumford's dual, not the fppf Pic0; BLR 8.4 / FGA Explained 9.5 / Milne 1986 10 to read); locator UNVERIFIED |
| kleimanPicZeroProper | published | LEAF | unread: new printed leaf (Kleiman 9.5.4, X proper and geometrically normal over a field, every representing object); locator UNVERIFIED |

How the count moves:
* Strict LEAF: −1 for poincareComplement, +3 for the published leaves.
* GLUE: −1 for blr_7_2_1, −1 for picZeroAbVar, +1 for picZeroSmoothPosChar.

## Checks per contribution

* `lake build` of PoincareComplement, NeronBaseChangeStrictHenselization, Fold33.NeronBLR, PicZeroSmoothCartier and
  PicZeroAbVarCartier: RC=0, 12886 jobs. No "environment already contains", so no name clash.
* `#print axioms`: each of the following gives [propext, Classical.choice, Quot.sound]:
  * `poincareComplement_of_open`
  * `Fold33.blr_7_2_1_proof`
  * `NeronSH.neronBaseChangeUnramifiedDVR_proof`
  * `PicSmooth.picZeroAbVar_of_printed2`
  * `cartierSmooth_proof`

  Source: `scratch/leaf-fold33/Axioms.lean`.
* Forbidden tokens (sorry, axiom, native_decide, run_cmd, #eval, initialize, extern, implemented_by, admit): none in
  the new Lean files.
* Vendored files: none changed by the merges. pic-smooth's 68 CloudB3W16Cartier files were already on lf32b,
  byte-identical.

## The fold: one spec became two autofolds

The combined spec `scratch/leaf-fold33/autofold.json` dry-ran (16/21 on 37 → 18/20 on 38), but its module did not
compile:
* Error at TailZ46.lean:105: "Invalid field notation ... l has type OpenAddedLeaves20".
* Cause: autofold writes the textbook conversion before the added-bundle structure of the same module. The
  poincareComplement discharge reads `{l}`, so the not-yet-declared `OpenAddedLeaves20` became an auto-bound implicit.

What I did:
* Reverted that commit (3133b5813).
* Ran `autofold-a.json`: poincareComplement with `{l}.picZeroAbVar` against `OpenAddedLeaves19`, plus blr_7_2_1.
* Then ran `autofold-b.json`: picZeroAbVar.

The discharges and the end state are the same. Existing H modules and Main.lean were not edited by hand.

## Main and supplier PRs

* (a) At first, 5e235a40 was not on origin/main, so I merged it (075e3622c).
  * Its only change was main's STATUS.md wording for NVLocalInertia. I kept the branch's STATUS.md: that paragraph is
    no longer in it, so there was nothing to apply the wording to.
  * The commit message wrongly says the merge kept main's NVLocalInertia wording. In fact no hunk applied.
* During the final check, 5e235a40 landed (origin/main c1e4ed1b8), so I merged origin/main as well (d6f6d53d9, no
  conflict).
  * It adds only blueprint/ markdown and `scripts/one_proof/vault_chapter/`. No Lean, and nothing the check reads.
  * After this merge, `render_open.py --check` (RC 0) and `frontier_crosswalk.py --check` (RC 0) were rerun. The
    Lean part was not rerun, because the Lean tree is identical.
* (b) Each supplier head is an ancestor of HEAD at every check, including the last at d6f6d53d9, so nothing was
  merged:
  * origin/pr/23 0eab413df, pr/25 7c9177bd9, pr/29 fefce8ef0, pr/31 d42bb38f4
  * pr/34 4fa17fc59, pr/35 37a970528, pr/36 47ca4df21, pr/38 a9bc2e35c

## Final check (the check log lf33.log, run on e34ff390e)

```
BUILD-RC=0
info: ZInQKernel/OneProof/Main.lean:91:0: 'ZInQ.OneProof.frozenTarget' depends on axioms: [propext, Classical.choice, Quot.sound]
PRUNE-RC=0
PRUNE bundle HDec.HSyn.OpenAddedLeaves20: 8 fields, unused 0: []
PRUNE total unused top-level fields: 0
PRUNE bundles with unused fields: 50
PRUNE prune set: 0 entries
HASH lf16 14038 lf17 14099 gone [] new 61 changed ['ZInQ.OneProof.frozenTarget']
#discharges: 46 open hypotheses, 6810 theorems checked, 12 discharge one
wrote docs/one-proof/open-statements.json: 46 open hypotheses
38 H hypotheses, strictest 18/20, 8 others
ok: 46 open hypotheses, all classified; 4 generated files up to date
CHECK-RC=0
wrote docs/one-proof/frontier-crosswalk.tsv: 232 IDs, 33 matched to an open hypothesis
ok: docs/one-proof/frontier-crosswalk.tsv is up to date (232 IDs, 33 matched)
XWALK-RC=0
```

Notes on the log:
* "PRUNE bundles with unused fields: 50" lists the superseded inner bundles of older tail modules. The prune set is
  empty.
* The hash labels lf16/lf17 are the script's names for lf32b and lf33.
* The first run, on the reverted single-spec fold, had BUILD-RC=1 (see the log). Its docs were not committed.

## For the lead

* **Re-rate the 4 new leaves.**
  * `picLocFinType` ("any representing object by Yoneda") and `kleimanPicZeroProper` ("every representing object")
    are stated for every scheme that represents Pic. If you read that as use form, they enter as consequence (GLUE)
    and the strict count becomes 16/22.
  * `picZeroSmoothPosChar` is already GLUE (pending reading).
  * None of the four has a frontier ID yet. The crosswalk lists them among open hypotheses with no frontier ID.
* **pic-fix2 fold B** can only land as a hand fold of TailZ24/26/30/31/34 with hash-guard exceptions. Even then it
  would need re-deriving against lf32b, where phiAmpleIsogeny has already been replaced by two weaker-hypothesis leaves.
* **Autofold limitation.** A spec that discharges a field from `{l}` and also changes the added bundle in the same
  fold emits an ill-ordered module. The dry run does not catch it. It needs either a fix in autofold.py or split specs.
* **The check script's own commit messages are stale.**
  * 89cd291e1 says "(hS replaced by hCM and hX)".
  * e77ac61a8 says "leaf-fold28".
  * Both are fixed strings in lf33-check.sh, not descriptions of this fold.
