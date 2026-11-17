# fold33-review log

Base: wip/leaf-fold33b 667e0aed (origin/main already included, VERIFIED by git merge-base).

## 1. Closure and hypothesis list (scratch/fold33-review/Closure.lean -> Closure-output.txt, open-statements.json)

Build tree: copied (cp -a) from the leaf-fold33b worktree at the same commit 667e0aed (.lake/build and lean/.lake).
`lake env lean scratch/fold33-review/Closure.lean`: 2 min 16 s, no errors (VERIFIED).

- `#print axioms ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound] (VERIFIED).
- 37 open hypotheses (31 H bundle fields + 6 others), identical (field name and full type string) to the lead's
  committed docs/one-proof/open-statements.json at 667e0aed (VERIFIED, python compare).
- Against the list at 3e66542b6 (step 7, before the homfree reroute; 44 hypotheses): removed hP23, hQ, hW, hfx,
  homFreeFiniteAlgClosed, mumfordGroupLawConn, neronSchemeExtensionExists, sga3_VIB_3_10_Nbhd; added only
  neronSchemeExtensionDedekind; type changed only hCM (ShimuraMainCM -> HCMDict.ShimuraThm54). Every other field has
  the same full type string (VERIFIED).
- Constant closure of frozenTarget (through definitions and theorem proofs): 271096 constants. Names matching
  SGA3_VIB_3_10 / MumfordGroupLawConn / GZDecomp.GrossZagierHeegner: none (VERIFIED). Matches present, all derived
  or proved: T5Glue.ShimuraMainCM (derived by shimuraMainCM_of_printed), NeronC.NeronSchemeExtensionExists (derived
  by neronSchemeExtensionExists_of_dedekind), GZOptimal.GrossZagierModuliOptAt/Cd and
  GZStatements.GrossZagierHeegnerCd (derived from hGZ), HomFreeC.HomFreeFiniteC / homFreeFiniteC (proved), the
  projections OpenTextbookLeaves{6..13}HF.homFreeFiniteAlgClosed (field type HomFreeC.HomFreeFiniteC, the proved
  C-form, HomFreeFiniteAlgClosedReroute.lean:729, :2018), and AVB1.HomFreeFiniteAlgClosed._proof_4 (an auxiliary
  proof term, see below).
- Statement closure (types through definitions only) of each open hypothesis: no removed Prop reached; the only hit
  is AVB1.HomFreeFiniteAlgClosed._proof_4 under charPolyIndepOfEllAlgClosed (auxiliary proof shared by the
  elaborator, checked in step 2).
