# fold34-ht log

Base wip/leaf-fold33b c0f3d085c (= origin/main; not moved). Render_open count at base: 35 open (29 H, strictest 11/18,
6 others) (leaf-fold33 log step 17).

1. Merged origin/wip/hodgetate-from-dr (7320b450) without conflicts (its merge base 5e235a40a is an ancestor of the
   base). Count unchanged (35 open): the merge adds only Contrib modules and scratch files, not imported by Main.
2. New Contrib modules (fold34-ht), separate from the fold:
   * `ZInQKernel/Contrib/OneProof/HodgeTatePairingWeil0.lean` (imports TailK): `tatePairingZl_field0`,
     `tateGSp_field0` = hodgetate-from-dr's `HodgeTatePairingWeil.lean` verbatim with T9 in the type of
     `PicZeroChar0.T09_SymmIsogenyExists0` (written out) and `[CharZero K]` added.
   * `ZInQKernel/Contrib/OneProof/HodgeTatePairingCore0.lean`: `hodgeTateDecompAbVar_of_leaves0` = Core verbatim with the
     characteristic-0 T9 (F is finite over Q_p, CharZero F is derived in the proof already).
   * `ZInQKernel/Contrib/OneProof/HodgeTatePairingCharZero.lean`: `t09SymmIsogenyExists0_of_open` (from
     picRepresentableAbVar, kleimanPicZeroProper, mumfordTorsionAlgClosed via picZeroAbVar0_of_leaves with
     picLocFinType_proof and identityComponentLFT_proof, phisurj's characteristic-0 theorems) and
     `hodgeTateDecompAbVar_of_open (hHT : HodgeTateDecompExists) (hM : MumfordTorsionAlgClosed)
     (h1 : PicRepresentableAbVar) (hK : KleimanPicZeroProper) : HodgeSplit.HodgeTateDecompAbVar`.
   Build oleans copied (reflink) from ~/dzq-wt/lcal-one (byte-identical Main.lean, ZInQKernel differs only by its own
   Contrib files).
3. `lake build ZInQKernel.Contrib.OneProof.HodgeTatePairingCharZero` (12981 jobs) succeeded (VERIFIED);
   `hodgeTateDecompAbVar_of_leaves0`, `t09SymmIsogenyExists0_of_open`, `hodgeTateDecompAbVar_of_open` depend on
   [propext, Classical.choice, Quot.sound].
4. `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges` (14227 jobs) ok; `scratch/fold34-ht/Discharges.lean`
   (output `Discharges-output.txt`): `DISCHARGES [OpenResearchLeaves31.hodgeTateDecompAbVar] by
   ZInQ.Contrib.HodgeTateFromPairing.hodgeTateDecompAbVar_of_open still assumes: [HodgeTateDecompExists,
   AvSplit.MumfordTorsionAlgClosed, T09Pic.PicRepresentableAbVar, PicFix.KleimanPicZeroProper]`, standard axioms
   (VERIFIED). `#discharges: 35 open hypotheses, 9864 theorems checked, 35 discharge one`.
5. Autofold spec `scratch/fold34-ht/autofold.json` (field hodgeTateDecompAbVar; new research leaf hodgeTateDecompExists,
   kind published, flag "unread: new printed leaf (...); locator UNVERIFIED"). `--dry-run`
   (`autofold-dryrun.txt`): strict count 11/18 on 29 -> 12/17 on 29; strictest 11/18 -> 12/17 (VERIFIED).
6. Fold: `python3 scripts/one_proof/autofold.py scratch/fold34-ht/autofold.json` wrote
   `ZInQKernel/OneProof/H/TailZ56.lean` (`OpenResearchLeaves32` = `OpenResearchLeaves31` without hodgeTateDecompAbVar,
   with hodgeTateDecompExists; `sixContactMin_of_open49`), switched Main.lean, kinds.tsv (row hodgeTateDecompAbVar
   GLUE/GLUE dropped; row hodgeTateDecompExists published LEAF/LEAF, flag "unread: new printed leaf (...); locator
   UNVERIFIED", flag_class unread,unverified-locator, added); claims.tsv had no row for the field (unchanged).
   Checks (all VERIFIED):
   * `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.HodgeTatePairingCharZero
     ZInQKernel.Contrib.OneProof.HodgeTatePairing` (14235 jobs) ok; `sixContactMin_of_open49` and
     `ZInQ.OneProof.frozenTarget` depend on [propext, Classical.choice, Quot.sound]. (hodgetate-from-dr's original
     `hodgeTateDecompAbVar_of_printed` also still builds on this base; it is not used by the fold.)
   * closure (`closure_1_ht.txt`, 271666 constants): no bundle field has type HodgeTateDecompAbVar (it is in the closure
     only as the statement proved by `hodgeTateDecompAbVar_of_open`); the only checked field type is the new leaf
     `hodgeTateDecompExists`; sorryAx, MumfordPhiSurjectiveAC, PicZeroAbVar, PicZeroSmooth, PhiAmpleIsogeny,
     T09_SymmIsogenyExists, MumfordKLFiniteSectionAC, hodgeTateDecompAbVar_of_printed and earlier removed Props absent.
   * hash guard (`hashes_0_base.txt` = Main at c0f3d085 rebuilt, `hashes_1_ht.txt`, `hashdiff_1_ht.txt`): before 15751,
     after 15783, only before 0, only after 32 (all in TailZ56), changed 1 (`ZInQ.OneProof.frozenTarget` type+value).
   * `lake env lean scripts/one_proof/OpenStatements.lean`: 35 open hypotheses.
   * `render_open.py`: **35 open (29 H hypotheses, strictest 12/17, 6 others)**; `--check` ok (35 classified, 4
     generated files up to date).
   * `frontier_crosswalk.py`: 232 IDs, 25 matched; `--check` ok (hodgeTateDecompExists listed with no frontier ID).
   * `scratch/contrib-kit/DischargesTest.lean` rerun (`DischargesTest-output.txt`: 35 open, 9867 theorems, 34 discharge one).
   * `uvx --offline ... autoform check blueprint --lean-root .`: OK, 781 articles, 2343 dependencies (`autoform_1_ht.txt`).
   Count: strict 11/18 on 29 -> 12/17 on 29 (GLUE -1, LEAF +1, fields 29 -> 29); 35 open unchanged.
7. Merge hygiene: scratch/hodgetate-from-dr/AutofoldDry.lean (redeclares HDec.HSyn bundles) renamed .lean.txt (its
   report docs/research/hodgetate-from-dr.md still names the .lean path; not edited, other task's report); host path
   (~/dzq) removed from scratch/hodgetate-from-dr/log.md; no vendored LICENSE/NOTICE files in the merged branch.
