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
