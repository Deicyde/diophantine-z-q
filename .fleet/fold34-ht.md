# fold34-ht — fleet summary

**Result: `hodgeTateDecompAbVar` (GLUE) is folded. Strict and strictest go 11/18 → 12/17 on 29 fields; 35 open
(29 H, 6 others).** I merged wip/hodgetate-from-dr (7320b450). Its proof read leaf-fold32b's T9 leaves, which this base
has proved or removed, so I added three Contrib modules. `HodgeTatePairingWeil0`/`Core0` are verbatim copies with
T9 in characteristic 0 (`T09_SymmIsogenyExists0`; the base field is finite over ℚ_p).
`HodgeTatePairingCharZero.hodgeTateDecompAbVar_of_open : HodgeTateDecompExists → MumfordTorsionAlgClosed →
PicRepresentableAbVar → KleimanPicZeroProper → HodgeSplit.HodgeTateDecompAbVar` uses the proved PicLocFinType and
IdentityComponentLFT, piczero-char0's `picZeroAbVar0_of_leaves` and phisurj's characteristic-0 theorems. The only new
field is the leaf `hodgeTateDecompExists` (published, LEAF, flag "unread: new printed leaf (...); locator UNVERIFIED").

**Compiles and checks (VERIFIED):** the autofold wrote TailZ56 (`sixContactMin_of_open49`). The build of
Main, Discharges and the new modules succeeded (14235 jobs), and frozenTarget uses only the standard axioms.
`#discharges` shows the field discharged. The closure contains no field of the removed type and no sorryAx. The hash
guard shows only frozenTarget changed and 32 new constants in TailZ56. OpenStatements gives 35. render_open,
crosswalk (with `--check`), DischargesTest and the autoform check all pass.

**Replay:** `scratch/fold34-ht/REPLAY.md`: Contrib commits 301197af6 and 9a7266d8a, then
`autofold.py scratch/fold34-ht/autofold.json`. The fold commit is d3f989e44. Report: `docs/research/fold34-ht.md`.

**Remaining:** the locators.md row for the new leaf is not added (another task's file). The leaf has no review yet.
