# c8-conrad (2026-11-17)

**Verdict.**
* **Why Conrad was replaced.** The appeal to Conrad App. B was not replaced because of a defect. h-trust C8 adopted
  V14/V16's determinant argument as a shortening (up-h §4 item 1). rv-h-c8 §4 verified N5's
  local-algebraicity chain as an argument. Glazer's theorem-application audit accepted A011 and itself added the
  Conrad citation. The only caveats: the source is an unrefereed preprint, and the finiteness at l != 5 is elementary
  but unstated in N5.
* **Target not reachable through C8** (VERIFIED by source reading and a field-taint run on the built top,
  `scratch/c8-conrad/fieldtaint_out.txt`). `picRepresentableAbVar` and `kleimanPicZeroProper954SiteQ` have three live
  consumers:
  * (i) C8: `DetTate` / `G12DetPZ`;
  * (ii) Poincaré reducibility, `t8` (E1-E2, manuscript L865);
  * (iii) `hodgeTateDecompAbVar` -> `r10` (R10, read by G9 and G11).

  Rerouting C8 removes (i) only, so no fold is proposed.

**What compiles** (standard axioms, `lake build` ok): `ZInQKernel/Contrib/OneProof/C8Conrad.lean`, a copy of
`scratch/c8-conrad/C8Conrad.lean`. It contains:
* `ConradAppBQp`: Conrad App. B for base field Q_p over Tau Ceti's local Artin map. Printed-form instance, flagged
  unread (the PDF fetch was refused; the statement is the audit's report). GLUE in the strict reading, as an unrefereed
  preprint.
* Three glue Props: `TwistCharHT0`, `LocAlgExponentEqWeight`, `FiniteOfLocAlgTrivialQ`.
* `g12DetPZ_of_conrad`, which proves C8's consumer `HDec.G0Galois.G12DetPZ` without DetTate or the Weil pairing.
* `g12DetPZ_of_twistFinite`, which shows `G12DetPZ` is equivalent to "the twist has finite image".

`#discharges`: nothing discharged, as expected. `scratch/c8-conrad/autofold.json` records that no field is discharged
and lists the would-be leaf and glue.

**What remains.**
* Read Conrad pp. 32-33 against `ConradAppBQp`.
* Prove the three glue Props.
* Reroute (ii): Mumford §19 as a printed leaf.
* Reroute (iii): HT multiplicities g, g as a printed leaf (Faltings 1988 III.4.1).

Only then does the one-term C8 swap at `g8_g12_of_leaves3_hf_pz_eb` (`docs/research/c8-conrad.md` §5) take the two
Picard rows off the route. Report: `docs/research/c8-conrad.md`.
