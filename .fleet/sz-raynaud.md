# sz-raynaud (fleet summary)

**Result.** Neither row (`sga7_IX_Cor3_3`, `sga7_IX_3_5_ForwardGeom`) has a counterpart on the manuscript's route at
diophantine_zq.tex L814-818, and neither can be proved from it. In their place the route has two leaves, and from them
L814-818 is proved in Lean.

- **Why the rows don't carry over.**
  - Cor. 3.3 feeds only the persistence of semistability under base change (SS3: heights over a common field). The
    manuscript gets semistability over `F = L_v(A[3])` directly, so there is nothing to persist.
  - IX 3.5 feeds r6: D2, where the manuscript needs only the weaker wild-inertia sentence, and A6, which is not the
    manuscript's route.
- **New leaves** (`ZInQKernel/Contrib/OneProof/SZRaynaud.lean`):
  - `SilverbergZarhinThm35`: **LEAF**, provenance (b), cited at L816. Read from the page image 11-17: `n >= 3`
    (the locators R6 worry was an OCR misread), any field with a discrete valuation, semistable as an extension by a
    torus that need not be split (`IsSemistableResT`). No known issue.
  - `ElliotWildInertiaTrivial`: **ELLIOT**, the uncited sentence at L817-818 (kind consequence). Stated at a finite
    place of a number field. It is true and standard (SGA 7 IX 3.5 + wild inertia pro-p), but the manuscript cites
    nothing for it; the documented issue and a suggested citation are in the report, §4.
- **Proved** (standard axioms, no sorry; compiles):
  - `isSemistable_of_sz`: the named step from SZ's semistability to the kernel's (Stacks 04KV).
  - `raynaudSemistable_of_sz35`: the kernel's Raynaud criterion over every DVR.
  - `raynaudSemistableSHOr_of_sz35`: the bundle field, statement unchanged.
  - `raynaudWildNF_of_leaves`: L814-818 from SZ35 + ELLIOT.
  - `def34_of_sz35`: SZ gives ga-rigidity's Déf. 3.4 "no G_a" hypothesis, via GaRigidity's rigidity.
  - `elliot_of_semistableUnipotent`: sanity check, from IX 3.5 + on-the-spot glue that is not proved.
- **Fold.**
  - scratch/sz-raynaud/autofold.json discharges `raynaudSemistableSHOr` with the leaf `silverbergZarhinThm35`.
  - #discharges confirms it.
  - Strict dry run (leaf-fold33b's scripts, d67ea55f6, identical at 74395dcf0): **12/22 on 34 -> 12/22**, strictest
    11/23 -> 11/23 (a LEAF on SGA 7, which the manuscript does not cite, replaced by a cited one).
  - The dry-run module compiles (`sixContactMin_of_open61`, standard axioms).

**Remains.**
- Lead's call on how ELLIOT rows count. The ELLIOT leaf discharges no field: r6 is still needed by A6.
- Follow-up: reroute D2 (TailH `raynaudPlace_of_R6`, `torsFix_of_descent`) through `RaynaudWildNF`, then reroute A6
  to the manuscript's universal abelian scheme (L529-530). Only then do both SGA 7 rows leave the bundle.

Report: docs/research/sz-raynaud.md; log, spec, Discharges.lean and dry-run output: scratch/sz-raynaud/.
