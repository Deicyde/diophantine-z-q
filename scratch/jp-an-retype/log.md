# jp-an-retype results log

## 11-17 06:00 setup
- Base bf691da22; merged origin/wip/semistab-assembly 418304785 (no conflicts).
- Statements read (VERIFIED, in tree): `JavanpeykarDirect.JavanpeykarThm111` JavanpeykarDirect.lean:86,
  `IsStableHeightBar` :63 (clause `ZInQ.HeightFix.IsPrintedStableHeight (ofVendored V) x`);
  `ZInQ.R3Residual.IsAnStableHeight` AnalyticStableHeight.lean:710 (clause `IsSemistableRes 𝒩`);
  `isAnStableHeight_iff (hT35 : UniformizationExists)` :835; r3-residual discharges hT35 by
  `AvSplit.Final.h38 uniformizationLeafAll_proof hMT` (`javanpeykarPrintedMap_of_an`, :948).
  `ZInQ.SemistabAssembly.IsAnStableHeightSS` (clause `IsSemistablePrinted 𝒩`, both readings).
- Current top field: `javanpeykarThm111 : JavanpeykarDirect.JavanpeykarThm111` (TailZ74.lean:881).
- Manuscript L860-875 (VERIFIED, read): "By \cite[Theorem 1.1.1 and Section 2.3]{javanpeykar}", h_F(J) <= 13000000 N^12,
  J = J_1(N); "The normalization in that theorem is the original stable Faltings height of the Jacobian."

## 11-17 06:02 Lean (ZInQKernel/Contrib/OneProof/JavanpeykarAnRetype.lean, namespace JavanpeykarAnRetype)
- `lake env lean` on the file: VERIFIED compiles, no errors, no warnings.
- Proved (VERIFIED, compiled):
  - `isSemistableRes_of_resPrinted`, `isSemistableRes_of_printed`: IsSemistablePrinted 𝒩 -> IsSemistableRes 𝒩
    (U open with range = connectedComponent of unit => U connected; open embedding is inducing). Converse of
    semistab-assembly's bridge, so the SS clause is EQUIVALENT to IsSemistableRes.
  - `isAnStableHeightSS_iff : IsAnStableHeightSS A x ↔ IsAnStableHeight A x` (no T35).
  - `IsStableHeightBarAn` (def), `isStableHeightBarAn_iff (hT35)`: ↔ IsStableHeightBar.
  - `JavanpeykarThm111An` (def, the leaf): JavanpeykarThm111 verbatim with IsStableHeightBar -> IsStableHeightBarAn.
  - `javanpeykarThm111_of_an' (h) (hUL) (hMT)`, `javanpeykarThm111_of_an (h) (hMT) : JavanpeykarThm111`.
  - `javanpeykarThm111An_of_thm111 (h) (hT35) : JavanpeykarThm111An` (converse: not stronger).

## 11-17 06:20 checks
- `lake build +Main +Discharges +JavanpeykarAnRetype`: VERIFIED "Build completed successfully (16217 jobs)".
- `#discharges` (discharges-output.txt): VERIFIED `DISCHARGES [OpenResearchLeaves48.javanpeykarThm111] by
  JavanpeykarAnRetype.javanpeykarThm111_of_an`, still assumes [JavanpeykarThm111An, AvSplit.MumfordTorsionAlgClosed];
  axioms standard. All five #print axioms standard.
- `autofold.py scratch/jp-an-retype/autofold.json --dry-run` (autofold-dryrun.txt): VERIFIED exit 0,
  "strict count: 4/27 on 31 -> 4/27 on 31; strictest 4/27 -> 4/27" (count effect 0).
- Rating: javanpeykarThm111An consequence/GLUE; not printed form: R3' inside the height, and the §2.3 composite
  (lead's ruling wanted). No ON THE SPOT arguments.
