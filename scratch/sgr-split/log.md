# sgr-split results log

Target: `HDec.CurveSplitGR.ShimuraGoodReductionNoGuard` (ZInQKernel/OneProof/H/TailW.lean:739).

## Final result
`SGRSplit.shimuraGoodReductionNoGuard_of_printed : ShimuraIntegralModelRep → ShimuraGoodReductionNoGuard`
(ZInQKernel/Contrib/OneProof/ShimuraGoodReductionNoGuard.lean). Standard axioms. VERIFIED (compiled, #discharges).

## Statements
- Verbatim copy: `StatementCopy.lean` (namespace `HDec.SGRCopy`), `Iff.rfl` with the chain's. VERIFIED (compiled).
- New printed leaf `ShimuraIntegralModelRep` (representability over ℤ_(p), p > 324, on `QMAbScheme`; Kottwitz 1992 §5, Buzzard 1997, Morita 1981; locators UNVERIFIED). Flag: pending reading (level at 3 | D; PEL vs polarization-free).
- Glue, all proved: `QMAbFieldFibre` (G1), `QML3AsQMAb` (G2), `FibreClassUnique` (G3), `AbVarSurfaceRelDim`, `SmoothGeomConnIntegral`, `AbVarEndTorsionFree` (char 0).

## Compile outcomes (lake env lean / lake build; all standard axioms)
- 02:30 `SGR.lean`: `shimuraGoodReductionNoGuard_of_rep` compiled. VERIFIED.
- 02:32 `fibreClassUnique` compiled. VERIFIED.
- 02:35 `qml3AsQMAb_of` compiled. VERIFIED.
- 02:40 Contrib file built (86 s); first `#discharges`. VERIFIED.
- 02:43 first autofold dry run (3 new rows, strict 46/13 -> 47/14). Superseded.
- 02:48 `abVarSurfaceRelDim` proved (Smooth.exists_isStandardSmooth chart + ZInQ.Contrib.Dim stalk dimensions). VERIFIED.
- 02:57 `qmAbFieldFibre_of : SmoothGeomConnIntegral → AbVarEndTorsionFree → QMAbFieldFibre` (`G1.lean`). VERIFIED.
- 03:03 `smoothGeomConnIntegral` (`L1.lean`; vendored `Algebra.Smooth.isDomain_and_isIntegrallyClosed_of_isLocalization_atPrime` + Tau Ceti `irreducibleSpace_of_connected_of_isDomain_stalk`). VERIFIED.
- 03:04 `abVarEndTorsionFree0` (`L2.lean`; `ZInQ.Contrib.AbVarBC.mulIsogeny` + `ext_of_isDominant_of_isSeparated`). VERIFIED.
- 03:09 Contrib file rebuilt; `#discharges`: still assumes [SGRSplit.ShimuraIntegralModelRep] (`discharges.txt`); autofold dry run: strict 46/13 on 59 -> 46/13 on 59, strictest 45/14 -> 45/14, generated module (`AutofoldDryRun.lean`) compiles, `sixContactMin_of_open26` standard axioms. VERIFIED.

## Findings
- curve-split §3.6 "not statable": superseded; `QMAbScheme` supplies abelian schemes over a base with 𝒪-action and level 3.
- NOS (r7a) / Néron / BLR leaves concern models of abelian varieties; they do not produce a model of the curve (statements VERIFIED by reading Objects.lean 861, 1377).
- Pitfall: `ι` is GrpObj inverse notation under `open MonObj`; a `let` of an anonymous `AbVar` structure blocks the `Ring (End _)` instance (use a def).
