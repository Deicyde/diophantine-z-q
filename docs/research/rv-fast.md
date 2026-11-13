# rv-fast: adversarial review of curve-infra, lg-kerwild, unram-roots, afr-absfrob, ring-class

Task rv-fast, 2026-11-13. Base `wip/rv-fast` (b7cdba8e), merged with origin/wip/curve-infra, lg-kerwild
(both already in the base), unram-roots (b066d686) and afr-absfrob (2ffcf322). Check files:
`scratch/rv-fast/` (results log `log.md`). This is model review only; no human has checked it.

Marks: **VERIFIED** = compiled, computed, or read in a file here. **STANDARD** = published, with a
reference. **SPECULATIVE** = my judgement. Theorem numbers recalled without a source are
**UNVERIFIED** (no network).

## 0. Verdicts (most serious first)

| result | verdict | one line |
|---|---|---|
| lg-kerwild | **CONCERN** (core results SOUND) | `TateBridgeK`, `KerWild`, `DescentPts` are right; but the every-`ℓ` LocalGlue theorem keeps a hypothesis `G7Clauses β' ε' L` about data that `TateBridgeK` hides behind `∃`, so no consumer can discharge it; and the committed file can no longer be rebuilt from the current local-glue source |
| ring-class | **SOUND** (citation note) | `hprimeNormal`, `iInH4`, `ringClassFieldD_tyz` have exactly cm-points' types; the fields are non-degenerate; the new leaf `CM.CMFieldOfDefinition ringClassFieldD` is true, but it is a consequence of Shimura's reciprocity law, not the printed statement of Gross 1984 §3 |
| unram-roots | **SOUND** | unconditional theorem; statement byte-identical to local-glue's; no hidden leaf |
| afr-absfrob | **SOUND** | `AbsFrob` proved from Mathlib with a genuine Frobenius; `FExtendGen` from I2-NMP only; statements byte-identical |
| curve-infra | **SOUND** | unconditional; `ffAlgebra` is `fnFieldAlgebra` by `rfl`; the statements give the right values on `K[X]` and `K` |

(Section 6 records the compile runs and axioms; see there for anything left unchecked.)

PLACEHOLDER-BODY
