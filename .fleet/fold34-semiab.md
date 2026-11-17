# fold34-semiab (fleet note)

**Result.** height-fix (49e6d97d, which brings height-dict) and semiab-descend (6a6de248) are merged and folded into
wip/leaf-fold33b (c0f3d085). wip/leaf-fold33b fast-forwards to wip/fold34-semiab. Report:
docs/research/fold34-semiab.md. Log: scratch/fold34-semiab/log.md.

| | top | H (render_open) | open |
|---|---|---|---|
| base | sixContactMin_of_open48 | 29, strictest 11/18 | 35 |
| fold (TailZ56) | sixContactMin_of_open49 | 30, 14/16 | 36 |

- **The fold** (one autofold, `scratch/fold34-semiab/autofold.json`): strict and strictest GLUE are both −2, and one
  field is added.
  - Removed: `bostLowerBound` and `gaudronRemondThm14` (consequence, GLUE).
  - Added: the published leaves `bostLowerBoundPrinted`, `gaudronRemondThm14Printed` (over height-fix's printed
    stable height) and `chevalleyPerfect`. Each is flagged "unread: new printed leaf (...); locator UNVERIFIED".
  - Height-fix's glue `SemiAbelianDescendsPerfect` is proved from `chevalleyPerfect`, and `uniformizationLeafAll`
    is proved on this base.
- **Not folded: the optional javanpeykar/pazuki rows.** Their 11-16 re-rating cites dictionaries that the printed
  height does not touch, so honest rows stay GLUE and the count does not change (`autofold-all4-honest.json`).
  javanpeykar-rebase is left out.

**Compiles (VERIFIED).**
- `lake build +Main +Discharges` and the new modules (14234 jobs).
- frozenTarget rests on the standard axioms.
- Closure: no binder or field has a removed type, and `sorryAx` is absent.
- Hash guard: +33 constants (TailZ56), and only frozenTarget changed.
- OpenStatements 36. render_open --check, frontier_crosswalk --check, DischargesTest and the autoform check all pass
  (OK, 781 articles).
- Merge hygiene: five bundle-redeclaring scratch files renamed `.lean.txt`. No host paths and no vendored code.

**Replay** on a later head: `scratch/fold34-semiab/REPLAY.md`. The Contrib files are separate from the fold. The
specs are `autofold.json`, and `autofold-after-height-fix.json` for a head where height-fix alone was folded.

**Remains.**
- Statement checks of the three new leaves (ChevalleyPerfect's quotient reading).
- The locators.md rows.
- unipotent-b's `SemiAbelianDescendsSepClosed` (not a hypothesis here).
