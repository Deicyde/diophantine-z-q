# igusa-drop: `igusaGL2DSGalSome` removed from the single proof with no new leaf

Task igusa-drop, 2026-11-17. Base: wip/leaf-fold33b 97247ce1. Top before: `sixContactMin_of_open71` (TailZ78).
Results log: `scratch/igusa-drop/log.md`. Branch wip/igusa-drop = base + this task's commits (fast-forward). Model
work; no person has reviewed it.

## 1. Result

**The research field `igusaGL2DSGalSome` (Diamond–Shurman Thm 7.6.3, printed form; igusa-gal, TailZ73) is gone from
`ZInQ.OneProof.frozenTarget`, with no new leaf and no new statement.** frozenTarget still uses only
`propext`, `Classical.choice` and `Quot.sound` (VERIFIED).

| | top | open | H strict / strictest |
| --- | --- | --- | --- |
| base | `sixContactMin_of_open71` (TailZ78, `OpenResearchLeaves52`) | 35 | 6/24 on 30 |
| igusa-drop | `sixContactMin_of_open72` (TailZ79, `OpenResearchLeaves53`) | 34 | 5/24 on 29 |

The field was rated LEAF/LEAF (inbox 53), so removing it lowers the LEAF count and the field count by one; the strict
GLUE count (24) is unchanged. The fold qualifies because it removes a field.

## 2. Why no leaf is needed (the reviewer's analysis, confirmed in Lean)

The chain used Igusa's theorem once: `AfTateLam.r16CoreY_of_printed` (AfTateLambda.lean:857) applies
`X1Igusa.x1PointsConjugate_of_igusaGL2DS hI` and uses `hI` nowhere else; `r16CoreY_of_ds965` only passes `hI` through.
The Prop it needs, `R16IsJ1Dict.X1PointsConjugate`, is proved:

1. `X1PointsConjugate ↔ ZInQ.RLeaf.IgusaTransitive` is `Iff.rfl` (`X1Igusa.x1PointsConjugate_iff_igusaTransitive`);
2. `IgusaTransitive ↔ X0Transitive` (`ZInQ.RLeaf.igusaTransitive_iff_x0Transitive`, Contrib/RLeaf/T40.lean, using the
   proved `ZInQ.RLeaf.tateMuN`);
3. `X0Transitive` is `FltCqj2.x0Transitive_proof` (Contrib/OneProof/ModularEquationGeneric.lean; Anthropic FLT's
   cyclic-quotient bijection, ported), already in the build (TailX.lean).

New module **`ZInQKernel/Contrib/OneProof/IgusaDrop.lean`** (imports R16CoreYDS965, RLeaf.T40,
OneProof.ModularEquationGeneric; a leaf module, so acyclic):
- `AfTateLam.x1PointsConjugate_proof : R16IsJ1Dict.X1PointsConjugate` (steps 1–3);
- `AfTateLam.r16CoreY_of_printed_x0 (h1 : HeckeJ1DS) (h2 : AfShimura) (h3 : AfTateDSLambda)
  (hM : AvSplit.MumfordTorsionAlgClosed) : R16Split.R16CoreY` — the proof of `r16CoreY_of_printed` verbatim with
  `x1PointsConjugate_proof` in place of the Igusa step;
- `AfTateLam.r16CoreY_of_ds965_x0 (h1) (h2) (h3 : AfCharpolyDS965) (hM) : R16Split.R16CoreY`.
All three: standard axioms (VERIFIED, `lake build`).

## 3. The fold (bypass, generated)

`IgusaGL2DSGalSome` itself is not proved, so autofold cannot remove the field; the fold is a copy reroute in
fold-b105's pattern. `scratch/igusa-drop/gen_igusa_drop.py` (fold-b105's `gen_chev_bypass.py` with this field and one
reader rule) walks `sixContactMin_of_open71 → openResearchLeaves51_of_OpenResearchLeaves52 → sixContactMin_of_open70
→ openResearchLeaves36EBCF_of_OpenResearchLeaves51` and stops at `OpenResearchLeaves36EBCF`, the first bundle without
the field. The only reader is the field `r16CoreY` of that composite, rewritten to
`AfTateLam.r16CoreY_of_ds965_x0 n.heckeJ1DS n.afShimura n.afCharpolyDS965 mumfordTorsionAlgClosed_proof`.
Generated `ZInQKernel/OneProof/H/TailZ79.lean`: `OpenResearchLeaves53` (= `OpenResearchLeaves52` minus the field,
docstrings verbatim, 27 fields), the composite `openResearchLeaves36EBCF_of_OpenResearchLeaves53`, and
`sixContactMin_of_open72`; Main.lean switched (one paragraph added to its docstring); the kinds.tsv row
`igusaGL2DSGalSome` dropped. There was no claims.tsv row and no reviews.tsv row. Every existing declaration is unchanged.

## 4. Checks (VERIFIED; outputs in scratch/igusa-drop/)

- `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges +ZInQKernel.Contrib.OneProof.IgusaDrop`:
  success (16226 jobs).
- `#print axioms ZInQ.OneProof.frozenTarget`: [propext, Classical.choice, Quot.sound].
- Closure check (`FoldCheck.lean`, 304529 constants): no `sorryAx`, `X1Igusa.IgusaGL2DSGalSome`,
  `X1Igusa.IgusaGL2DS`, `igusaGL2DS_of_igusaGL2DSGalSome`, `x1PointsConjugate_of_igusaGL2DS`,
  `AfTateLam.r16CoreY_of_ds965`, `r16CoreY_of_printed`; the replacement route is present.
- DumpCompact hash guard against the base oleans: 35 new constants, all in TailZ79; only `ZInQ.OneProof.frozenTarget`
  changed; none removed (`cmp_hashes.txt`).
- OpenStatements.lean: 34 open. render_open: 29 H, strictest 5/24, 5 others; `--check` ok.
  frontier_crosswalk and `--check` ok. DischargesTest rerun, no error. autoform check: exit 0, 776 articles.
- `#discharges` cannot list the field as DISCHARGED (bypass); the closure check is the evidence, as for fold-b105's
  `chevalleyPerfect`.
- Replay (text): the generator run on a fresh worktree at the Contrib commit 159fcd50 reproduces TailZ79, Main.lean,
  kinds.tsv and claims.tsv byte for byte; on the folded head it reports "nothing to do".

## 5. Replay on a later head

See `scratch/igusa-drop/REPLAY.md`. The Contrib file is its own commit (159fcd50); the fold is
`python3 scratch/igusa-drop/gen_igusa_drop.py`, then the build and `bash scratch/igusa-drop/run_checks.sh <base tree>`.
The generator composes later autofolds through and aborts if any reader of another shape remains.

## 6. Notes

- The kinds row and reviewer rating of `igusaGL2DSGalSome` (inbox 53, LEAF/LEAF) are superseded: the row is gone.
  igusa-gal's Lean (`X1Igusa.igusaGL2DS_of_igusaGL2DSGalSome`, Contrib/OneProof/IgusaGL2DSGalSome.lean) stays in the
  tree, unused by the single proof.
- Provenance: no statement introduced; nothing on-the-spot.
