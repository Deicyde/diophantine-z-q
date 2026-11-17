# fold-chev

**Verdict: folded.** The research field `chevalleyPerfect` (Chevalley over a perfect field, GLUE/GLUE) is gone from
`ZInQ.OneProof.frozenTarget` with no new leaf.
- **Counts:** 39 → **38** open; H 34 → **33**; strict and strictest **9/25 → 9/24**.
- **Why it works:** chevalley-free proved `ZInQ.HeightFix.SemiAbelianDescendsPerfect` outright. That proof is now
  `ZInQKernel/Contrib/OneProof/ChevalleyFree.lean`; the scratch copy is renamed `.lean.txt`.
- **Fold module:** `ZInQKernel/OneProof/H/TailZ72.lean`, a bypass. autofold cannot be used because there is no proof of
  `ChevalleyPerfect`, and the three readers sit nine conversions below the top.
  - `OpenResearchLeaves46` is `OpenResearchLeaves45` without the field.
  - `openResearchLeaves36EB_of_OpenResearchLeaves46` is the composite of every conversion from `sixContactMin_of_open64`
    down to `sixContactMin_of_open53_eb_k954`.
  - In it, `bostLowerBound`, `gaudronRemondThm14` and `javanpeykarBound` take `semiAbelianDescendsPerfect` from
    chevalley-free.
  - The new top theorem is `sixContactMin_of_open65`.
- **Other edits:** Main is switched to the new bundle and top theorem. The kinds row is dropped (there was no claims
  row). The docs are regenerated.

**What compiles and is checked** (VERIFIED):
- `lake build` of Main, Discharges, ChevalleyFree and TailZ72 succeeds.
- `frozenTarget` and `sixContactMin_of_open65` use only the standard axioms.
- **Closure check:** no `ChevalleyPerfect`, no `sorryAx`, no `OpenResearchLeaves45`.
- **Hash guard:** only `frozenTarget` changed; 38 new constants, all in TailZ72.
- **Regenerated and checked:**
  - OpenStatements gives 38.
  - `render_open` and `frontier_crosswalk` pass `--check`.
  - DischargesTest was rerun.
  - The autoform check passes.
- `#discharges` does not show `chevalleyPerfect` as discharged, because this is a bypass. The field is simply no longer
  a hypothesis.

**Replay:** run `python3 scratch/fold-chev/gen/gen_bypass.py` on any later head. It follows Main's chain, so it works on
top of further autofolds; this was tested in text only, on a head with a fake extra autofold. Keep the Contrib commit and
regenerate the fold. Commits: 36808d3e merge, c0761608 Contrib move, c72c936a generator, ba5f6df5 fold. Report: `docs/research/fold-chev.md`; log: `scratch/fold-chev/log.md`.

**What remains:** nothing for this fold. A side note: `ZInQ.ChevFree.pazukiCor13Upper_of_printed_free` would let
`pazukiCor13Upper` be retyped to height-fix's printed leaf. That is a rating question and was not done.
