# fold-chev: chevalley-free folded, the research field `chevalleyPerfect` removed with no new leaf

Task fold-chev, 2026-11-17. Base: wip/leaf-fold33b `1a3bab4a`, H top `sixContactMin_of_open64`. This is model work,
and no human has reviewed it.

## 1. Result

**The research field `chevalleyPerfect` is gone from `ZInQ.OneProof.frozenTarget`, and no leaf replaces it.**
- The field was `ZInQ.SemiAbDescend.ChevalleyPerfect`, Chevalley's structure theorem over a perfect field, rated
  GLUE/GLUE.
- chevalley-free proved `ZInQ.HeightFix.SemiAbelianDescendsPerfect` outright:
  `ZInQ.ChevFree.semiAbelianDescendsPerfect_proof`, now in `ZInQKernel/Contrib/OneProof/ChevalleyFree.lean`. That
  statement is the only thing the field's readers took from it.

The fold:
- **Module:** `ZInQKernel/OneProof/H/TailZ72.lean`.
- **New bundle:** `OpenResearchLeaves46`, which is `OpenResearchLeaves45` minus the field (30 fields).
- **New top theorem:** `sixContactMin_of_open65`.

Counts (render_open, VERIFIED):

| | before | after |
| --- | --- | --- |
| open hypotheses | 39 | **38** |
| H hypotheses | 34 | **33** |
| strict LEAF/GLUE | 9/25 | **9/24** |
| strictest LEAF/GLUE | 9/25 | **9/24** |
| others | 5 | 5 |

So the fold removes one field and one strict GLUE.

Checks (VERIFIED):
- **Build:** `lake build ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges ZInQKernel.Contrib.OneProof.ChevalleyFree
  ZInQKernel.OneProof.H.TailZ72` succeeds (16095 jobs).
- **Axioms:** `#print axioms ZInQ.OneProof.frozenTarget` and `#print axioms HDec.HSyn.sixContactMin_of_open65` are both
  `[propext, Classical.choice, Quot.sound]`. All 22 `#print axioms` lines of ChevalleyFree are the same.
- **Closure** (`scratch/fold-chev/FoldCheck.lean`): the closure of `frozenTarget` has 302580 constants. It contains none
  of these:
  - `ChevalleyPerfect`, `semiAbelianDescendsPerfect_of_chevalley`, `bostLowerBound_of_printed_chevalley`,
    `gaudronRemondThm14_of_printed_chevalley`;
  - `sorryAx`;
  - `OpenResearchLeaves45`, `sixContactMin_of_open64`.
- **Hash guard** (DumpCompact): 17348 → 17386 constants.
  - 0 removed.
  - 38 added, all in `TailZ72`.
  - Only `ZInQ.OneProof.frozenTarget` changed.
- **Regenerated files:**
  - OpenStatements: 38.
  - `render_open.py`, then `--check`: ok.
  - `frontier_crosswalk.py`, then `--check`: ok, the table is unchanged.
  - DischargesTest rerun: the only change is the labels `45` → `46`, plus one new row (`ZInQ.ChevFree.pazukiCor13Upper_of_printed_free`).
  - autoform check blueprint: ok (772 articles).

## 2. Why a bypass, not autofold

autofold fills a field with a proof of that field's type, and `ChevalleyPerfect` itself is not proved. The field is
read in exactly three places (grep and closure, VERIFIED), all in `EichlerBoundCopy.lean`, nine conversions below the
top bundle:

| conversion | reader | how it reads the field |
| --- | --- | --- |
| `38EB → 37EB` | `javanpeykarBound` | through `semiAbelianDescendsPerfect_of_chevalley` |
| `37EB → 36EB` | `bostLowerBound` | through `bostLowerBound_of_printed_chevalley` |
| `37EB → 36EB` | `gaudronRemondThm14` | through `gaudronRemondThm14_of_printed_chevalley` |

All three end in `semiAbelianDescendsPerfect_of_chevalley`. After step 23 of leaf-fold33 and r3-residual, the printed
inputs of these readers come from `bostLowerBoundAn` and `gaudronRemondThm14An`, through
`R3Residual.*Printed_of_an` in `TailZ68`. The bypass keeps that route.

How the bypass works:
- `openResearchLeaves36EB_of_OpenResearchLeaves46` composes, field by field, every research conversion that
  `sixContactMin_of_open64` applies on its way down to `sixContactMin_of_open53_eb_k954`. That is the first step whose
  bundle `OpenResearchLeaves36EB` no longer carries the field.
- In the composite, the three readers are replaced by `ZInQ.ChevFree.bostLowerBound_of_printed_free`,
  `gaudronRemondThm14_of_printed_free` and `semiAbelianDescendsPerfect_proof`.
- `sixContactMin_of_open65` calls the existing `sixContactMin_of_open53_eb_k954` (fold-kleiman2's copy chain, which
  takes `OpenAddedLeaves26`).
- No declaration is copied or changed.

## 3. Reproducing it on a later head

The proof and the fold are kept separate:
1. **Contrib file.** `ZInQKernel/Contrib/OneProof/ChevalleyFree.lean` is a verbatim copy of chevalley-free's
   `ChevFree.lean`. Its scratch copy is now `scratch/chevalley-free/ChevFree.lean.txt`.
2. **Generator.** `python3 scratch/fold-chev/gen/gen_bypass.py [--dry-run]`, run from the repository root on any head
   whose top research bundle still has `chevalleyPerfect`:
   - It reuses autofold's parsers.
   - It follows Main's top theorem down the chain and composes the conversions.
   - It writes the next `TailZ<j>`, the next bundle and the next `sixContactMin_of_open<N+1>`.
   - It switches Main (import, bundle, top call, and a docstring paragraph placed before "The hypotheses of
     `frozenTarget` are therefore exactly the open statements.").
   - It drops the field's kinds and claims rows.
   - It refuses to run if any result still reads the field, or if a GLUE count would rise.
3. **Checks.** Then run the usual checks as in §1.

Replay test (VERIFIED, text only): on the base plus a fake autofold that removes one more field and uses `{t}`, the
generator produced `TailZ73` with `OpenResearchLeaves47` and `sixContactMin_of_open66`. Its chain was one step longer
and it reached the same stop bundle and the same three readers.

On the lead's head:
- The commits that land the Contrib file are `c0761608` (merge plus move) and `c72c936a` (generator).
- The fold itself is commit `ba5f6df5e` (`bypass fold TailZ72`); if the head moved, regenerate it rather than cherry-picking it.

## 4. Hygiene

- Merged `origin/wip/chevalley-free` `81ca42f6`. Its base `fe2f0d4a` is an ancestor of `1a3bab4a`, and the merge had
  no conflicts.
- `scratch/chevalley-free/ChevFree.lean` and `fold/MainCheck.lean` are renamed `.lean.txt`. MainCheck redeclares the
  HDec.HSyn bundles.
- No host paths.
- The vendored CloudW07 LICENSE and NOTICE files are unchanged.
- The full build logs are left out; there are excerpts in `scratch/fold-chev/`.
  - Caveat: one intermediate commit (`bypass fold TailZ72 … (unbuilt)`) still carries the 9 MB base build log. It is
    deleted in the next commit. History was not rewritten, because the branch is pushed in the background.

## 5. Side observation (not acted on)

`#discharges` now lists `ZInQ.ChevFree.pazukiCor13Upper_of_printed_free`. It proves the open field
`pazukiCor13Upper` from:
- height-fix's printed leaf `ZInQ.HeightFix.PazukiCor13UpperPrinted`;
- `uniformizationLeafAll` and `mumfordTorsionAlgClosed` (both proved);

with standard axioms. Replacing that field by the printed leaf is a separate rating question: the field is currently
re-rated under the dictionary ruling. It is outside this task.

## 6. What this does not do

- Chevalley's theorem itself is not proved; the proof no longer needs it.
- `UnipotentForward.SemiAbelianDescendsSepClosed`, the imperfect case, is untouched.
