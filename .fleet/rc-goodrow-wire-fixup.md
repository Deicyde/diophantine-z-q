# rc-goodrow-wire-fixup hand-off

Documentation-only fixes for the reviewer's three warns and one report edit, as commits on top of
wip/rc-goodrow-wire at b18ad0569. No new Lean declarations and no statement changes; the Lean edits are
in comments only.

**Commits.**

1. 900ccb1b6: (O.7) is derived in Lean from the listed inputs, not proved (goodrow-wire, target and
   neron reports, target hand-off); the tex 9101–9113 verdict is "reduced to the listed inputs".
2. f09c2128c: "What remains" lists `π`, `hQ`, `han` (substantive), `F`, `hN`, the three instance
   arguments and `X` (fixed by `J`'s owner; `sp` for the same `X`).
3. d92e01a35: one owner for `point_W` (input of `SamePlaceData`, same-place lane in the hCM lane; also
   needs generic5 item 4) and one status for `extension` (supplied by `ModelGeneric5.goodRow_extension`,
   witness `Wint`); the neron report's OPEN.md locator is now "`docs/one-proof/OPEN.md`, section `hRC`".
4. 6dc8e1c2f: degenerate-witness statement (Known issues of the report; one sentence in the hand-off).
5. 3df84a04f: docstrings in `RC/GoodRowWire/SamePlace.lean` and `RC/GoodRowWire/Assembly.lean`.

**Build.** After commit 5, `lake build` of `RC.GoodRowWire.SamePlace`, `.Row` and `.Assembly` (one
process, throttled) succeeded with no errors. `#print axioms` gives only propext, Classical.choice and
Quot.sound. Output: `scratch/rc-goodrow-wire-fixup/build.txt`.

**Questions for the lead (stop rule).**

* Edit 5: the module docstring of `SamePlace.lean` already names `frobenius_sq` (lines 5–6, wrapped
  onto line 6). The smallest faithful edit was to name the four fields, including `frobenius_sq`, in
  the `SamePlaceData` structure docstring, which had not named them.
* Edit 3: the stale OPEN.md line locator in the neron report was at line 84, not 82. The same kind of
  line locator remains in `docs/research/rc-model-target.md:10`, `.fleet/rc-model-target.md:23` and
  `docs/research/rc-model-generic5.md:3`, which the instruction did not cover; left unchanged.
* Edit 1: the generic5 report's tex 9101–9113 row ("unverified"; that run did not touch (O.7)) is not
  in edit 1's file list and was left unchanged.

**SHA.** Last content commit: 3df84a04f. This hand-off file is committed on top of it; the branch tip
is the final SHA.
