# dcy3-fold: done. `deligneComponentsY3PrintedAb` removed from `frozenTarget`, no new leaf (fields −1, GLUE −1)

**Base defect (report at once).** 094bdd96 (leaf-fold29) does not build: Main.lean uses h29-ne3's `H29Split`
leaves, but the drop-in `scratch/h29-ne3/TYZLemma29Mod2.lean` was never copied over
`ZInQKernel/Contrib/OneProof/TYZLemma29Mod2.lean`. All checks below used that drop-in locally, **uncommitted**. The
integrator must apply it.

**Result (VERIFIED, with the drop-in).**
- `Y3Connected` is threaded in place as a binder `hY3`:
  - it starts at `addedLeaves8_of_open9` (TailZ13), where generation 8's `y3Connected` is produced;
  - it goes up through `sixContactMin_of_open11`–`_open27`;
  - `sixContactMin_of_open28` (TailZ34) supplies it with dcy3-used's
    `DCY3Used.y3Connected_of_leaves r.mumfordGroupLaw r.shimuraMainThmIDeligneY3AbU`. TailZ34 has one new import,
    DeligneComponentsY3Used.
- After that, PruneScan found exactly `OpenAddedLeaves17.deligneComponentsY3PrintedAb` unused.
- The field is pruned from `OpenAddedLeaves9`–`17`, nine fields with nine assignments. The off-chain generations 10
  and 11 are included, because they are filled from the next generation. No reader died.
- `open29`–`open31` and `frozenTarget` are unchanged in type and hash.
- Checks:
  - `lake build +ZInQKernel.OneProof.Main` OK, and frozenTarget's axioms are the standard three;
  - PruneScan finds 0 unused of 50;
  - cmp_hashes: removed = the 9 projections; new = the 111 DeligneComponentsY3Used constants; changed 106, all
    allowed kinds (bundle auxiliaries, conversions, `sixContactMin_of_open11`–`28`, `addedLeaves8_of_open9`);
  - DischargesTest: same 8 discharges and controls, 61 open hypotheses.
- kinds.tsv strict counts for the H rows go from 41 LEAF / 10 GLUE to **41 / 9**; strictest from 39 / 12 to **39 / 11**.
  The field's kinds.tsv and claims.tsv rows are deleted.
- open-statements.json is regenerated (61 hypotheses).

**Not done.**
- `render_open.py` fails on the base, independently of this task. kinds.tsv keys the six h29-ne3 rows by leaf name,
  while Main's binders are `hL29`, `hT21`, `hP23`, `hfx`, `hL3s` and `hJP`. So OPEN.md, pages-wanted.md,
  CONTRIBUTING.md and STATUS.md are not regenerated.
- In a temporary copy with those six keys renamed, render gave 50 H, strictest 39/11, and `--check` passed.
- frontier-crosswalk.tsv still has row H-169, which is outside the allowed edits.

Report: docs/research/dcy3-fold.md; log and tools: scratch/dcy3-fold/.
