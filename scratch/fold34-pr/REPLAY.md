# Replaying fold34-pr on a later head

The Contrib proofs are separate from the folds: the two merges (fork PRs #54 and #55) only add files under
`ZInQKernel/Contrib/`; the folds are two runs of `scripts/one_proof/autofold.py` with the specs in this directory.

On a head H that already has further autofolds:

1. `git merge origin/proof/mumford-torsion-review-20261117` (9f54c2cc), then `git merge origin/cloud-b3/w17b-gaga-morphism`
   (d81efece); both are add-only under ZInQKernel/Contrib/ (or merge wip/fold34-pr's two merge commits 16cd620c, b97b725b).
2. `python3 scripts/one_proof/autofold.py scratch/fold34-pr/autofold-mumford.json` (writes the next free TailZ<j>,
   removes `mumfordTorsionAlgClosed` from the textbook bundle, drops its kinds and claims rows).
3. Build and check: `lake build +ZInQKernel.OneProof.Main +ZInQKernel.OneProof.Discharges`, then
   `scratch/fold34-pr/checks.sh TAG` (hash dump, closure check, OpenStatements, DischargesTest), then
   `python3 scratch/fold34-pr/tools/hashdiff.py BEFORE AFTER`, `render_open.py`, `render_open.py --check`,
   `frontier_crosswalk.py`, `--check`, `autoform check blueprint --lean-root .`.
4. `python3 scripts/one_proof/autofold.py scratch/fold34-pr/autofold-gaga.json` (removes `gagaMorphism`), and step 3 again.

The specs name only the field and the provider, so they apply to whatever the textbook bundle's generation is on H, as
long as the fields `mumfordTorsionAlgClosed` and `gagaMorphism` are still open there. If a later fold (e.g. eichler-bound's)
reads these fields as `{t}.mumfordTorsionAlgClosed` / `{t}.gagaMorphism` and is replayed after this one, its spec must use
the providers instead: `_root_.ZInQ.Contrib.CloudB3W16Torsion.mumfordTorsionAlgClosed_proof`,
`_root_.ZInQ.Contrib.OneProof.GAGAMorphism.gagaMorphism_proof`.

Builds: the two vendored libraries take about 23 min (#54, 1343 modules) and see log.md (#55) with 8 Lean threads; seed
`.lake/build` and `lean/.lake/build` from a tree with an identical `ZInQKernel/OneProof/Main.lean` first.
