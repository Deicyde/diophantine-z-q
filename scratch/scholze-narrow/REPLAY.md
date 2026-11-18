# Replay

From the repository root at the base plus this change, with the base project
dependencies available in Lake. Run one command at a time. The wrapper checks
host load and available memory before invoking `lake env lean`.

```sh
set -o pipefail
python3 scratch/scholze-narrow/build_base.py ZInQKernel.OneProof.Main ZInQKernel.OneProof.Discharges
bash scratch/scholze-narrow/check.sh -o .lake/build/lib/lean/ZInQKernel/Contrib/OneProof/ScholzeNarrow.olean ZInQKernel/Contrib/OneProof/ScholzeNarrow.lean
bash scratch/scholze-narrow/check.sh scratch/scholze-narrow/Readers.lean
bash scratch/scholze-narrow/check.sh scratch/scholze-narrow/Discharges.lean
bash scratch/scholze-narrow/check.sh scratch/scholze-narrow/Census.lean | sed -n '5,$s/[[:space:]]*$//p' > scratch/scholze-narrow/census-output.txt
python3 scratch/scholze-narrow/generate.py
python3 scratch/scholze-narrow/counts.py
bash scratch/scholze-narrow/check.sh scratch/scholze-narrow/Chain.lean
bash scratch/scholze-narrow/check.sh scratch/scholze-narrow/DryRun.lean
```

`build_base.py` expects the pinned external package oleans and the checked-out
helper package oleans. It compiles missing project modules in import order and
always recompiles the base headline. For an already built base, omit this
step.

The generator writes the proposed H chain as `Chain.lean` and the
standalone `DryRun.lean`, embedding that same H chain and the checks from
`Closure.lean.txt`. No scratch Lean file imports another. The first import
in the dry run makes the old headline available as a control. For an
integration, the chain imports only the old tail and the new contribution;
the scratch-only harness is not part of the fold. This generator never
modifies the live headline or catalog.
