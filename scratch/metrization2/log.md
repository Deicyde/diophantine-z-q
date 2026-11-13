# metrization2 results log

- Setup: scratch/metrization2/base/ = verbatim copies of scratch/metrization/{Base,ExtLine,part_*}.lean
  (Base.lean byte-identical to scratch/metrization/Base.lean, VERIFIED by cmp). MetrBase.lean (generated,
  gitignored) = metrization's build.sh assembly minus `#print axioms` lines; compiled to an olean with
  `lake env lean -o` in 2 min 38 s, 0 errors (VERIFIED), used only for fast iteration.
