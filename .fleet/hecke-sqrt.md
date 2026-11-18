# Hecke square root: proved

`SGRDirect.heckeSqrtBranchAny_proof` proves the unchanged global
square-root proposition from `Y3P1j.Y3ToP1j`, already in the Y₃ consumer’s
bundle. No new open hypothesis is needed. The proof is ON THE SPOT
(provenance (c)): count the finite-chart Hecke actions, take the sign of
the outer twist, use the descended CM(−24) isomorphism to get negative
inertia, and restrict a squarefree sign radicand by its inertia. This
leaves a nonzero rational multiple of `27X + 16`.

The four proof modules, `HeckeSqrtFold.lean`, and the `frozenTarget` dry
run compile. The main proof and the dry run use only `propext`,
`Classical.choice`, and `Quot.sound`. The discharge check identifies
`y3ToP1j` as the only input to the proof and confirms that the open list
loses only `heckeSqrtBranchAny`. H has 28 → 27 GLUE in both columns,
with 5 LEAF throughout (H total 33 → 32; with pole completeness 34 → 33).

For integration, apply the fold after the Y₃ fold: switch to
`OpenResearchLeaves60Y3` and `sixContactMin_of_open79_heckeSqrt`, and
remove just `research/heckeSqrtBranchAny` from kinds. The active Main is
untouched. The manuscript’s integral-model route and the independent
reading of the existing Y₃ source remain outside this proof.

See [the proof report](../docs/research/hecke-sqrt.md) and the
[results log](../scratch/hecke-sqrt/log.md).
