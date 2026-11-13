# tc-license results log

## Merge
- `git merge origin/main` at start: fast, only added files (merge commit b7a1fa99). VERIFIED.

## Step 3: modified vendored files (Apache-2.0 §4(b))
- Tool: `scratch/tc-license/diffcheck.py WORKTREE [-v]` regenerates each vendored file from its
  Tau Ceti source (commit read from the provenance line; 5a01f5fe → ~/tc-oct16, 97a5b235 → ~/tc-nov01)
  with tcport.py's import rewrite + provenance line, and compares byte for byte.
- Result on this branch (before step 3): 1120 files under ZInQKernel/Contrib/TauCeti/; 1110 identical;
  2 without provenance (MathlibBackport/Sylow.lean, Notice.lean: original project files);
  8 differ. VERIFIED (computed). The 8 diffs are exactly those listed in docs/research/tc-port.md:
  - NumberTheory/ClassFieldTheory/Formation/InvariantKernel.lean: `.isPGroup` → `.isPGroup'` (1 line)
  - RepresentationTheory/Homological/ContCohomology/Coinduced/Discrete.lean: `G A` added to 3 instance heads
  - RepresentationTheory/Homological/GroupCohomology/PrimeIndex.lean: `.isPGroup'` (2 lines)
  - RepresentationTheory/Homological/TateCohomology/TrivialityCriterion.lean: `.isPGroup'` (1 line)
  - Topology/Algebra/Group/Profinite/Generation.lean: `rfl` added (1 line)
  - Topology/Algebra/Group/Profinite/Sylow/Basic.lean: `.isPGroup'` (1 line)
  - Topology/Algebra/Group/Profinite/Sylow/Containment.lean: import of MathlibBackport.Sylow added
  - Topology/Algebra/Group/Profinite/Sylow/Existence.lean: `.isPGroup'` (1 line)
- Each of the 8 got one line `-- Modified for the Z-in-Q kernel: <change>.` directly under the
  provenance line (`scratch/tc-license/addnotes.py`).
- MathlibBackport/Sylow.lean: the leading comment block (which named Tau Ceti and Mathlib licensing)
  removed; the file now starts with `module` like this project's original Lean files, and the module
  docstring states it is original to the project, only the name/statement following Mathlib PR #44454.
  Not copied from Tau Ceti: no `is_maximal'` / `theorem maximal_isPGroup` in ~/tc-oct16, ~/tc-nov01,
  ~/tc-main. VERIFIED (grep).

## Step 4: rebuild (lake build, one module at a time, 2026-11-13 04:18 PST)
All rc=0, "Build completed successfully", .olean timestamps renewed. VERIFIED (compiled):
MathlibBackport.Sylow, NumberTheory.ClassFieldTheory.Formation.InvariantKernel,
RepresentationTheory.Homological.ContCohomology.Coinduced.Discrete,
RepresentationTheory.Homological.GroupCohomology.PrimeIndex,
RepresentationTheory.Homological.TateCohomology.TrivialityCriterion,
Topology.Algebra.Group.Profinite.Generation, Topology.Algebra.Group.Profinite.Sylow.{Basic,Containment,Existence}
(all under ZInQKernel.Contrib.TauCeti.).
