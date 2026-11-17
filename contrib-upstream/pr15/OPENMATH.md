# Open Math: scalar-ratio repository handoff

Open Math pulls this repository and performs the Lean 4.35 paranoid run in its
cloud environment. All preparation inputs are committed here; no local ZIP,
Mac build directory or attachment is needed. Actual arithmetic boundary–cup
compatibility remains OPEN, independently of the formal checking outcome.

| Item | Value |
| --- | --- |
| Repository | `https://github.com/CheyLoveday/diophantine-z-q.git` |
| Branch | `codex/derivative-switch-boundary-v13` |
| Reviewed scalar-ratio snapshot | `3d2243ff141f9681fbd6a659ca28ffddfae9b000` |
| Selected declarations | 39: previous 21 plus 18 raw-frame/unit/adapter results |
| Offline preparation | [prepare_derivative_switch_openmath.py](scripts/prepare_derivative_switch_openmath.py) |
| Scope and observed local results | [Scalar-ratio verification](research/scalar-ratio/VERIFICATION.md) |
| Prior freezes | [Six lemmas](research/determinant-switch/FREEZE.md), [boundary-scalar](research/boundary-scalar/VERIFICATION.md) |

Use the research branch explicitly. `main` remains the Version 13 baseline and
excludes this research contribution. Record the actual pulled checkout commit;
the preparation receipt records it too. A private mirror also exists at
`CheyLoveday/diophantine-z-q-private`, with the same reviewed research branch.
The public fork above is the active pull destination.

## Prepare from the checkout

From the repository root with Git and Python 3.9 or newer:

```sh
python3 -B scripts/prepare_derivative_switch_openmath.py
```

The default is `--packet scalar-ratio`. This offline command verifies the two
prior frozen manifests (63 and 65 inputs) and the current 99-input
manifest, then creates `lean/.checks/openmath-scalar-ratio`. It checks the
25 generated input files against manifest SHA-256
`117f9ca2c28c42e45198f790dd8c3f324e1bed9d3af11ea9707575363304b811`,
and writes `OPENMATH_PREPARATION.json`. No Lean installation, cache, network,
untracked local ZIP or Mac artifact is used. Existing output directories are
never overwritten; use `--output lean/.checks/openmath-scalar-ratio-2` for a
second preparation.

The generated default builds seven solution modules and Solution. Challenge
is separate, with seven specification modules preserving their paired import
contexts. The first three specifications retain the previous 21 unchanged;
the new four use concrete definitions and eighteen theorem signatures. There
are no definition holes. The inherited default ZInQ target excludes this
contribution, so run the generated project.

Earlier projects remain explicitly reproducible with `--packet boundary-scalar`
(21 targets, previous output directory) and `--packet six-lemma` (six targets).
Neither earlier freeze is rewritten or silently dropped from the combined
current inventory.

## Open Math cloud execution

Open Math supplies Linux, the pinned Lean 4.35.0 toolchain, Git, Python and a
working bubblewrap sandbox. Protect the challenge/configuration/manifest from
solution control. Use the nine locked dependency revisions and trust only the
requested official Mathlib master cache closures:

```sh
set -eu
cd lean/.checks/openmath-scalar-ratio
sha256sum -c MANIFEST.sha256
lean --version
lake --version
MATHLIB_CACHE_DIR="$PWD/.lake/mathlib-cache" lake exe cache get --cache-from=master \
  Mathlib.Algebra.Module.Equiv.Basic Mathlib.Tactic.Ring \
  Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.Tactic.FieldSimp \
  Mathlib.LinearAlgebra.BilinearForm.Properties \
  Mathlib.LinearAlgebra.Matrix.NonsingularInverse Mathlib.Tactic.Push \
  Mathlib.Data.Matrix.Block Mathlib.Tactic.FinCases
sha256sum -c MANIFEST.sha256
lake comparator --config comparator.json --paranoid
sha256sum -c MANIFEST.sha256
```

Capture the comparator's own exit status and complete stdout/stderr in addition
to the final hash check. Retain checkout, preparation receipt, manifests,
actual dependency/tool/checker identities, cache provenance and OS/sandbox
outcomes. Do not upgrade dependencies, remove a checker or disable sandboxing
to obtain a pass.

Success requires exact 39-declaration/referenced-definition matching, the
allowed axiom policy, and acceptance by Lean default, Lean paranoid, lean4lean,
nanoda, con-leche and con-ron. A missing/refusing checker is not a pass. The 39
intentional Challenge sorry warnings are specification placeholders;
sorryAx is forbidden in solution proofs. Full requirements are in the
[frozen verification instructions](research/scalar-ratio/verification/README.md).

Local native compilation, type/axiom auditing, exact models and the direct
structural comparison pass. That comparison exercises six rejection controls
but provides no protected Linux isolation, export-kernel replay or external
kernel evidence. No paranoid or cloud run was performed locally.

The new raw common-strict frame construction and integral-unit equivalence are
formalized, including zero functionals. The full boundary–cup adapter uses the
same actual rows and keeps normalization assumptions explicit. Derived
integral determinant functors, the additive-DVR iff, quotient construction,
actual arithmetic maps/normalizations, localizations and retained limits remain
separate ordinary/open obligations as described in the
[contract](research/scalar-ratio/CONTRACT.md). A successful cloud run does not
prove the manuscript's arithmetic determinant-switch theorem.

Command semantics were checked on 8 November 2026 against installed Lean 4.35.0
sources Lake/Load/Resolve.lean, Lake/CLI/Check.lean, Lake/Check/Compare.lean and
Lake/Check/Axioms.lean, the [4.35 release documentation](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/),
and [pinned Mathlib cache documentation](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Cache/README.md).
Offline preparation checks establish checkout completeness, not cloud runtime
qualification or mathematical acceptance.
