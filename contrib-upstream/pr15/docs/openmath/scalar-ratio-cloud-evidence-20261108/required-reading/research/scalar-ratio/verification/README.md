# Combined scalar-ratio verification project

Generated copies are non-authoritative; do not edit them. The authority is the
explicit source/output list in `research/scalar-ratio/verification/prepare.py`.
`SOURCES.json` records every source path, its SHA-256 and the sole lockfile
transformation (root package name). Fresh generation must be byte-identical.
No dependency cache, build output or local symlink is an input.

The default solution imports seven research modules. The comparator selects
exactly 39 declarations: the previous six boundary/volume lemmas, thirteen
matrix results, two typed inverse-J adapter results, and eighteen new raw-frame,
coordinate, integral-unit and same-row boundary–cup results. Supporting proofs
are compiled transitively; counts describe coverage, not mathematical importance.

The challenge has seven separate modules preserving the corresponding solution
import context. Its first three modules are byte-identical to the previous
21-target specifications. The four new modules retain concrete definitions
and eighteen reviewed signatures, with no solution imports. Exactly 39 theorem
proof holes are intentional specifications; `definition_names` is empty.
`sorryAx` is forbidden in solution proofs. The only permitted axioms are
propext, Quot.sound and Classical.choice.

## Cloud execution owned by Open Math

Use locked Lean 4.35.0/dependencies and Linux with working bubblewrap. Protect
challenge/configuration/manifest from solution control. From this directory:

```sh
set -eu
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

Capture the comparator's own exit code and complete stdout/stderr in addition
to the final manifest check. Success requires exact declaration/definition
comparison, allowed axioms and every configured checker: Lean default, Lean
paranoid, lean4lean, nanoda, con-leche and con-ron. Missing/refusing checkers
are not passes. Preserve actual tool/checker/dependency identities, checkout,
cache provenance, OS/sandbox outcomes and preparation receipt. Do not update
dependencies, remove checkers or disable sandboxing to get a pass.

Native macOS compilation and the direct local structural/axiom probe provide
no protected Linux comparison, export-kernel replay or external kernel claim.
Those cloud gates remain NOT_RUN locally. The inherited default ZInQ target
excludes this contribution; use this generated project.

The raw frame bridge and integral-unit iff are now formal targets. The
cofactor/determinant-functor interpretation, quotient complement construction,
additive-DVR iff and actual arithmetic application are separate. BoundaryCup
assumes the actual full adjunctions and compatible normalization; it does not
establish them for the manuscript's Selmer construction. Arithmetic tensor
compatibility remains OPEN after even a successful paranoid run.

Command semantics were checked 8 November 2026 against installed Lean 4.35.0
commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc sources Lake/CLI/Check.lean,
Lake/Check/Compare.lean and Lake/Check/Axioms.lean, the
[4.35 release documentation](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
and [pinned Mathlib cache documentation](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Cache/README.md).
