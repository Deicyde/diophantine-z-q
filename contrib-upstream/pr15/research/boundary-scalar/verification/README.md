# Combined boundary-scalar verification project

This is a generated project. Its source is the explicit copy list in
`research/boundary-scalar/verification/prepare.py`. **Do not edit generated
copies.** `SOURCES.json` records source paths/hashes and the sole lockfile
transformation; `MANIFEST.sha256` binds the generated inputs. Fresh generation
must give byte-identical files. Compiled artifacts and dependency symlinks are
excluded.

The default solution imports three research modules: the original six-lemma
module, the general matrix/cofactor comparison, and the typed boundary--cup
adapter. The comparator selects exactly 21 declarations: the original six,
thirteen principal matrix results, and two adapter results. Other matrix
helpers are compiled and checked as proof dependencies; their statements are
not additional separately selected comparator targets.

The challenge is a separate environment with 21 intentional theorem proof holes.
Its three specification modules each use the exact import context of the
corresponding solution module, preserving the elaborated coercion instances.
It imports no solution. All eight referenced project definitions are concrete,
and `definition_names` is empty. Its first section reuses the original frozen
six-declaration challenge; the remaining signatures and definitions are reviewed
for the new matrix and adapter contracts. `sorryAx` is forbidden in solution
proofs. The allowlist is `propext`, `Quot.sound`, `Classical.choice`.

## Open Math cloud run

Use pinned Lean 4.35.0 and working Linux `bubblewrap`. Preserve the trusted
challenge/configuration/manifest outside solution control. The cache is an
explicitly trusted dependency input, not a fresh build of Mathlib.

```sh
set -eu
sha256sum -c MANIFEST.sha256
lean --version
lake --version
MATHLIB_CACHE_DIR="$PWD/.lake/mathlib-cache" lake exe cache get \
  Mathlib.Algebra.Module.Equiv.Basic Mathlib.Tactic.Ring \
  Mathlib.LinearAlgebra.Matrix.Adjugate Mathlib.Tactic.FieldSimp \
  Mathlib.LinearAlgebra.BilinearForm.Properties
sha256sum -c MANIFEST.sha256
lake comparator --config comparator.json --paranoid
sha256sum -c MANIFEST.sha256
```

Keep the nine locked dependency revisions and record their actual source state.
Capture the comparator's own exit status and complete stdout/stderr. Success
requires the full declaration list, protected definitions, axiom audit, and
acceptance by `Lean default`, `Lean paranoid`, `lean4lean`, `nanoda`, `con-leche`
and `con-ron`. A missing or refusing checker is not a successful run. Do not
drop a checker or disable sandboxing. No second redundant `lake check` is needed.

Retain source checkout and manifests, generated preparation receipt, actual
tool/dependency/checker identities, OS/sandbox outcome, commands, logs, exit
codes and cache provenance. Record export hashes only if exports were retained;
standard Lake uses temporary exports. A source-bound comparator run is required
for this plan; an unrelated export does not establish source correspondence.

Local macOS compilation and the direct export-structure/axiom probe use no
`--paranoid` and provide no Linux isolation or external kernel evidence. The
generated project is the target; the inherited `lean/ZInQ` default does not
cover this contribution.

The formal matrix theorem assumes the stated normal-form presentation and
basis determinants. Construction of those bases from common-strict matrices,
the determinant-functor interpretation and DVR valuation consequence are
explained in `DERIVATION.md` as ordinary algebra. The typed adapter assumes
the actual two boundary--cup identities. Their arithmetic realization remains
OPEN, even after a successful paranoid run.

Command semantics use installed Lean 4.35.0 commit
`eb6cafb7290e8bd5f2937522d8d804f58f02bafc`, inspected help and pinned
`Lake/CLI/Check.lean`, `Lake/Check/Compare.lean`, and `Lake/Check/Axioms.lean`.
Consulted 8 November 2026: [4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/)
and [pinned Mathlib cache documentation](https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Cache/README.md).
