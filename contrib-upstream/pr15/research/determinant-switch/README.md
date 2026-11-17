# Derivative-switch boundary research

Six separate research lemmas compile with pinned Lean 4.35.0, and their
transitive axiom audit uses only `propext` and `Quot.sound`. They prove abstract
boundary and volume identities. **The actual arithmetic class-functional
determinant compatibility remains open.**

Start here:

- [Freeze decision and remaining Open Math OS gate](FREEZE.md)
- [Scope and source-to-arithmetic contract](CONTRACT.md)
- [Verification, statement crosswalk and remaining gaps](VERIFICATION.md)
- [Lean source](../../lean/Research/DerivativeSwitchBoundary.lean)
- [Exact finite-model checks](check_local_model.py)
- [Fresh observed results](evidence/freeze-20261108/RESULT.json), [elaborated statements](evidence/statements-compact.log), and [axiom audit](evidence/freeze-20261108/axioms-and-statements.log)
- [Separately authored model review](evidence/freeze-20261108/final-review.md)
- [Generate the separate six-lemma verification project](verification/README.md)
- [Received ZIP](inputs/derivative_switch_pr_candidate.zip), preserved for provenance, and [ingestion record](PROVENANCE.json)
- [Prepared PR description](PR.md)

The editable research authority is the Lean source and contract above. The ZIP
is the historical input; its README's uncompiled status describes the original
preparation environment. This packet is outside the inherited 48-module helper
snapshot. It changes no manuscript, frozen target, acceptance record, or main
branch.

From the repository root, prepare the **pinned** import closures:

```sh
cd lean
MATHLIB_CACHE_DIR="$PWD/.checks/mathlib-cache" lake exe cache get \
  Mathlib.Algebra.Module.Equiv.Basic Mathlib.Tactic.Ring
cd ..
python3 -B research/determinant-switch/verify.py \
  --output lean/.checks/derivative-switch-fresh
```

Choose a new output directory for each verification. The driver runs the exact
Python models and repository guards, checks all dependency pins and tracked
source cleanliness, freshly compiles this research module with kernel checking
enabled, and prints its statements and transitive axioms. It does not build the
unchanged 48 helper modules or claim their fresh compilation.

The observed run was local macOS, **without `--paranoid`**, as requested.
Published dependency caches are trusted inputs. The separate model review and
local export-structure probe are complete. External kernels, protected Linux
statement comparison, release assurance, hosted CI, and human or arithmetic
acceptance remain pending. Nothing has been pushed or dispatched.

The [packet manifest](MANIFEST.sha256) binds the source, received ZIP and saved
evidence. From the repository root, check it with:

```sh
shasum -a 256 -c research/determinant-switch/MANIFEST.sha256
```
