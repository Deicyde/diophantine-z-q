# Opt-in Axiom / PkgI2 bridge

This is a separate Lake package. It does not change the repository-root
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `KERNEL_CONTRACT.json`,
kernel checker, default target (`ZInQKernel`) or any existing workflow.

The PkgI2 objects come from the existing upstream module
`ZInQKernel.HDecomp.Objects` (`PkgI2.IsAbelianVariety`, `PkgI2.IsAbelianScheme`,
`PkgI2.HasGoodReduction`). The root package is required by path, so its existing
`ZInQKernel` library makes that module importable; no new root library, copied
definition, extra axiom, admitted proof or extra premise is introduced. Building
the bridge compiles only `ZInQKernel.HDecomp.Objects` from the root package (its
imports are Mathlib modules), not the root default target.

## Pins

- Lean: `leanprover/lean4:v4.35.0`
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (same as the root manifest)
- Mordell: `82a30cb7857f6e3cfdb1be91f5533c0ccb57d493`
- Stacks (Mordell's dependency): `c496df0d9beea9deaeabcea8492605f9a0a2313b`

## Build and audit

A cold build of the Stacks/Mordell closure takes hours (12,769 modules), so use
the verified dependency cache described in [CACHE.md](CACHE.md). With elan
installed, `zstd`, and the two cache parts plus `SHA256SUMS` downloaded into a
directory of your choice (`$CACHE_DIR` below), run from this directory:

```sh
set -euo pipefail
lake update
python3 scripts/restore_cache.py --metadata ../../.github/axiom-cache.json --check-pins .
lake exe cache get
python3 scripts/restore_cache.py --metadata ../../.github/axiom-cache.json \
  --parts-dir "$CACHE_DIR" --checksums "$CACHE_DIR/SHA256SUMS" \
  --packages-dir .lake/packages
# Fails instead of compiling if any cached dependency output is missing or stale.
lake --no-cache --no-build --fail-fast build \
  +Mordell.Jacobian.Existence +Mordell.Jacobian.Dimension \
  +Mordell.AbelianVariety.GoodReduction
lake build AxiomBridge
lake env lean Check.lean | tee axioms.log
python3 scripts/check_axiom_output.py axioms.log
```

The restore helper deletes the downloaded parts after a successful restore.

The bridge imports only specific Mordell modules: `Jacobian.Existence`,
`Jacobian.Dimension`, and `AbelianVariety.GoodReduction`. It never imports
`Mordell`, `Stacks`, or `StacksFrontier` wholesale. Their transitive closure is
nevertheless large. In particular, an upstream resolution/projective-dimension
module imports the `StacksCore` umbrella; that indirect import is not rewritten.

## Declarations

- `pkgI2_of_proper_geometricallyIntegral`: smoothness follows from Mathlib's
  `smooth_of_grpObj`; properness supplies local finite type and geometric
  integrality supplies geometric reducedness.
- `pkgI2_of_axiom`, `axiom_of_pkgI2`, `abelianVariety_iff`: equivalence with
  `AlgebraicGeometry.IsAbelianVariety`, Stacks Tag 03RO, on the same group scheme.
- `jacobian_isAbelianVariety`: every `Faltings.Jacobian` gives a PkgI2 variety.
- `exists_pkgI2_jacobian`: a curve with a rational divisor of degree one has such
  a Jacobian, dimension equals genus, and the compatible representing-scheme
  isomorphism is unique. This does not strengthen the source's uniqueness into
  a new bundled group-isomorphism statement.
- `geometricallyConnected_of_geometricallyIntegral`,
  `pkgI2_isAbelianScheme_of_fibres`, `pkgI2_hasGoodReduction_of_faltings`:
  the good-reduction implication at `(p.valuation k).valuationSubring`, using
  smooth group-scheme fibres and `Smooth.of_smooth_fiberToSpecResidueField`.

`Check.lean` prints every theorem's statement and transitive axiom dependencies;
`scripts/check_axiom_output.py` requires all nine reports and allows only
`propext`, `Classical.choice` and `Quot.sound`.

This is definition/interface reuse for the H-decomposition's abelian-variety
work packages. It does not discharge Néron–Ogg–Shafarevich, Faltings' Tate theorem,
modularity, or the six-contact estimate itself. Jacobian existence is conditional
on a supplied curve with a degree-one divisor; a positive-genus instance is needed
to obtain a nonzero abelian variety from its dimension theorem. A passing build
and axiom audit is a structural check, not acceptance of any manuscript argument.

## Resource measurements

GNU `/usr/bin/time` and Python 3 are needed. From this directory:

```sh
/usr/bin/time -v -o bridge.time \
  python3 scripts/measure.py --jobs 1 --label my-run AxiomBridge
python3 scripts/summarize.py my-run
```

Use a fresh label each time. The script writes to `.lake/measurements/<label>`.
It does not change the installed toolchain: `LEAN_SYSROOT` points at a symlink
shadow, and `LAKE_OVERRIDE_LEAN=true` makes co-located Lake respect it. A FIFO
with `--jobs` tokens (1–4) caps real Lean compiler subprocesses; each compiler
uses `LEAN_NUM_THREADS=1`. Each compiler has its own `/usr/bin/time -v` record.
Five-second process-group RSS, free-memory and free-disk samples are retained;
sampled aggregate RSS is not an exact maximum or a cgroup charge. The summary
counts compiled StacksCore, StacksFrontier and Mordell modules; after a cache
restore all three counts must be zero.

After the first successful bridge build, keep the restored Axiom `.lake/build`
directories and rebuild incrementally; never `lake clean` the Axiom packages.
Replacing bridge proofs with admitted terms would not remove their imported
dependency cost, and would invalidate the axiom audit.

The optional workflow `.github/workflows/axiom-bridge.yml` runs these steps on
a GitHub-hosted runner; see [CACHE.md](CACHE.md).
