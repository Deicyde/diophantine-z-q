> **Superseding status and scope (2026-11-14 UTC).** The four historical proof banners are authorship cutoffs, not rewritten. See [SOURCE-STATUS.md](SOURCE-STATUS.md) for exact 3a43 public events, the 18 named axiom-report roots and three type-ascribed consumer statements; other helpers and the Frobenius probes are not individually statement/axiom-audited. [PINNED-SOURCE-EVIDENCE.md](PINNED-SOURCE-EVIDENCE.md) supplies compact full defining/telescope context for fresh F2 review, with exact source bindings. Prior findings/full evidence stay preserved; no App acceptance or later-head CI is implied.

# Opt-in Axiom / PkgI2 bridge

This is a separate Lake package. It does not change the repository-root
`lakefile.toml`, `lake-manifest.json`, `lean-toolchain`, `KERNEL_CONTRACT.json`,
kernel checker, default target (`ZInQKernel`) or any existing required workflow.
Its separate optional cache workflow checks the explicitly requested consumers.

The PkgI2 objects come from the existing upstream module
`ZInQKernel.HDecomp.Objects` (`PkgI2.IsAbelianVariety`, `PkgI2.IsAbelianScheme`,
`PkgI2.HasGoodReduction`). The root package is required by path, so its existing
`ZInQKernel` library makes that module importable; no new root library, copied
definition, extra axiom, admitted proof or extra premise is introduced. Building
the original nine-theorem bridge compiles only `ZInQKernel.HDecomp.Objects` from
this package. The opt-in native-continuity companion additionally imports the
existing `ZInQKernel.HDecomp.C10.C10`; neither build invokes the root default target.

## Pins

- Lean: `leanprover/lean4:v4.35.0`
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679` (same as the root manifest)
- Mordell: `82a30cb7857f6e3cfdb1be91f5533c0ccb57d493`
- Stacks (Mordell's dependency): `c496df0d9beea9deaeabcea8492605f9a0a2313b`

## Build and audit

An uncached Stacks/Mordell dependency build takes hours, so use the pinned verified
expanded cache described in [CACHE.md](CACHE.md). With elan
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
  +Mordell.AbelianVariety.GoodReduction \
  +Mordell.AbelianVariety.Reduction.Basic \
  +StacksFrontier.Algebra.Group.TateModule \
  +StacksFrontier.AlgebraicGeometry.GroupScheme.AbelianVariety.TateModule \
  +StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.AbelianVariety \
  +StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion \
  +StacksFrontier.AlgebraicGeometry.Variety.Frobenius.Twist
lake build AxiomBridge TateConsumers FrobeniusAdapters FrobeniusAdapterChecks
lake env lean Check.lean | tee axioms.log
python3 scripts/check_axiom_output.py axioms.log
lake env lean ComponentCheck.lean | tee components.log
python3 scripts/check_component_axioms.py components.log
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

## Opt-in Tate and native-continuity consumers

`TateConsumers` preserves the checked standalone module names. Its point bridge
uses the actual same-field pullback adjunction, and its Tate comparison preserves
the original scalar and sequence maps. It supplies the full original
`PkgI3.TateModuleFree` (free, finite, rank `2 * A.dim`) and finite-dimensionality of
the actual rational Tate space. Native matrix/trace continuity reuses the existing
canonical-Objects proof with those actual module properties, not caller assumptions.

`FrobeniusAdapters` and `FrobeniusAdapterChecks` preserve the frozen four
implementation/four-probe source paths. They provide relative/prime/finite-field
and coordinate-point packaging only. The subsequent torsion/finiteness supplements
are not included in this snapshot. None of these results supplies all C10
representation/descent/common-trace/semisimplicity or reduction squares, H, height
assembly, or a complete Hilbert10 proof. Root default dependencies remain isolated.

The dedicated private trust-zero full-type/body/control evidence and source review
are separate from this lightweight public CI statement/axiom check; do not infer
full imported-library replay or manuscript acceptance from either.

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
