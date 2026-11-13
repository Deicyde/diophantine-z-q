# Opt-in Axiom / PkgI2 bridge

This is a separate Lake package. The repository-root package still has
`defaultTargets = ["ZInQKernel"]`, its original dependencies, and unchanged CI.
The only root configuration addition is the non-default `PkgI2Leaves` library,
which makes the existing `scratch/h-decomposition/Leaves.lean` importable as
`Leaves`. That source file is not edited or copied.

## Pins

- Original cache/source base: `48b5f075e5509678c84685f0d1ec53febd10b1e5`
- Integration base for this refresh: `d5ea962c16450e26aed593501254b33f1d45f365`
- Lean: `leanprover/lean4:v4.35.0`
- Mathlib: `56a005855ea17e0b0958f73ec801ae140b0a1679`
- Mordell: `82a30cb7857f6e3cfdb1be91f5533c0ccb57d493`
- Stacks (Mordell's dependency): `c496df0d9beea9deaeabcea8492605f9a0a2313b`

## Build and audit

With elan installed, run from this directory:

```sh
lake update
lake exe cache get
lake build AxiomBridge
set -o pipefail
lake env lean Check.lean | tee axioms.log
python3 scripts/check_axiom_output.py axioms.log
```

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

`Check.lean` prints every theorem's statement and transitive axiom dependencies.
No extra smoothness premise, new axiom, or admitted proof is introduced.

This is definition/interface reuse for the H-decomposition's abelian-variety
work packages. It does not discharge Néron–Ogg–Shafarevich, Faltings' Tate theorem,
modularity, or the six-contact estimate itself. Jacobian existence is conditional
on a supplied curve with a degree-one divisor; a positive-genus instance is needed
to obtain a nonzero abelian variety from its dimension theorem.

## Reproduce resource measurements

GNU `/usr/bin/time` and Python 3 are needed. From this directory:

```sh
lake clean Stacks Mordell axiomBridge
/usr/bin/time -v -o bridge.time \
  python3 scripts/measure.py --jobs 4 --label clean-four AxiomBridge
python3 scripts/summarize.py clean-four
```

Use a fresh label each time. The script writes to `.lake/measurements/<label>`.
It does not change the installed toolchain: `LEAN_SYSROOT` points at a symlink
shadow, and `LAKE_OVERRIDE_LEAN=true` makes co-located Lake respect it. A FIFO
with four tokens caps real Lean compiler subprocesses to four; each compiler
uses `LEAN_NUM_THREADS=1`. Lake's runtime uses `LEAN_NUM_THREADS=4`. Each
compiler has its own `/usr/bin/time -v` record. Five-second process-group RSS,
free-memory, and free-disk samples are retained; sampled aggregate RSS is not
an exact maximum or a cgroup charge. GNU time's peak RSS is a per-process peak,
not the sum of concurrent compiler peaks.

This cleans only the Axiom packages and this scratch package, retaining Mathlib
cache and any root-package artifacts. To include the root's large scratch
`Leaves` compilation cost, measure it separately or clean the root package too.
Existing CI cleans/builds the root default target, not this optional bridge.

For ordinary development, run `lake build ZInQKernel` at the repository root.
After the first successful bridge build, preserve the pinned Axiom `.lake/build`
directories and run incremental `lake build AxiomBridge` here; do not clean the
Axiom packages on every check. Replacing bridge proofs with admitted terms would
not remove their imported dependency cost, and would invalidate the axiom audit.

For one compiler at a time use `--jobs 1` and a new label. No external build
cache is downloaded by the measured `lake --no-cache build` invocation.

See the accompanying verification report and raw build measurements for results
and the GitHub-runner estimate; no workflow has been edited to enable the bridge.
