# Companion port: projective compactness and smooth connectedness

Added by the cloud-b3 w17 route lane on top of the vendored core
(`ZInQKernel/Contrib/CloudB3W17Hodge/Port`, commit `e222d7ba1`). Same source, same licence, same
mechanical treatment as `MODIFIED.md` describes; **no core file is changed by this addition**.

Source: `Paul-Lez/HodgeConjecture` @ `2ead713179628a3c738197d5996f51c8a9c886ac`, Apache-2.0. See
`../NOTICE` and `../LICENSE`. Upstream copyright lines differ per file (The Formal Conjectures
Authors; Bhavik Mehta) and each ported file keeps its own licence block and names its own upstream
copyright in the provenance header.

## What this port delivers

| declaration | statement |
| --- | --- |
| `AlgebraicGeometry.IsProjective.complexPoint_compactSpace` | for `X : Over (Spec ℂ)` with `IsProjective X.hom`, `CompactSpace (ComplexPoint X)` |
| `AlgebraicGeometry.ComplexPoint.connectedSpace` | for `X : Over (Spec ℂ)` with `IsIntegral X.left`, `Smooth X.hom`, `QuasiSeparatedSpace X.left`, `ConnectedSpace (ComplexPoint X)` |

Both are over the native `ComplexPoint` / `Point.analyticTopology` of the vendored core. Neither is a
statement about arbitrary proper schemes, and neither gives connectedness without smoothness: they do
**not** by themselves supply `ProperCompactAn` or `ConnectedConnectedAn`.

## Files added (19), all under `Port/`

Minimal import closure of the two targets over the core's existing 25 files:

* `Lemmas/AlgebraicGeometry/ClosedImmersion/ResidueField.lean`
* `Lemmas/AlgebraicGeometry/ComplexPoint/{ClosedImmersion,Projective,ProjectiveCompact}.lean`
* `Other/AlgebraicGeometry/ComplexPoint/{AffineConnected,DenseNonvanishing,EtaleDenseNonvanishing,
  IteratedLocalization,LocalizationConnected,SmoothConnected,StandardEtaleDerivative}.lean`
* `Other/Analysis/Complex/Polynomial/{Complement,FactorGrowth,FiniteSingularity,Growth,
  HolomorphicFactor}.lean`
* `Other/RingTheory/{AlgebraicNonvanishing,IntegralPrimitiveElement,StandardEtaleAlgebraic}.lean`

Upstream `Other/…` keeps its own top level under `Port/Other/…`, so the module prefix is
`ZInQKernel.Contrib.CloudB3W17Hodge.Port.Other.…`.

## Modifications

Only the two mechanical ones of `MODIFIED.md`:

* a provenance header naming the source revision, the source path and that file's upstream copyright;
* 26 import lines remapped, `HodgeConjecture.A.B` → `ZInQKernel.Contrib.CloudB3W17Hodge.Port.A.B` and
  `Other.A.B` → `ZInQKernel.Contrib.CloudB3W17Hodge.Port.Other.A.B`.

No statement, proof term or declaration name is changed. None of the 19 files declares `notation`,
`macro`, `syntax`, `elab`, `#eval`, `run_cmd` or `initialize`, and none uses `sorry`, so no expansion
of the kind `MODIFIED.md` records for `ProjectiveSpace.lean` was needed.
