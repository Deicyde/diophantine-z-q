# Source and license notice

The `StacksCore/` and `StacksFrontier/` Lean files in this directory are derived
from AxiomMath/Stacks, immutable commit
`c496df0d9beea9deaeabcea8492605f9a0a2313b`:
https://github.com/AxiomMath/Stacks/tree/c496df0d9beea9deaeabcea8492605f9a0a2313b

The upstream Apache-2.0 license is preserved as `LICENSE`. All source copyright,
author, reference and explanatory notices are retained. The source/destination
file list and hashes are in `SOURCE_MANIFEST.json`.

Port scope: the initial transitive source cone of
`StacksFrontier.AlgebraicGeometry.Groupoids.GroupSchemeProperties.Dimension`.
The unused `FibreDimension.Equidimensional` import was subsequently removed.
Fifteen source modules retained from that initial cone are no longer imported by
the closing proof; they remain listed in the manifest and were independently
compiled from source alongside the modules that the proof uses.
Imports are routed under `ZInQKernel.Contrib.CloudB3W16Dimension`. Citation-only
`stacks`/`ega`/`sga` attributes and `add_to_*` commands are removed, and their two
registration modules are omitted; no new macros or elaborators are introduced.
The retained `MvPolynomial/PrimeStandardForm.lean` module expands the original
local `up` and `r` notation directly as `2 + f.totalDegree` and its indexed powers;
its mathematical declarations and public theorem types are unchanged.
The mathematical declarations retain their upstream names unless a documented
current-Mathlib compatibility repair requires otherwise. Each ported module
carries upstream's `autoImplicit = false`, `relaxedAutoImplicit = false` and
`maxSynthPendingDepth = 3` locally; current Mathlib backward-defeq compatibility
is enabled locally too. Quasi-regular `Defs.lean` explicitly inherits the Ring
structure when constructing its commutative endomorphism subalgebra and uses
local elaboration transparency/heartbeat settings. No repository configuration
or pin is changed.

`UniversalSubspace.lean` reconstructs the universal-subspace dimension transport
from Mathlib's actual `Homeomorph.Set.univ` and
`IsHomeomorph.topologicalKrullDim_eq`. The local-dimension supremum proof uses it
for the universal-neighbourhood bound.

The closing contribution imports the existing `TailP` declaration, not `Main`,
and proves `AVGlue.GroupSchemeEquidim` without changing its statement. Existing
Mathlib and already-main project modules are reused through that import closure.
